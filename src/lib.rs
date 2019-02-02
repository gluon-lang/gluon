//! This crate contains contains the implementation for the gluon programming language.
//!
//! Gluon is a programming language suitable for embedding in an existing application to extend its
//! behaviour. For information about how to use this library the best resource currently is the
//! [tutorial](http://gluon-lang.org/book/index.html) which contains examples
//! on how to write gluon programs as well as how to run them using this library.
#![doc(html_root_url = "https://docs.rs/gluon/0.12.0")] // # GLUON

#[cfg(test)]
extern crate env_logger;

pub extern crate either;
#[macro_use]
extern crate log;
#[macro_use]
extern crate quick_error;

#[cfg(feature = "serde_derive_state")]
#[macro_use]
extern crate serde_derive_state;
#[cfg(feature = "serde")]
extern crate serde_state as serde;

#[macro_use]
pub extern crate gluon_base as base;
pub extern crate gluon_check as check;
extern crate gluon_format as format;
pub extern crate gluon_parser as parser;
#[macro_use]
extern crate gluon_codegen;
#[macro_use]
pub extern crate gluon_vm as vm;

macro_rules! try_future {
    ($e:expr) => {
        try_future!($e, Box::new)
    };
    ($e:expr, $f:expr) => {
        match $e {
            Ok(x) => x,
            Err(err) => return $f(::futures::future::err(err.into())),
        }
    };
}

pub mod compiler_pipeline;
#[macro_use]
pub mod import;
pub mod query;
pub mod std_lib;

pub use crate::vm::thread::{RootedThread, Thread};

use futures::{Future, IntoFuture};

use either::Either;

use std as real_std;
use std::{
    env, error::Error as StdError, fmt, path::PathBuf, result::Result as StdResult, sync::Arc,
};

use crate::base::{
    ast::{self, SpannedExpr},
    error::{Errors, InFile},
    filename_to_module,
    metadata::Metadata,
    pos::{BytePos, Span, Spanned},
    symbol::{Symbol, Symbols},
    types::{ArcType, TypeCache},
};

use crate::format::Formatter;

use crate::vm::api::{Getable, Hole, OpaqueValue, VmType};
use crate::vm::compiler::CompiledModule;
use crate::vm::macros;

use crate::{
    compiler_pipeline::*,
    import::{add_extern_module, DefaultImporter, Import},
    query::Compilation,
};

quick_error! {
/// Error type wrapping all possible errors that can be generated from gluon
#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub enum Error {
    /// Error found when parsing gluon code
    Parse(err: InFile<parser::Error>) {
        description(err.description())
        display("{}", err)
        from()
    }
    /// Error found when typechecking gluon code
    Typecheck(err: InFile<check::typecheck::HelpError<Symbol>>) {
        description(err.description())
        display("{}", err)
        from()
    }
    /// Error found when performing an IO action such as loading a file
    IO(err: IoError) {
        description(err.description())
        display("{}", err)
        from()
    }
    /// Error found when executing code in the virtual machine
    VM(err: crate::vm::Error) {
        description(err.description())
        display("{}", err)
        from()
    }
    /// Error found when expanding macros
    Macro(err: InFile<macros::Error>) {
        description(err.description())
        display("{}", err)
        from()
    }
    Other(err: macros::Error) {
        description(err.description())
        display("{}", err)
        from()
    }
    /// Multiple errors where found
    Multiple(err: Errors<Error>) {
        description(err.description())
        display("{}", err)
    }
}
}

impl From<std::io::Error> for Error {
    fn from(err: std::io::Error) -> Self {
        Error::IO(err.into())
    }
}

impl Error {
    pub fn merge(self, other: Self) -> Self {
        match (self, other) {
            (Error::Multiple(mut errors), Error::Multiple(err)) => {
                errors.extend(err);
                Error::Multiple(errors)
            }
            (Error::Multiple(mut errors), err) | (err, Error::Multiple(mut errors)) => {
                errors.push(err);
                Error::Multiple(errors)
            }
            (l, r) => Error::Multiple(vec![l, r].into_iter().collect()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct IoError(Arc<std::io::Error>);

impl fmt::Display for IoError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl StdError for IoError {
    fn description(&self) -> &str {
        self.0.description()
    }
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        self.0.source()
    }
}

impl<E> From<E> for IoError
where
    std::io::Error: From<E>,
{
    fn from(err: E) -> Self {
        IoError(Arc::new(err.into()))
    }
}

impl Eq for IoError {}

impl PartialEq for IoError {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(&*self.0, &*other.0)
    }
}

impl std::hash::Hash for IoError {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher,
    {
        (&*self.0 as *const std::io::Error).hash(state)
    }
}

impl base::error::AsDiagnostic for Error {
    fn as_diagnostic(&self) -> codespan_reporting::Diagnostic {
        codespan_reporting::Diagnostic::new_error(self.to_string())
    }
}

impl From<String> for Error {
    fn from(s: String) -> Self {
        Error::VM(s.into())
    }
}

impl From<Errors<Spanned<macros::Error, BytePos>>> for Error {
    fn from(mut errors: Errors<Spanned<macros::Error, BytePos>>) -> Error {
        if errors.len() == 1 {
            let err = errors.pop().unwrap();
            match err.value.downcast::<Error>() {
                Ok(err) => *err,
                Err(err) => Error::Other(err),
            }
        } else {
            Error::Multiple(
                errors
                    .into_iter()
                    .map(|err| match err.value.downcast::<Error>() {
                        Ok(err) => *err,
                        Err(err) => Error::Other(err),
                    })
                    .collect(),
            )
        }
    }
}

impl From<Errors<Error>> for Error {
    fn from(mut errors: Errors<Error>) -> Error {
        if errors.len() == 1 {
            errors.pop().unwrap()
        } else {
            errors = errors
                .into_iter()
                .flat_map(|err| match err {
                    Error::Multiple(errors) => Either::Left(errors.into_iter()),
                    err => Either::Right(Some(err).into_iter()),
                })
                .collect();

            Error::Multiple(errors)
        }
    }
}

impl Error {
    pub fn emit_string(&self, code_map: &::codespan::CodeMap) -> ::std::io::Result<String> {
        let mut output = Vec::new();
        self.emit(
            &mut ::codespan_reporting::termcolor::NoColor::new(&mut output),
            code_map,
        )?;
        Ok(String::from_utf8(output).unwrap())
    }

    pub fn emit<W>(&self, writer: &mut W, code_map: &::codespan::CodeMap) -> ::std::io::Result<()>
    where
        W: ?Sized + ::codespan_reporting::termcolor::WriteColor,
    {
        match *self {
            Error::Parse(ref err) => err.emit(writer, code_map),
            Error::Typecheck(ref err) => err.emit(writer, code_map),
            Error::IO(ref err) => write!(writer, "{}", err),
            Error::VM(ref err) => write!(writer, "{}", err),
            Error::Macro(ref err) => err.emit(writer, code_map),
            Error::Other(ref err) => write!(writer, "{}", err),
            Error::Multiple(ref errors) => {
                for err in errors {
                    err.emit(writer, code_map)?;
                }
                Ok(())
            }
        }
    }
}

/// Type alias for results returned by gluon
pub type Result<T> = StdResult<T, Error>;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct Settings {
    implicit_prelude: bool,
    emit_debug_info: bool,
    full_metadata: bool,
    use_standard_lib: bool,
}

impl Default for Settings {
    fn default() -> Self {
        Self {
            implicit_prelude: true,
            emit_debug_info: true,
            full_metadata: false,
            use_standard_lib: true,
        }
    }
}

/// Type which enables parsing, typechecking and compiling an AST into bytecode
pub struct Compiler {
    pub run_io: bool,
    pub implicit_prelude: bool,
}

pub struct ModuleCompiler<'a> {
    compiler: &'a Compiler,
    database: &'a query::CompilerDatabase,
    symbols: Symbols,
}

impl<'a> std::ops::Deref for ModuleCompiler<'a> {
    type Target = &'a query::CompilerDatabase;
    fn deref(&self) -> &Self::Target {
        &self.database
    }
}

macro_rules! option {
($(#[$attr:meta])* $name: ident $set_name: ident : $typ: ty) => {
    $(#[$attr])*
    pub fn $name(mut self, $name: $typ) -> Self {
        self.$name = $name;
        self
    }

    pub fn $set_name(&mut self, $name: $typ) {
        self.$name = $name;
    }
};
}

macro_rules! runtime_option {
($(#[$attr:meta])* $name: ident $set_name: ident : $typ: ty) => {
    $(#[$attr])*
    pub fn $name(mut self, $name: $typ) -> Self {
        self.$set_name($name);
        self
    }

    pub fn $set_name(&mut self, $name: $typ) {
        let mut settings = self.compiler_settings();
        settings.$name = $name;
        self.set_compiler_settings(settings);
    }
};
}

impl import::CompilerLock {
    runtime_option! {
        /// Sets whether the implicit prelude should be include when compiling a file using this
        /// compiler (default: true)
        implicit_prelude set_implicit_prelude: bool
    }

    runtime_option! {
        /// Sets whether the compiler should emit debug information such as source maps and variable
        /// names.
        /// (default: true)
        emit_debug_info set_emit_debug_info: bool
    }

    runtime_option! {
        /// Sets whether full metadata is required
        /// (default: false)
        full_metadata set_full_metadata: bool
    }

    runtime_option! {
        /// Sets whether internal standard library is searched for requested modules
        /// (default: true)
        use_standard_lib set_use_standard_lib: bool
    }
}

impl Compiler {
    /// Creates a new compiler with default settings
    pub fn new() -> Self {
        Compiler {
            run_io: false,
            implicit_prelude: true,
            use_standard_lib: true,
        }
    }

    pub fn new_lock() -> Self {
        Self::new()
    }

    option! {
        /// Sets whether the implicit prelude should be include when compiling a file using this
        /// compiler (default: true)
        implicit_prelude set_implicit_prelude: bool
    }

    option! {
        /// Sets whether `IO` expressions are evaluated.
        /// (default: false)
        run_io set_run_io: bool
    }

    pub fn module_compiler<'a>(
        &'a self,
        database: &'a query::CompilerDatabase,
    ) -> ModuleCompiler<'a> {
        ModuleCompiler {
            compiler: self,
            database,
            symbols: Default::default(),
        }
    }

    /// Parse `expr_str`, returning an expression if successful
    pub fn parse_expr(
        &self,
        vm: &Thread,
        type_cache: &TypeCache<Symbol, ArcType>,
        file: &str,
        expr_str: &str,
    ) -> StdResult<SpannedExpr<Symbol>, InFile<parser::Error>> {
        self.parse_partial_expr(vm, type_cache, file, expr_str)
            .map_err(|(_, err)| err)
    }

    /// Parse `input`, returning an expression if successful
    pub fn parse_partial_expr(
        &self,
        vm: &Thread,
        type_cache: &TypeCache<Symbol, ArcType>,
        file: &str,
        expr_str: &str,
    ) -> SalvageResult<SpannedExpr<Symbol>, InFile<parser::Error>> {
        parse_expr(
            &mut self.module_compiler(&get_db_snapshot(&vm)),
            type_cache,
            file,
            expr_str,
        )
    }

    /// Parse and typecheck `expr_str` returning the typechecked expression and type of the
    /// expression
    pub fn typecheck_expr(
        &self,
        vm: &Thread,
        file: &str,
        expr_str: &str,
        expr: &mut SpannedExpr<Symbol>,
    ) -> Result<ArcType> {
        expr.typecheck_expected(
            &mut self.module_compiler(&get_db_snapshot(&vm)),
            vm,
            file,
            expr_str,
            None,
        )
        .map(|result| result.typ)
    }

    pub fn typecheck_str(
        &self,
        vm: &Thread,
        file: &str,
        expr_str: &str,
        expected_type: Option<&ArcType>,
    ) -> Result<(SpannedExpr<Symbol>, ArcType)> {
        let TypecheckValue { expr, typ, .. } = expr_str.typecheck_expected(
            &mut self.module_compiler(&get_db_snapshot(&vm)),
            vm,
            file,
            expr_str,
            expected_type,
        )?;
        Ok((expr, typ))
    }

    /// Compiles `expr` into a function which can be added and run by the `vm`
    pub fn compile_script(
        &self,
        vm: &Thread,
        filename: &str,
        expr_str: &str,
        expr: &SpannedExpr<Symbol>,
    ) -> Result<CompiledModule> {
        TypecheckValue {
            expr,
            typ: vm.global_env().type_cache().hole(),
            metadata: Default::default(),
            metadata_map: Default::default(),
        }
        .compile(
            &mut self.module_compiler(&get_db_snapshot(&vm)),
            vm,
            filename,
            expr_str,
            (),
        )
        .map(|result| result.module)
    }

    /// Compiles the source code `expr_str` into bytecode serialized using `serializer`
    #[cfg(feature = "serialization")]
    pub fn compile_to_bytecode<S>(
        &self,
        thread: &Thread,
        name: &str,
        expr_str: &str,
        serializer: S,
    ) -> StdResult<S::Ok, Either<Error, S::Error>>
    where
        S: serde::Serializer,
        S::Error: 'static,
    {
        compile_to(
            expr_str,
            &mut self.module_compiler(&get_db_snapshot(&thread)),
            &thread,
            name,
            expr_str,
            None,
            serializer,
        )
    }

    /// Loads bytecode from a `Deserializer` and stores it into the module `name`.
    ///
    /// `load_script` is equivalent to `compile_to_bytecode` followed by `load_bytecode`
    #[cfg(feature = "serialization")]
    pub fn load_bytecode<'vm, D>(
        &self,
        thread: &'vm Thread,
        name: &str,
        deserializer: D,
    ) -> impl Future<Item = (), Error = Error> + 'vm
    where
        D: serde::Deserializer<'vm> + 'vm,
        D::Error: Send + Sync,
    {
        Precompiled(deserializer).load_script(
            &mut self.module_compiler(&get_db_snapshot(&thread)),
            thread,
            name,
            "",
            (),
        )
    }

    /// Parses and typechecks `expr_str` followed by extracting metadata from the created
    /// expression
    pub fn extract_metadata(
        &self,
        vm: &Thread,
        file: &str,
        expr_str: &str,
    ) -> Result<(SpannedExpr<Symbol>, ArcType, Arc<Metadata>)> {
        use crate::check::metadata;
        let (mut expr, typ) = self.typecheck_str(vm, file, expr_str, None)?;

        let (metadata, _) = metadata::metadata(&*vm.get_env(), &mut expr);
        Ok((expr, typ, metadata))
    }

    /// Compiles `input` and if it is successful runs the resulting code and stores the resulting
    /// value in the vm.
    ///
    /// If at any point the function fails the resulting error is returned and nothing is added to
    /// the VM.
    pub fn load_script(&self, vm: &Thread, filename: &str, input: &str) -> Result<()> {
        self.load_script_async(vm, filename, input).wait()
    }

    pub fn load_script_async<'vm>(
        &self,
        vm: &'vm Thread,
        filename: &str,
        input: &str,
    ) -> impl Future<Item = (), Error = Error> + 'vm {
        input.load_script(
            &mut self.module_compiler(&get_db_snapshot(&vm)),
            vm,
            filename,
            input,
            None,
        )
    }

    /// Loads `filename` and compiles and runs its input by calling `load_script`
    pub fn load_file<'vm>(&self, vm: &'vm Thread, filename: &str) -> Result<()> {
        self.load_file_async(vm, filename).wait()
    }

    pub fn load_file_async<'vm>(
        &self,
        vm: &'vm Thread,
        filename: &str,
    ) -> impl Future<Item = (), Error = Error> {
        // Use the import macro's path resolution if it exists so that we mimick the import
        // macro as close as possible
        let import = get_import(vm);
        let module_name = Symbol::from(format!("@{}", filename_to_module(filename)));
        import
            .load_module(
                &mut self.module_compiler(&import.snapshot(vm.root_thread())),
                vm,
                &module_name,
            )
            .map_err(|(_, err)| err.into())
            .into_future()
    }

    /// Compiles and runs the expression in `expr_str`. If successful the value from running the
    /// expression is returned
    ///
    /// # Examples
    ///
    /// Import from gluon's standard library and evaluate a string
    ///
    /// ```
    /// # extern crate gluon;
    /// # use gluon::{new_vm,Compiler};
    /// # fn main() {
    /// let vm = new_vm();
    /// let (result, _) = Compiler::new()
    ///     .run_expr::<String>(
    ///         &vm,
    ///         "example",
    ///         " let string  = import! \"std/string.glu\" in string.trim \"  Hello world  \t\" "
    ///     )
    ///     .unwrap();
    /// assert_eq!(result, "Hello world");
    /// # }
    /// ```
    ///
    pub fn run_expr<'vm, T>(
        &self,
        vm: &'vm Thread,
        name: &str,
        expr_str: &str,
    ) -> Result<(T, ArcType)>
    where
        T: for<'value> Getable<'vm, 'value> + VmType + Send + 'vm,
    {
        let expected = T::make_type(vm);
        expr_str
            .run_expr(
                &mut self.module_compiler(&get_db_snapshot(&vm)),
                vm,
                name,
                expr_str,
                Some(&expected),
            )
            .and_then(move |execute_value| {
                Ok((
                    T::from_value(vm, execute_value.value.get_variant()),
                    execute_value.typ,
                ))
            })
            .wait()
    }

    /// Compiles and runs the expression in `expr_str`. If successful the value from running the
    /// expression is returned
    ///
    /// # Examples
    ///
    /// Import from gluon's standard library and evaluate a string
    ///
    /// ```
    /// # extern crate gluon;
    /// # use gluon::{new_vm,Compiler};
    /// # use gluon::base::types::Type;
    /// # fn main() {
    /// let vm = new_vm();
    /// let result = Compiler::new()
    ///     .run_expr::<String>(&vm, "example",
    ///         " let string  = import! \"std/string.glu\" in string.trim \"    Hello world  \t\" ")
    ///     .unwrap();
    /// let expected = ("Hello world".to_string(), Type::string());
    ///
    /// assert_eq!(result, expected);
    /// }
    /// ```
    ///
    pub fn run_expr_async<T>(
        &self,
        vm: &Thread,
        name: &str,
        expr_str: &str,
    ) -> impl Future<Item = (T, ArcType), Error = Error>
    where
        T: for<'vm, 'value> Getable<'vm, 'value> + VmType + Send + 'static,
    {
        let expected = T::make_type(&vm);
        let vm = vm.root_thread();
        expr_str
            .run_expr(
                &mut self.module_compiler(&get_db_snapshot(&vm)),
                vm.clone(),
                name,
                expr_str,
                Some(&expected),
            )
            .and_then(move |execute_value| {
                Ok((
                    T::from_value(&vm, execute_value.value.get_variant()),
                    execute_value.typ,
                ))
            })
    }

    pub fn format_expr(
        &self,
        formatter: &mut Formatter,
        thread: &Thread,
        file: &str,
        input: &str,
    ) -> Result<String> {
        fn has_format_disabling_errors(file: &codespan::FileName, err: &Error) -> bool {
            match *err {
                Error::Multiple(ref errors) => errors
                    .iter()
                    .any(|err| has_format_disabling_errors(file, err)),
                Error::Parse(ref err) => err.source_name() == file,
                _ => false,
            }
        }

        let db = get_db_snapshot(thread);
        let mut compiler = self.module_compiler(&db);
        let compiler = &mut compiler;

        let expr = match input.reparse_infix(compiler, thread, file, input) {
            Ok(expr) => expr.expr,
            Err((Some(expr), err)) => {
                if has_format_disabling_errors(&codespan::FileName::from(file.to_string()), &err) {
                    return Err(err);
                }
                expr.expr
            }
            Err((None, err)) => return Err(err),
        };

        fn skip_implicit_prelude(
            span: Span<BytePos>,
            l: &SpannedExpr<Symbol>,
        ) -> &SpannedExpr<Symbol> {
            match l.value {
                ast::Expr::LetBindings(_, ref e) if !span.contains(l.span) => {
                    skip_implicit_prelude(span, e)
                }
                _ => l,
            }
        }

        let file_map = db.get_filemap(file).unwrap();
        let expr = skip_implicit_prelude(file_map.span(), &expr);
        Ok(formatter.pretty_expr(&*file_map, expr))
    }
}

pub trait ThreadExt {
    fn get_database(&self) -> salsa::Snapshot<query::CompilerDatabase>;
    fn get_database_mut(&self) -> import::CompilerLock;
}

impl ThreadExt for Thread {
    fn get_database(&self) -> salsa::Snapshot<query::CompilerDatabase> {
        get_db_snapshot(self)
    }
    fn get_database_mut(&self) -> import::CompilerLock {
        get_import(self).compiler_lock(self.root_thread())
    }
}

fn get_db_snapshot(vm: &Thread) -> salsa::Snapshot<query::CompilerDatabase> {
    get_import(vm).snapshot(vm.root_thread())
}

fn get_import(vm: &Thread) -> Arc<Import> {
    let opt_macro = vm.get_macros().get("import");
    match opt_macro.and_then(|mac| mac.downcast_arc::<Import>().ok()) {
        Some(import) => import,
        None => Arc::new(Import::new(DefaultImporter)),
    }
}

impl<'a> ModuleCompiler<'a> {
    pub fn mut_symbols(&mut self) -> &mut Symbols {
        &mut self.symbols
    }

    fn include_implicit_prelude(
        &mut self,
        type_cache: &TypeCache<Symbol, ArcType>,
        name: &str,
        expr: &mut SpannedExpr<Symbol>,
    ) {
        use std::mem;
        if name == "std.prelude" {
            return;
        }

        let prelude_expr = parse_expr(self, type_cache, "", PRELUDE).unwrap();
        let original_expr = mem::replace(expr, prelude_expr);

        // Replace the 0 in the prelude with the actual expression
        fn assign_last_body(l: &mut SpannedExpr<Symbol>, original_expr: SpannedExpr<Symbol>) {
            match l.value {
                ast::Expr::LetBindings(_, ref mut e) => {
                    assign_last_body(e, original_expr);
                }
                _ => *l = original_expr,
            }
        }
        assign_last_body(expr, original_expr);
    }
}

pub const PRELUDE: &'static str = r#"
let __implicit_prelude = import! std.prelude
let { IO, Num, Eq, Ord, Show, Functor, Applicative, Monad, Option, Bool, ? } = __implicit_prelude

let { (+), (-), (*), (/), negate, (==), (/=), (<), (<=), (>=), (>), (++), show, not, flat_map } = __implicit_prelude

let __implicit_bool @ { ? } = import! std.bool

let { ? } = import! std.option

let __implicit_float @ { ? } = import! std.float

let __implicit_int @ { ? } = import! std.int

let __implicit_string @ { ? } = import! std.string

let { error } = import! std.prim

in ()
"#;

#[derive(Default)]
pub struct VmBuilder {
    import_paths: Option<Vec<PathBuf>>,
}

impl VmBuilder {
    pub fn new() -> VmBuilder {
        VmBuilder::default()
    }

    option! {
        /// (default: ["."])
        import_paths set_import_paths: Option<Vec<PathBuf>>
    }

    pub fn build(self) -> RootedThread {
        let vm =
            RootedThread::with_global_state(crate::vm::vm::GlobalVmStateBuilder::new().build());

        let import = Import::new(DefaultImporter);
        if let Some(import_paths) = self.import_paths {
            import.set_paths(import_paths);
        }

        if let Ok(gluon_path) = env::var("GLUON_PATH") {
            import.add_path(gluon_path);
        }
        vm.get_macros().insert(String::from("import"), import);

        add_extern_module(&vm, "std.prim", crate::vm::primitives::load);

        Compiler::new()
            .run_expr::<OpaqueValue<&Thread, Hole>>(
                &vm,
                "",
                r#"//@NO-IMPLICIT-PRELUDE
                    let _ = import! std.types
                    let _ = import! std.prim
                    ()
                "#,
            )
            .unwrap_or_else(|err| panic!("{}", err));

        add_extern_module(&vm, "std.byte.prim", crate::vm::primitives::load_byte);
        add_extern_module(&vm, "std.int.prim", crate::vm::primitives::load_int);
        add_extern_module(&vm, "std.float.prim", crate::vm::primitives::load_float);
        add_extern_module(&vm, "std.string.prim", crate::vm::primitives::load_string);
        add_extern_module(&vm, "std.fs.prim", crate::vm::primitives::load_fs);
        add_extern_module(&vm, "std.path.prim", crate::vm::primitives::load_path);
        add_extern_module(&vm, "std.char.prim", crate::vm::primitives::load_char);
        add_extern_module(&vm, "std.array.prim", crate::vm::primitives::load_array);

        add_extern_module(&vm, "std.lazy.prim", crate::vm::lazy::load);
        add_extern_module(&vm, "std.reference.prim", crate::vm::reference::load);

        add_extern_module(&vm, "std.channel.prim", crate::vm::channel::load_channel);
        add_extern_module(&vm, "std.thread.prim", crate::vm::channel::load_thread);
        add_extern_module(&vm, "std.debug.prim", crate::vm::debug::load);
        add_extern_module(&vm, "std.io.prim", crate::std_lib::io::load);
        add_extern_module(&vm, "std.process.prim", crate::std_lib::process::load);
        add_extern_module(&vm, "std.env.prim", crate::std_lib::env::load);

        add_extern_module_if!(
            #[cfg(feature = "serialization")],
            available_if = "gluon is compiled with the 'serialization' feature",
            args(&vm, "std.json.prim", crate::vm::api::json::load)
        );

        add_extern_module_if!(
            #[cfg(feature = "regex")],
            available_if = "gluon is compiled with the 'regex' feature",
            args(&vm, "std.regex.prim", crate::std_lib::regex::load)
        );

        add_extern_module_if!(
            #[cfg(feature = "web")],
            available_if = "gluon is compiled with the 'web' feature",
            args(&vm, "std.http.prim_types", crate::std_lib::http::load_types)
        );

        add_extern_module_if!(
            #[cfg(feature = "web")],
            available_if = "gluon is compiled with the 'web' feature",
            args(&vm, "std.http.prim", crate::std_lib::http::load)
        );

        add_extern_module_if!(
            #[cfg(all(feature = "random", not(target_arch = "wasm32")))],
            available_if = "gluon is compiled with the 'random' feature and is not targeting WASM",
            args(&vm, "std.random.prim", crate::std_lib::random::load)
        );

        vm
    }
}

/// Creates a new virtual machine with support for importing other modules and with all primitives
/// loaded.
pub fn new_vm() -> RootedThread {
    VmBuilder::default().build()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn implicit_prelude() {
        let _ = ::env_logger::try_init();

        let thread = new_vm();
        Compiler::new()
            .implicit_prelude(false)
            .run_expr::<()>(&thread, "prelude", PRELUDE)
            .unwrap_or_else(|err| panic!("{}", err));
    }
}
