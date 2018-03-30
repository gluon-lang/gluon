//! This crate contains contains the implementation for the gluon programming language.
//!
//! Gluon is a programming language suitable for embedding in an existing application to extend its
//! behaviour. For information about how to use this library the best resource currently is the
//! [tutorial](https://github.com/gluon-lang/gluon/blob/master/TUTORIAL.md) which contains examples
//! on how to write gluon programs as well as how to run them using this library.
#![doc(html_root_url = "https://docs.rs/gluon/0.7.1")] // # GLUON

#[cfg(test)]
extern crate env_logger;

pub extern crate either;
extern crate futures;
extern crate itertools;
#[macro_use]
extern crate log;
#[macro_use]
extern crate quick_error;
#[cfg(not(target_arch = "wasm32"))]
extern crate tokio_core;

#[cfg(feature = "serde_derive_state")]
#[macro_use]
extern crate serde_derive_state;
#[cfg(feature = "serde")]
extern crate serde_state as serde;

#[macro_use]
pub extern crate gluon_base as base;
pub extern crate gluon_check as check;
pub extern crate gluon_parser as parser;
#[macro_use]
pub extern crate gluon_vm as vm;

pub mod compiler_pipeline;
pub mod import;
pub mod io;
#[cfg(feature = "regex")]
pub mod regex_bind;
#[cfg(all(feature = "rand", not(target_arch = "wasm32")))]
pub mod rand_bind;

pub use vm::thread::{RootedThread, Thread};

pub use futures::Future;

use either::Either;

use std::error::Error as StdError;
use std::result::Result as StdResult;
use std::env;
use std::path::PathBuf;

use base::filename_to_module;
use base::ast::{self, SpannedExpr};
use base::error::{Errors, InFile};
use base::metadata::Metadata;
use base::symbol::{Symbol, SymbolModule, Symbols};
use base::types::{ArcType, TypeCache};
use base::pos::{self, BytePos, Span, Spanned};

use vm::Variants;
use vm::api::{Getable, Hole, OpaqueValue, VmType};
use vm::future::{BoxFutureValue, FutureValue};
use vm::compiler::CompiledModule;
use vm::thread::ThreadInternal;
use vm::macros;
use compiler_pipeline::*;
use import::{add_extern_module, DefaultImporter, Import};

quick_error! {
    /// Error type wrapping all possible errors that can be generated from gluon
    #[derive(Debug)]
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
        IO(err: ::std::io::Error) {
            description(err.description())
            display("{}", err)
            from()
        }
        /// Error found when executing code in the virtual machine
        VM(err: ::vm::Error) {
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
        Other(err: Box<StdError + Send + Sync>) {
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

/// Type alias for results returned by gluon
pub type Result<T> = StdResult<T, Error>;

/// Type which makes parsing, typechecking and compiling an AST into bytecode
pub struct Compiler {
    symbols: Symbols,
    implicit_prelude: bool,
    emit_debug_info: bool,
    run_io: bool,
}

impl Default for Compiler {
    fn default() -> Compiler {
        Compiler::new()
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

impl Compiler {
    /// Creates a new compiler with default settings
    pub fn new() -> Compiler {
        Compiler {
            symbols: Symbols::new(),
            implicit_prelude: true,
            emit_debug_info: true,
            run_io: false,
        }
    }

    option!{
        /// Sets whether the implicit prelude should be include when compiling a file using this
        /// compiler (default: true)
        implicit_prelude set_implicit_prelude: bool
    }

    option!{
        /// Sets whether the compiler should emit debug information such as source maps and variable
        /// names.
        /// (default: true)
        emit_debug_info set_emit_debug_info: bool
    }

    option!{
        /// Sets whether `IO` expressions are evaluated.
        /// (default: false)
        run_io set_run_io: bool
    }

    pub fn mut_symbols(&mut self) -> &mut Symbols {
        &mut self.symbols
    }

    /// Parse `expr_str`, returning an expression if successful
    pub fn parse_expr(
        &mut self,
        type_cache: &TypeCache<Symbol, ArcType>,
        file: &str,
        expr_str: &str,
    ) -> StdResult<SpannedExpr<Symbol>, InFile<parser::Error>> {
        self.parse_partial_expr(type_cache, file, expr_str)
            .map_err(|(_, err)| err)
    }

    /// Parse `input`, returning an expression if successful
    pub fn parse_partial_expr(
        &mut self,
        type_cache: &TypeCache<Symbol, ArcType>,
        file: &str,
        expr_str: &str,
    ) -> StdResult<SpannedExpr<Symbol>, (Option<SpannedExpr<Symbol>>, InFile<parser::Error>)> {
        Ok(parser::parse_partial_expr(
            &mut SymbolModule::new(file.into(), &mut self.symbols),
            type_cache,
            expr_str,
        ).map_err(|(expr, err)| (expr, InFile::new(file, expr_str, err)))?)
    }

    /// Parse and typecheck `expr_str` returning the typechecked expression and type of the
    /// expression
    pub fn typecheck_expr(
        &mut self,
        vm: &Thread,
        file: &str,
        expr_str: &str,
        expr: &mut SpannedExpr<Symbol>,
    ) -> Result<ArcType> {
        expr.typecheck_expected(self, vm, file, expr_str, None)
            .map(|result| result.typ)
    }

    pub fn typecheck_str(
        &mut self,
        vm: &Thread,
        file: &str,
        expr_str: &str,
        expected_type: Option<&ArcType>,
    ) -> Result<(SpannedExpr<Symbol>, ArcType)> {
        let TypecheckValue { expr, typ } =
            expr_str.typecheck_expected(self, vm, file, expr_str, expected_type)?;
        Ok((expr, typ))
    }

    /// Compiles `expr` into a function which can be added and run by the `vm`
    pub fn compile_script(
        &mut self,
        vm: &Thread,
        filename: &str,
        expr_str: &str,
        expr: &SpannedExpr<Symbol>,
    ) -> Result<CompiledModule> {
        TypecheckValue {
            expr: expr,
            typ: vm.global_env().type_cache().hole(),
        }.compile(self, vm, filename, expr_str, ())
            .map(|result| result.module)
    }

    /// Compiles the source code `expr_str` into bytecode serialized using `serializer`
    #[cfg(feature = "serialization")]
    pub fn compile_to_bytecode<S>(
        &mut self,
        thread: &Thread,
        name: &str,
        expr_str: &str,
        serializer: S,
    ) -> StdResult<S::Ok, Either<Error, S::Error>>
    where
        S: serde::Serializer,
        S::Error: 'static,
    {
        compile_to(expr_str, self, &thread, name, expr_str, None, serializer)
    }

    /// Loads bytecode from a `Deserializer` and stores it into the module `name`.
    ///
    /// `load_script` is equivalent to `compile_to_bytecode` followed by `load_bytecode`
    #[cfg(feature = "serialization")]
    pub fn load_bytecode<'vm, D>(
        &mut self,
        thread: &'vm Thread,
        name: &str,
        deserializer: D,
    ) -> BoxFutureValue<'vm, (), Error>
    where
        D: serde::Deserializer<'vm> + 'vm,
        D::Error: Send + Sync,
    {
        Precompiled(deserializer).load_script(self, thread, name, "", ())
    }

    /// Parses and typechecks `expr_str` followed by extracting metadata from the created
    /// expression
    pub fn extract_metadata(
        &mut self,
        vm: &Thread,
        file: &str,
        expr_str: &str,
    ) -> Result<(SpannedExpr<Symbol>, ArcType, Metadata)> {
        use check::metadata;
        let (mut expr, typ) = self.typecheck_str(vm, file, expr_str, None)?;

        let (metadata, _) = metadata::metadata(&*vm.get_env(), &mut expr);
        Ok((expr, typ, metadata))
    }

    /// Compiles `input` and if it is successful runs the resulting code and stores the resulting
    /// value in the vm.
    ///
    /// If at any point the function fails the resulting error is returned and nothing is added to
    /// the VM.
    pub fn load_script(&mut self, vm: &Thread, filename: &str, input: &str) -> Result<()> {
        self.load_script_async(vm, filename, input).wait()
    }

    pub fn load_script_async<'vm>(
        &mut self,
        vm: &'vm Thread,
        filename: &str,
        input: &str,
    ) -> BoxFutureValue<'vm, (), Error> {
        input.load_script(self, vm, filename, input, None)
    }

    /// Loads `filename` and compiles and runs its input by calling `load_script`
    pub fn load_file<'vm>(&mut self, vm: &'vm Thread, filename: &str) -> Result<()> {
        self.load_file_async(vm, filename).wait()
    }

    pub fn load_file_async<'vm>(
        &mut self,
        vm: &'vm Thread,
        filename: &str,
    ) -> BoxFutureValue<'vm, (), Error> {
        use macros::MacroExpander;

        // Use the import macro's path resolution if it exists so that we mimick the import
        // macro as close as possible
        let opt_macro = vm.get_macros().get("import");
        let owned_import;
        let import = match opt_macro
            .as_ref()
            .and_then(|mac| mac.downcast_ref::<Import>())
        {
            Some(import) => import,
            None => {
                owned_import = Import::new(DefaultImporter);
                &owned_import
            }
        };
        let module_name = Symbol::from(format!("@{}", filename_to_module(filename)));
        let mut macros = MacroExpander::new(vm);
        if let Err((_, err)) =
            import.load_module(self, vm, &mut macros, &module_name, Span::default())
        {
            macros.errors.push(pos::spanned(Span::default(), err));
        };
        FutureValue::from(macros.finish().map_err(|err| err.into())).boxed()
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
        &mut self,
        vm: &'vm Thread,
        name: &str,
        expr_str: &str,
    ) -> Result<(T, ArcType)>
    where
        T: Getable<'vm> + VmType + Send + 'vm,
    {
        self.run_expr_async(vm, name, expr_str).wait()
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
    ///     .run_expr_async::<String>(&vm, "example",
    ///         " let string  = import! \"std/string.glu\" in string.trim \"    Hello world  \t\" ")
    ///     .sync_or_error()
    ///     .unwrap();
    /// let expected = ("Hello world".to_string(), Type::string());
    ///
    /// assert_eq!(result, expected);
    /// }
    /// ```
    ///
    pub fn run_expr_async<'vm, T>(
        &mut self,
        vm: &'vm Thread,
        name: &str,
        expr_str: &str,
    ) -> BoxFutureValue<'vm, (T, ArcType), Error>
    where
        T: Getable<'vm> + VmType + Send + 'vm,
    {
        let expected = T::make_type(vm);
        expr_str
            .run_expr(self, vm, name, expr_str, Some(&expected))
            .and_then(move |execute_value| unsafe {
                FutureValue::sync(Ok((
                    T::from_value(vm, Variants::new(&execute_value.value.get_value())),
                    execute_value.typ,
                )))
            })
            .boxed()
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

        let prelude_expr = self.parse_expr(type_cache, "", PRELUDE).unwrap();
        let original_expr = mem::replace(expr, prelude_expr);

        // Set all spans in the prelude expression to -1 so that completion requests always
        // skips searching the implicit prelude
        use base::ast::{walk_mut_expr, walk_mut_pattern, MutVisitor, SpannedPattern};
        use base::pos::UNKNOWN_EXPANSION;
        struct ExpandedSpans;

        impl<'a> MutVisitor<'a> for ExpandedSpans {
            type Ident = Symbol;

            fn visit_expr(&mut self, e: &mut SpannedExpr<Self::Ident>) {
                e.span.expansion_id = UNKNOWN_EXPANSION;
                walk_mut_expr(self, e);
            }

            fn visit_pattern(&mut self, p: &mut SpannedPattern<Self::Ident>) {
                p.span.expansion_id = UNKNOWN_EXPANSION;
                walk_mut_pattern(self, &mut p.value);
            }
        }
        ExpandedSpans.visit_expr(expr);

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
and { Num, Eq, Ord, Show, Functor, Applicative, Monad, ? } = __implicit_prelude
and { Bool, not, ? } = import! std.bool
and { Option, ? } = import! std.option

let { (+), (-), (*), (/), (==), (/=), (<), (<=), (>=), (>), show, ? } = __implicit_prelude

let __implicit_float @ { ? } = import! std.float


let __implicit_int @ { ? } = import! std.int

let __implicit_string @ { ? } = import! std.string

let { error } = import! std.prim

in ()
"#;

#[derive(Default)]
pub struct VmBuilder {
    #[cfg(not(target_arch = "wasm32"))]
    event_loop: Option<::tokio_core::reactor::Remote>,
    import_paths: Option<Vec<PathBuf>>,
}

impl VmBuilder {
    pub fn new() -> VmBuilder {
        VmBuilder::default()
    }

    #[cfg(not(target_arch = "wasm32"))]
    option!{
        /// Sets then event loop which threads are run on
        /// (default: None)
        event_loop set_event_loop: Option<::tokio_core::reactor::Remote>
    }

    option!{
        /// Sets then event loop which threads are run on
        /// (default: ["."])
        import_paths set_import_paths: Option<Vec<PathBuf>>
    }

    pub fn build(self) -> RootedThread {
        #[cfg(target_arch = "wasm32")]
        let vm = RootedThread::new();

        #[cfg(not(target_arch = "wasm32"))]
        let vm = RootedThread::with_global_state(
            ::vm::vm::GlobalVmStateBuilder::new()
                .event_loop(self.event_loop)
                .build(),
        );

        let import = Import::new(DefaultImporter);
        if let Some(import_paths) = self.import_paths {
            import.set_paths(import_paths);
        }

        if let Ok(gluon_path) = env::var("GLUON_PATH") {
            import.add_path(gluon_path);
        }
        vm.get_macros().insert(String::from("import"), import);

        Compiler::new()
            .implicit_prelude(false)
            .run_expr_async::<OpaqueValue<&Thread, Hole>>(&vm, "", r#" import! std.types "#)
            .sync_or_error()
            .unwrap_or_else(|err| panic!("{}", err));

        add_extern_module(&vm, "std.prim", ::vm::primitives::load);
        add_extern_module(&vm, "std.byte.prim", ::vm::primitives::load_byte);
        add_extern_module(&vm, "std.int.prim", ::vm::primitives::load_int);
        add_extern_module(&vm, "std.float.prim", ::vm::primitives::load_float);
        add_extern_module(&vm, "std.string.prim", ::vm::primitives::load_string);
        add_extern_module(&vm, "std.char.prim", ::vm::primitives::load_char);
        add_extern_module(&vm, "std.array.prim", ::vm::primitives::load_array);

        add_extern_module(&vm, "std.lazy", ::vm::lazy::load);
        add_extern_module(&vm, "std.reference", ::vm::reference::load);

        add_extern_module(&vm, "std.channel", ::vm::channel::load_channel);
        add_extern_module(&vm, "std.thread.prim", ::vm::channel::load_thread);
        add_extern_module(&vm, "std.debug", ::vm::debug::load);
        add_extern_module(&vm, "std.io.prim", ::io::load);

        load_regex(&vm);
        load_random(&vm);

        vm
    }
}

/// Creates a new virtual machine with support for importing other modules and with all primitives
/// loaded.
pub fn new_vm() -> RootedThread {
    VmBuilder::default().build()
}

#[cfg(feature = "regex")]
fn load_regex(vm: &Thread) {
    add_extern_module(&vm, "std.regex", ::regex_bind::load);
}
#[cfg(not(feature = "regex"))]
fn load_regex(_: &Thread) {}

#[cfg(all(feature = "rand", not(target_arch = "wasm32")))]
fn load_random(vm: &Thread) {
    add_extern_module(&vm, "std.random.prim", ::rand_bind::load);
}
#[cfg(any(not(feature = "rand"), target_arch = "wasm32"))]
fn load_random(_: &Thread) {}

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
