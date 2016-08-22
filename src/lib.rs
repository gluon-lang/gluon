//! This crate contains contains the implementation for the gluon programming language.
//!
//! Gluon is a programming language suitable for embedding in an existing application to extend its
//! behaviour. For information about how to use this library the best resource currently is the
//! [tutorial](https://github.com/Marwes/gluon/blob/master/TUTORIAL.md) which contains examples on
//! how to write gluon programs as well as how to run them using this library.
#[macro_use]
extern crate log;
#[macro_use]
extern crate quick_error;

#[macro_use]
pub extern crate gluon_vm as vm;
pub extern crate gluon_base as base;
pub extern crate gluon_parser as parser;
pub extern crate gluon_check as check;

mod io;
pub mod import;

pub use vm::thread::{RootedThread, Thread};

use std::result::Result as StdResult;
use std::string::String as StdString;
use std::env;

use base::ast;
use base::error::{Errors, InFile as InFileError};
use base::metadata::Metadata;
use base::source::Source;
use base::symbol::{Name, NameBuf, Symbol, Symbols, SymbolModule};
use base::types::TcType;

use vm::Variants;
use vm::api::generic::A;
use vm::api::{Getable, VmType, Generic, IO};
use vm::Error as VmError;
use vm::compiler::CompiledFunction;
use vm::thread::{RootedValue, ThreadInternal};
use vm::internal::ClosureDataDef;
use vm::macros;

quick_error! {
    /// Error type wrapping all possible errors that can be generated from gluon
    #[derive(Debug)]
    pub enum Error {
        /// Error found when parsing gluon code
        Parse(err: Errors<::parser::Error>) {
            description(err.description())
            display("{}", err)
            from()
        }
        /// Error found when typechecking gluon code
        Typecheck(err: InFileError) {
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
        Macro(err: macros::Error) {
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

impl From<Errors<macros::Error>> for Error {
    fn from(mut errors: Errors<macros::Error>) -> Error {
        if errors.errors.len() == 1 {
            let err = errors.errors.pop().unwrap();
            match err.downcast::<Error>() {
                Ok(err) => *err,
                Err(err) => Error::Macro(err),
            }
        } else {
            Error::Multiple(Errors {
                errors: errors.errors
                    .into_iter()
                    .map(|err| match err.downcast::<Error>() {
                        Ok(err) => *err,
                        Err(err) => Error::Macro(err),
                    })
                    .collect(),
            })
        }
    }
}


impl From<Errors<Error>> for Error {
    fn from(mut errors: Errors<Error>) -> Error {
        if errors.errors.len() == 1 {
            errors.errors.pop().unwrap()
        } else {
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
}

/// Advanced compiler pipeline which ensures that the compilation phases are run in order even if
/// not the entire compilation procedure is needed
pub mod compiler_pipeline {
    use super::*;

    use base::ast;
    use base::types::TcType;
    use base::symbol::Symbol;

    use vm::compiler::CompiledFunction;
    use vm::thread::{RootedValue, ThreadInternal};
    use vm::internal::ClosureDataDef;

    pub struct MacroValue(pub ast::SpannedExpr<ast::TcIdent<Symbol>>);

    pub trait MacroExpandable {
        fn expand_macro(self,
                        compiler: &mut Compiler,
                        thread: &Thread,
                        file: &str)
                        -> Result<MacroValue>;
    }

    impl<'s> MacroExpandable for &'s str {
        fn expand_macro(self,
                        compiler: &mut Compiler,
                        thread: &Thread,
                        file: &str)
                        -> Result<MacroValue> {
            compiler.parse_expr(file, self)
                .map_err(From::from)
                .and_then(|expr| expr.expand_macro(compiler, thread, file))
        }
    }

    impl MacroExpandable for ast::SpannedExpr<ast::TcIdent<Symbol>> {
        fn expand_macro(mut self,
                        compiler: &mut Compiler,
                        thread: &Thread,
                        file: &str)
                        -> Result<MacroValue> {
            if compiler.implicit_prelude {
                compiler.include_implicit_prelude(file, &mut self);
            }
            try!(thread.get_macros().run(thread, &mut self));
            Ok(MacroValue(self))
        }
    }

    pub struct TypecheckValue(pub ast::SpannedExpr<ast::TcIdent<Symbol>>, pub TcType);

    pub trait Typecheckable {
        fn typecheck(self,
                     compiler: &mut Compiler,
                     thread: &Thread,
                     file: &str,
                     expr_str: &str)
                     -> Result<TypecheckValue>
            where Self: Sized
        {
            self.typecheck_expected(compiler, thread, file, expr_str, None)
        }
        fn typecheck_expected(self,
                              compiler: &mut Compiler,
                              thread: &Thread,
                              file: &str,
                              expr_str: &str,
                              expected_type: Option<&TcType>)
                              -> Result<TypecheckValue>;
    }
    impl<T> Typecheckable for T
        where T: MacroExpandable
    {
        fn typecheck_expected(self,
                              compiler: &mut Compiler,
                              thread: &Thread,
                              file: &str,
                              expr_str: &str,
                              expected_type: Option<&TcType>)
                              -> Result<TypecheckValue>
            where Self: Sized
        {
            self.expand_macro(compiler, thread, file)
                .and_then(|expr| {
                    expr.typecheck_expected(compiler, thread, file, expr_str, expected_type)
                })
        }
    }
    impl Typecheckable for MacroValue {
        fn typecheck_expected(mut self,
                              compiler: &mut Compiler,
                              thread: &Thread,
                              file: &str,
                              expr_str: &str,
                              expected_type: Option<&TcType>)
                              -> Result<TypecheckValue>
            where Self: Sized
        {
            compiler.typecheck_expr_expected(thread, file, expr_str, &mut self.0, expected_type)
                .map(move |typ| TypecheckValue(self.0, typ))
        }
    }

    pub struct CompileValue(pub ast::SpannedExpr<ast::TcIdent<Symbol>>,
                            pub TcType,
                            pub CompiledFunction);

    pub trait Compileable<Extra> {
        fn compile(self,
                   compiler: &mut Compiler,
                   thread: &Thread,
                   file: &str,
                   arg: Extra)
                   -> Result<CompileValue>;
    }
    impl<'a, 'b, T> Compileable<(&'a str, Option<&'b TcType>)> for T
        where T: Typecheckable
    {
        fn compile(self,
                   compiler: &mut Compiler,
                   thread: &Thread,
                   file: &str,
                   (expr_str, expected_type): (&'a str, Option<&'b TcType>))
                   -> Result<CompileValue> {
            self.typecheck_expected(compiler, thread, file, expr_str, expected_type)
                .and_then(|tc_value| tc_value.compile(compiler, thread, file, ()))
        }
    }
    impl<Extra> Compileable<Extra> for TypecheckValue {
        fn compile(self,
                   compiler: &mut Compiler,
                   thread: &Thread,
                   file: &str,
                   _: Extra)
                   -> Result<CompileValue> {
            let function = try!(compiler.compile_script(thread, file, &self.0));
            Ok(CompileValue(self.0, self.1, function))
        }
    }

    pub trait Executable<Extra> {
        fn run_expr<'vm>(self,
                         compiler: &mut Compiler,
                         vm: &'vm Thread,
                         name: &str,
                         arg: Extra)
                         -> Result<(RootedValue<&'vm Thread>, TcType)>;
        fn load_script(self,
                       compiler: &mut Compiler,
                       vm: &Thread,
                       filename: &str,
                       arg: Extra)
                       -> Result<()>;
    }
    impl<C, Extra> Executable<Extra> for C
        where C: Compileable<Extra>
    {
        fn run_expr<'vm>(self,
                         compiler: &mut Compiler,
                         vm: &'vm Thread,
                         name: &str,
                         arg: Extra)
                         -> Result<(RootedValue<&'vm Thread>, TcType)> {

            self.compile(compiler, vm, name, arg)
                .and_then(|v| v.run_expr(compiler, vm, name, ()))
        }
        fn load_script(self,
                       compiler: &mut Compiler,
                       vm: &Thread,
                       filename: &str,
                       arg: Extra)
                       -> Result<()> {
            self.compile(compiler, vm, filename, arg)
                .and_then(|v| v.load_script(compiler, vm, filename, ()))
        }
    }
    impl Executable<()> for CompileValue {
        fn run_expr<'vm>(self,
                         _compiler: &mut Compiler,
                         vm: &'vm Thread,
                         name: &str,
                         _: ())
                         -> Result<(RootedValue<&'vm Thread>, TcType)> {
            let CompileValue(_, typ, mut function) = self;
            function.id = Symbol::new(name);
            let function = try!(vm.global_env().new_function(function));
            let closure = {
                let stack = vm.current_frame();
                try!(vm.alloc(&stack.stack, ClosureDataDef(function, &[])))
            };
            let value = try!(vm.call_module(&typ, closure));
            Ok((vm.root_value_ref(value), typ))
        }
        fn load_script(self,
                       _compiler: &mut Compiler,
                       vm: &Thread,
                       _filename: &str,
                       _: ())
                       -> Result<()> {
            use check::metadata;

            let CompileValue(mut expr, typ, function) = self;
            let metadata = metadata::metadata(&*vm.get_env(), &mut expr);
            let function = try!(vm.global_env().new_function(function));
            let closure = {
                let stack = vm.current_frame();
                try!(vm.alloc(&stack.stack, ClosureDataDef(function, &[])))
            };
            let value = try!(vm.call_module(&typ, closure));
            try!(vm.global_env().set_global(function.name.clone(), typ, metadata, value));
            Ok(())
        }
    }
}

impl Compiler {
    /// Creates a new compiler with default settings
    pub fn new() -> Compiler {
        Compiler {
            symbols: Symbols::new(),
            implicit_prelude: true,
        }
    }

    /// Sets wheter the implicit prelude should be include when compiling a file using this
    /// compiler (default: true)
    pub fn implicit_prelude(mut self, implicit_prelude: bool) -> Compiler {
        self.implicit_prelude = implicit_prelude;
        self
    }

    /// Parse `input`, returning an expression if successful
    pub fn parse_expr
        (&mut self,
         file: &str,
         input: &str)
         -> StdResult<ast::SpannedExpr<ast::TcIdent<Symbol>>, Errors<::parser::Error>> {
        Ok(try!(::parser::parse_tc(&mut SymbolModule::new(file.into(), &mut self.symbols),
                                   input)
            .map_err(|t| t.1)))
    }

    /// Parse `input`, returning an expression if successful
    pub fn parse_partial_expr(&mut self,
                              file: &str,
                              input: &str)
                              -> StdResult<ast::SpannedExpr<ast::TcIdent<Symbol>>,
                                           (Option<ast::SpannedExpr<ast::TcIdent<Symbol>>>,
                                            Errors<::parser::Error>)> {
        ::parser::parse_tc(&mut SymbolModule::new(file.into(), &mut self.symbols),
                           input)
    }

    /// Parse and typecheck `expr_str` returning the typechecked expression and type of the
    /// expression
    pub fn typecheck_expr(&mut self,
                          vm: &Thread,
                          file: &str,
                          expr_str: &str,
                          expr: &mut ast::SpannedExpr<ast::TcIdent<Symbol>>)
                          -> Result<TcType> {
        self.typecheck_expr_expected(vm, file, expr_str, expr, None)
    }

    fn typecheck_expr_expected(&mut self,
                               vm: &Thread,
                               file: &str,
                               expr_str: &str,
                               expr: &mut ast::SpannedExpr<ast::TcIdent<Symbol>>,
                               expected_type: Option<&TcType>)
                               -> Result<TcType> {
        use check::typecheck::Typecheck;

        let env = vm.get_env();
        let mut tc = Typecheck::new(file.into(), &mut self.symbols, &*env);
        let source = Source::new(expr_str);

        let typ = try!(tc.typecheck_expr_expected(expr, expected_type)
            .map_err(|err| InFileError::new(file, &source, err)));

        Ok(typ)
    }

    pub fn typecheck_str(&mut self,
                         vm: &Thread,
                         file: &str,
                         expr_str: &str,
                         expected_type: Option<&TcType>)
                         -> Result<(ast::SpannedExpr<ast::TcIdent<Symbol>>, TcType)> {
        let mut expr = try!(self.parse_expr(file, expr_str));
        if self.implicit_prelude {
            self.include_implicit_prelude(file, &mut expr);
        }
        try!(vm.get_macros().run(vm, &mut expr));
        let typ = try!(self.typecheck_expr_expected(vm, file, expr_str, &mut expr, expected_type));
        Ok((expr, typ))
    }

    /// Compiles `expr` into a function which can be added and run by the `vm`
    pub fn compile_script(&mut self,
                          vm: &Thread,
                          filename: &str,
                          expr: &ast::SpannedExpr<ast::TcIdent<Symbol>>)
                          -> Result<CompiledFunction> {
        use vm::compiler::Compiler;
        debug!("Compile `{}`", filename);
        let mut function = {
            let env = vm.get_env();
            let name = Name::new(filename);
            let name = NameBuf::from(name.module());
            let symbols = SymbolModule::new(StdString::from(AsRef::<str>::as_ref(&name)),
                                            &mut self.symbols);
            let mut compiler = Compiler::new(&*env, vm.global_env(), symbols);
            try!(compiler.compile_expr(&expr))
        };
        function.id = Symbol::new(filename);
        Ok(function)
    }

    /// Parses and typechecks `expr_str` followed by extracting metadata from the created
    /// expression
    pub fn extract_metadata
        (&mut self,
         vm: &Thread,
         file: &str,
         expr_str: &str)
         -> Result<(ast::SpannedExpr<ast::TcIdent<Symbol>>, TcType, Metadata)> {
        use check::metadata;
        let (mut expr, typ) = try!(self.typecheck_str(vm, file, expr_str, None));

        let metadata = metadata::metadata(&*vm.get_env(), &mut expr);
        Ok((expr, typ, metadata))
    }

    /// Compiles `input` and if it is successful runs the resulting code and stores the resulting
    /// value in the vm.
    ///
    /// If at any point the function fails the resulting error is returned and nothing is added to
    /// the VM.
    pub fn load_script(&mut self, vm: &Thread, filename: &str, input: &str) -> Result<()> {
        let (expr, typ, metadata) = try!(self.extract_metadata(vm, filename, input));
        let function = try!(self.compile_script(vm, filename, &expr));
        let function = try!(vm.global_env().new_function(function));
        let closure = {
            let stack = vm.current_frame();
            try!(vm.alloc(&stack.stack, ClosureDataDef(function, &[])))
        };
        let value = try!(vm.call_module(&typ, closure));
        try!(vm.global_env().set_global(function.name.clone(), typ, metadata, value));
        info!("Loaded module `{}` filename", filename);
        Ok(())
    }

    /// Loads `filename` and compiles and runs its input by calling `load_script`
    pub fn load_file(&mut self, vm: &Thread, filename: &str) -> Result<()> {
        use std::fs::File;
        use std::io::Read;
        let mut buffer = StdString::new();
        {
            let mut file = try!(File::open(filename));
            try!(file.read_to_string(&mut buffer));
        }
        let name = filename_to_module(filename);
        self.load_script(vm, &name, &buffer)
    }

    fn run_expr_<'vm>(&mut self,
                      vm: &'vm Thread,
                      name: &str,
                      expr_str: &str,
                      expected_type: Option<&TcType>)
                      -> Result<(RootedValue<&'vm Thread>, TcType)> {
        let (expr, typ) = try!(self.typecheck_str(vm, name, expr_str, expected_type));
        let mut function = try!(self.compile_script(vm, name, &expr));
        function.id = Symbol::new(name);
        let function = try!(vm.global_env().new_function(function));
        let closure = {
            let stack = vm.current_frame();
            try!(vm.alloc(&stack.stack, ClosureDataDef(function, &[])))
        };
        let value = try!(vm.call_module(&typ, closure));
        Ok((vm.root_value_ref(value), typ))
    }

    /// Compiles and runs the expression in `expr_str`. If successful the value from running the
    /// expression is returned
    pub fn run_expr<'vm, T>(&mut self,
                            vm: &'vm Thread,
                            name: &str,
                            expr_str: &str)
                            -> Result<(T, TcType)>
        where T: Getable<'vm> + VmType
    {
        let expected = T::make_type(vm);
        let (value, actual) = try!(self.run_expr_(vm, name, expr_str, Some(&expected)));
        unsafe {
            match T::from_value(vm, Variants::new(&value)) {
                Some(value) => Ok((value, actual)),
                None => Err(Error::from(VmError::WrongType(expected, actual))),
            }
        }
    }

    pub fn run_io_expr<'vm, T>(&mut self,
                               vm: &'vm Thread,
                               name: &str,
                               expr_str: &str)
                               -> Result<(T, TcType)>
        where T: Getable<'vm> + VmType,
              T::Type: Sized
    {
        let expected = IO::<T>::make_type(vm);
        let (value, actual) = try!(self.run_expr_(vm, name, expr_str, Some(&expected)));
        unsafe {
            match T::from_value(vm, Variants::new(&value)) {
                Some(value) => Ok((value, actual)),
                None => Err(Error::from(VmError::WrongType(expected, actual))),
            }
        }
    }

    fn include_implicit_prelude(&mut self,
                                name: &str,
                                expr: &mut ast::SpannedExpr<ast::TcIdent<Symbol>>) {
        use std::mem;
        if name == "std.prelude" {
            return;
        }

        let prelude_import = r#"
    let __implicit_prelude = import "std/prelude.glu"
    and { Num, Eq, Ord, Show, Functor, Monad, Bool, Option, Result, not } = __implicit_prelude

    let { (+), (-), (*), (/) } = __implicit_prelude.num_Int
    and { (==) } = __implicit_prelude.eq_Int
    and { (<), (<=), (>=), (>) } = __implicit_prelude.make_Ord __implicit_prelude.ord_Int

    let { (+), (-), (*), (/) } = __implicit_prelude.num_Float
    and { (==) } = __implicit_prelude.eq_Float
    and { (<), (<=), (>=), (>) } = __implicit_prelude.make_Ord __implicit_prelude.ord_Float

    let { (==) } = __implicit_prelude.eq_Char
    and { (<), (<=), (>=), (>) } = __implicit_prelude.make_Ord __implicit_prelude.ord_Char

    in 0
    "#;
        let prelude_expr = self.parse_expr("", prelude_import).unwrap();
        let original_expr = mem::replace(expr, prelude_expr);
        fn assign_last_body(l: &mut ast::SpannedExpr<ast::TcIdent<Symbol>>,
                            original_expr: ast::SpannedExpr<ast::TcIdent<Symbol>>) {
            match l.value {
                ast::Expr::Let(_, ref mut e) => {
                    assign_last_body(e, original_expr);
                }
                _ => *l = original_expr,
            }
        }
        assign_last_body(expr, original_expr);
    }
}

pub fn filename_to_module(filename: &str) -> StdString {
    use std::path::Path;
    let path = Path::new(filename);
    let name = path.extension()
        .map_or(filename, |ext| {
            ext.to_str()
                .map(|ext| &filename[..filename.len() - ext.len() - 1])
                .unwrap_or(filename)
        });

    name.replace(|c: char| c == '/' || c == '\\', ".")
}

/// Creates a new virtual machine with support for importing other modules and with all primitives
/// loaded.
pub fn new_vm() -> RootedThread {
    use ::import::{DefaultImporter, Import};

    let vm = RootedThread::new();
    let gluon_path = env::var("GLUON_PATH").unwrap_or(String::from("."));
    let import = Import::new(DefaultImporter);
    import.add_path(gluon_path);
    vm.get_macros()
        .insert(String::from("import"), import);

    Compiler::new()
        .implicit_prelude(false)
        .run_expr::<Generic<A>>(&vm, "", r#" import "std/types.glu" "#)
        .unwrap();
    ::vm::primitives::load(&vm).expect("Loaded primitives library");
    ::vm::channel::load(&vm).expect("Loaded channel library");
    ::io::load(&vm).expect("Loaded IO library");
    vm
}
