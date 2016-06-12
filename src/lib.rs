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
pub mod c_api;

pub use vm::thread::{RootedThread, Thread};

use std::result::Result as StdResult;
use std::string::String as StdString;

use base::ast;
use base::types::TcType;
use base::symbol::{Name, NameBuf, Symbol, Symbols, SymbolModule};
use base::metadata::Metadata;

use vm::Variants;
use vm::api::generic::A;
use vm::api::{Getable, VMType, Generic, IO};
use vm::Error as VMError;
use vm::compiler::CompiledFunction;
use vm::thread::{RootedValue, ThreadInternal};
use vm::internal::ClosureDataDef;

quick_error! {
    /// Error type wrapping all possible errors that can be generated from gluon
    #[derive(Debug)]
    pub enum Error {
        /// Error found when parsing gluon code
        Parse(err: ::parser::Error) {
            description(err.description())
            display("{}", err)
            from()
        }
        /// Error found when typechecking gluon code
        Typecheck(err: ::base::error::InFile<::check::typecheck::TypeError<Symbol>>) {
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
        Macro(err: ::base::error::Errors<::base::macros::Error>) {
            description(err.description())
            display("{}", err)
            from()
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
    pub fn parse_expr(&mut self,
                      file: &str,
                      input: &str)
                      -> StdResult<ast::LExpr<ast::TcIdent<Symbol>>, ::parser::Error> {
        Ok(try!(::parser::parse_tc(&mut SymbolModule::new(file.into(), &mut self.symbols),
                                   input)))
    }

    /// Parse and typecheck `expr_str` returning the typechecked expression and type of the
    /// expression
    pub fn typecheck_expr(&mut self,
                          vm: &Thread,
                          file: &str,
                          expr_str: &str)
                          -> Result<(ast::LExpr<ast::TcIdent<Symbol>>, TcType)> {
        self.typecheck_expr_expected(vm, file, expr_str, None)
    }

    fn typecheck_expr_expected(&mut self,
                               vm: &Thread,
                               file: &str,
                               expr_str: &str,
                               expected_type: Option<&TcType>)
                               -> Result<(ast::LExpr<ast::TcIdent<Symbol>>, TcType)> {
        use check::typecheck::Typecheck;
        use base::error;
        let mut expr = try!(self.parse_expr(file, expr_str));
        if self.implicit_prelude {
            self.include_implicit_prelude(file, &mut expr);
        }
        try!(vm.get_macros().run(vm, &mut expr));
        let env = vm.get_env();
        let mut tc = Typecheck::new(file.into(), &mut self.symbols, &*env);
        let typ = try!(tc.typecheck_expr_expected(&mut expr, expected_type)
                         .map_err(|err| error::InFile::new(StdString::from(file), expr_str, err)));
        Ok((expr, typ))
    }

    /// Compiles `expr` into a function which can be added and run by the `vm`
    pub fn compile_script(&mut self,
                          vm: &Thread,
                          filename: &str,
                          expr: &ast::LExpr<ast::TcIdent<Symbol>>)
                          -> CompiledFunction {
        use vm::compiler::Compiler;
        debug!("Compile `{}`", filename);
        let mut function = {
            let env = vm.get_env();
            let name = Name::new(filename);
            let name = NameBuf::from(name.module());
            let symbols = SymbolModule::new(StdString::from(name.as_ref()), &mut self.symbols);
            let mut compiler = Compiler::new(&*env, vm.global_env(), symbols);
            compiler.compile_expr(&expr)
        };
        function.id = Symbol::new(filename);
        function
    }

    /// Parses and typechecks `expr_str` followed by extracting metadata from the created
    /// expression
    pub fn extract_metadata(&mut self,
                            vm: &Thread,
                            file: &str,
                            expr_str: &str)
                            -> Result<(ast::LExpr<ast::TcIdent<Symbol>>, TcType, Metadata)> {
        use check::metadata;
        let (mut expr, typ) = try!(self.typecheck_expr(vm, file, expr_str));

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
        let function = self.compile_script(vm, filename, &expr);
        let function = vm.global_env().new_function(function);
        let closure = {
            let stack = vm.current_frame();
            vm.alloc(&stack.stack, ClosureDataDef(function, &[]))
        };
        let value = try!(vm.call_module(&typ, closure));
        try!(vm.global_env().set_global(function.name.clone(), typ, metadata, value));
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
        let (expr, typ) = try!(self.typecheck_expr_expected(vm, name, expr_str, expected_type));
        let mut function = self.compile_script(vm, name, &expr);
        function.id = Symbol::new(name);
        let function = vm.global_env().new_function(function);
        let closure = {
            let stack = vm.current_frame();
            vm.alloc(&stack.stack, ClosureDataDef(function, &[]))
        };
        let value = try!(vm.call_module(&typ, closure));
        Ok((vm.root_value_ref(value), typ))
    }

    /// Compiles and runs the expression in `expr_str`. If successful the value from running the
    /// expression is returned
    pub fn run_expr<'vm, T>(&mut self, vm: &'vm Thread, name: &str, expr_str: &str) -> Result<T>
        where T: Getable<'vm> + VMType
    {
        let expected = T::make_type(vm);
        let (value, actual) = try!(self.run_expr_(vm, name, expr_str, Some(&expected)));
        unsafe {
            T::from_value(vm, Variants::new(&value))
                .ok_or_else(move || Error::from(VMError::WrongType(expected, actual)))
        }
    }

    pub fn run_io_expr<'vm, T>(&mut self, vm: &'vm Thread, name: &str, expr_str: &str) -> Result<T>
        where T: Getable<'vm> + VMType,
              T::Type: Sized
    {
        let expected = IO::<T>::make_type(vm);
        let (value, actual) = try!(self.run_expr_(vm, name, expr_str, Some(&expected)));
        unsafe {
            T::from_value(vm, Variants::new(&value))
                .ok_or_else(move || Error::from(VMError::WrongType(expected, actual)))
        }
    }

    fn include_implicit_prelude(&mut self,
                                name: &str,
                                expr: &mut ast::LExpr<ast::TcIdent<Symbol>>) {
        use std::mem;
        if name == "std.prelude" {
            return;
        }

        let prelude_import = r#"
    let __implicit_prelude = import "std/prelude.hs"
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
        fn assign_last_body(l: &mut ast::LExpr<ast::TcIdent<Symbol>>,
                            original_expr: ast::LExpr<ast::TcIdent<Symbol>>) {
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

fn filename_to_module(filename: &str) -> StdString {
    use std::path::Path;
    let path = Path::new(filename);
    let name = path.extension()
                   .map(|ext| {
                       ext.to_str()
                          .map(|ext| &filename[..filename.len() - ext.len() - 1])
                          .unwrap_or(filename)
                   })
                   .expect("filename");

    name.replace("/", ".")
}

/// Creates a new virtual machine with support for importing other modules and with all primitives
/// loaded.
pub fn new_vm() -> RootedThread {
    let vm = RootedThread::new();
    vm.get_macros().insert(String::from("import"), ::import::Import::new());
    Compiler::new()
        .implicit_prelude(false)
        .run_expr::<Generic<A>>(&vm, "", r#" import "std/types.hs" "#)
        .unwrap();
    ::vm::primitives::load(&vm).expect("Loaded primitives library");
    ::vm::channel::load(&vm).expect("Loaded channel library");
    ::io::load(&vm).expect("Loaded IO library");
    vm
}
