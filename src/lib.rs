//! # Example
//!
//! ```rust
//! # extern crate env_logger;
//! # extern crate embed_lang;
//!
//! use embed_lang::{new_vm, Compiler};
//!
//! # fn main() {
//! # let _ = ::env_logger::init();
//!
//! let text = r#"
//! // `let` declares new variables.
//! let id x = x
//!
//! let factorial n =
//!         if n < 2
//!         then 1
//!         else n * factorial (n - 1)
//!
//! // `type` is used to declare a new type.
//! // In this case we declare `Countable` to be a record with a single field (count) which is a function
//! // taking a single arguemnt and returning an integer
//! type Countable a = { count: a -> Int }
//!
//! // "Counting" an integer just means returning the integer itself
//! let countable_Int: Countable Int = { count = \x -> x }
//!
//! let list_module =
//!     // Declare a new type which only exists in the current scope
//!     type List a = | Cons a (List a) | Nil
//!     let map f xs =
//!             case xs of
//!                 | Cons y ys -> Cons (f y) (map f ys)
//!                 | Nil -> Nil
//!     // Define a count instance over lists which counts each of the elements and sums
//!     // the results
//!     let countable_List c: Countable a -> Countable (List a) =
//!         let count xs =
//!             case xs of
//!             | Cons y ys -> c.count y + count ys
//!             | Nil -> 0
//!         { count }
//!     {
//!         // Since `List` is local we export it so its constructors can be used
//!         // outside the current scope
//!         List,
//!         countable_List,
//!         map
//!     }
//!
//! // Bring the `List` type and its constructors into scope
//! let { List, countable_List } = list_module
//! // Create a `Countable` record for `List Int`
//! let { count }: Countable (List Int) = countable_List countable_Int
//! if count (Cons 20 (Cons 22 Nil)) == 41 then
//!     error "This branch is not executed"
//! else
//!     io.print "Hello world!"
//! "#;
//!
//! let vm = new_vm();
//! match Compiler::new().run_expr(&vm, "example", text) {
//!     Ok(value) => {
//!         println!("{:?}", value);
//!     }
//!     Err(err) => {
//!         panic!("{}", err);
//!     }
//! }
//! return;
//!
//! # }
//! ```

#[macro_use]
extern crate log;
extern crate env_logger;
#[macro_use]
extern crate quick_error;

#[macro_use]
pub extern crate vm;
pub extern crate base;
pub extern crate parser;
pub extern crate check;

mod io;
pub mod import;

pub use vm::vm::VM;


use std::result::Result as StdResult;
use std::string::String as StdString;
use std::error::Error as StdError;

use base::ast;
use base::types::TcType;
use base::symbol::{Name, NameBuf, Symbol, Symbols, SymbolModule};
use base::metadata::Metadata;
use vm::vm::{ClosureDataDef, RootedValue};
use vm::compiler::CompiledFunction;

quick_error! {
    #[derive(Debug)]
    pub enum Error {
        Parse(err: ::parser::Error) {
            description(err.description())
            display("{}", err)
            from()
        }
        Typecheck(err: ::base::error::InFile<::check::typecheck::TypeError<Symbol>>) {
            description(err.description())
            display("{}", err)
            from()
        }
        IO(err: ::std::io::Error) {
            description(err.description())
            display("{}", err)
            from()
        }
        VM(err: ::vm::vm::Error) {
            description(err.description())
            display("{}", err)
            from()
        }
        Macro(err: ::base::error::Errors<::base::macros::Error>) {
            description(err.description())
            display("{}", err)
            from()
        }
    }
}

pub type Result<T> = StdResult<T, Error>;

pub struct Compiler {
    symbols: Symbols,
    implicit_prelude: bool,
}

impl Compiler {
    /// Creates a new compiler with default settings
    pub fn new() -> Compiler {
        Compiler { symbols: Symbols::new(), implicit_prelude: true }
    }

    /// Sets wheter the implicit prelude should be include when compiling a file using this
    /// compiler (default: true)
    pub fn implicit_prelude(mut self, implicit_prelude: bool) -> Compiler {
        self.implicit_prelude = implicit_prelude;
        self
    }

    pub fn parse_expr(&mut self,
                      file: &str,
                      input: &str)
                      -> StdResult<ast::LExpr<ast::TcIdent<Symbol>>, ::parser::Error> {
        Ok(try!(::parser::parse_tc(&mut SymbolModule::new(file.into(), &mut self.symbols), input)))
    }

    pub fn typecheck_expr(&mut self,
                       vm: &VM,
                       file: &str,
                       expr_str: &str)
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
        let typ = try!(tc.typecheck_expr(&mut expr)
                         .map_err(|err| error::InFile::new(StdString::from(file), expr_str, err)));
        Ok((expr, typ))
    }

    pub fn compile_script(&mut self,
                      vm: &VM,
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
            let mut compiler = Compiler::new(&*env, vm, symbols);
            compiler.compile_expr(&expr)
        };
        function.id = Symbol::new(filename);
        function
    }

    pub fn extract_metadata(&mut self,
                            vm: &VM,
                            file: &str,
                            expr_str: &str) -> Result<(ast::LExpr<ast::TcIdent<Symbol>>, TcType, Metadata)> {
        use check::metadata;
        let (mut expr, typ) = try!(self.typecheck_expr(
                                                   vm,
                                                   file,
                                                   expr_str));

        let metadata = metadata::metadata(&*vm.get_env(), &mut expr);
        Ok((expr, typ, metadata))
    }

    /// Compiles `input` and if it is successful runs the resulting code and stores the resulting value
    /// in the global variable named by running `filename_to_module` on `filename`.
    ///
    /// If at any point the function fails the resulting error is returned and nothing is added to the
    /// VM.
    pub fn load_script(&mut self, vm: &VM, filename: &str, input: &str) -> Result<()> {
        let (expr, typ, metadata) = try!(self.extract_metadata(vm, filename, input));
        let function = self.compile_script(vm, filename, &expr);
        let function = vm.new_function(function);
        let closure = {
            let stack = vm.current_frame();
            vm.alloc(&stack.stack, ClosureDataDef(function, &[]))
        };
        let value = try!(vm.call_module(&typ, closure));
        try!(vm.set_global(function.name.clone(), typ, metadata, value));
        Ok(())
    }

    /// Loads `filename` and compiles and runs its input by calling `load_script`
    pub fn load_file(&mut self, vm: &VM, filename: &str) -> Result<()> {
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

    /// Compiles and runs the expression in `expr_str`. If successful the value from running the
    /// expression is returned
    pub fn run_expr<'vm>(&mut self, vm: &'vm VM, name: &str, expr_str: &str) -> Result<RootedValue<'vm>> {
        let (expr, typ) = try!(self.typecheck_expr(vm, name, expr_str));
        let mut function = self.compile_script(vm, name, &expr);
        function.id = Symbol::new(name);
        let function = vm.new_function(function);
        let closure = {
            let stack = vm.current_frame();
            vm.alloc(&stack.stack, ClosureDataDef(function, &[]))
        };
        let value = try!(vm.call_module(&typ, closure));
        Ok(vm.root_value(value))
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
    and { Num, Eq, Ord, Show, Functor, Monad, Option, Result, not } = __implicit_prelude
    in
    let { (+), (-), (*), (/) } = __implicit_prelude.num_Int
    and { (==) } = __implicit_prelude.eq_Int
    and { (<), (<=), (=>), (>) } = __implicit_prelude.make_Ord __implicit_prelude.ord_Int
    in
    let { (+), (-), (*), (/) } = __implicit_prelude.num_Float
    and { (==) } = __implicit_prelude.eq_Float
    and { (<), (<=), (=>), (>) } = __implicit_prelude.make_Ord __implicit_prelude.ord_Float
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

pub fn filename_to_module(filename: &str) -> StdString {
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
pub fn new_vm() -> VM {
    let vm = VM::new();
    vm.get_macros().insert(String::from("import"), ::import::Import::new());
    Compiler::new()
        .implicit_prelude(false)
        .run_expr(&vm, "", r#" import "std/types.hs" "#).unwrap();
    ::vm::primitives::load(&vm).expect("Loaded primitives library");
    ::vm::channel::load(&vm).expect("Loaded channel library");
    ::io::load(&vm).expect("Loaded IO library");
    vm
}
