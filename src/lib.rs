//! # Example
//!
//! ```rust
//! # extern crate env_logger;
//! # extern crate embed_lang;
//!
//! use embed_lang::{new_vm, run_expr};
//!
//! # fn main() {
//! # let _ = ::env_logger::init();
//!
//! let text = r#"
//! // `type` is used to declare a new type.
//! // In this case we declare `Eq` to be a record with a single field (`==`) which is a function
//! // which takes two arguments of the same type and returns a boolean
//! type Eq a = { (==) : a -> a -> Bool }
//! // `let` declares new variables.
//! let id x = x
//!
//! let factorial n =
//!         if n < 2
//!         then 1
//!         else n * factorial (n - 1)
//!
//! let list_module =
//!         // Declare a new type which only exists in the current scope
//!         type List a = | Cons a (List a) | Nil
//!         let map f xs =
//!                 case xs of
//!                     | Cons y ys -> Cons (f y) (map f ys)
//!                     | Nil -> Nil
//!         let eq eq_a: Eq a -> Eq (List a) =
//!                 let (==) l r =
//!                     case l of
//!                         | Cons la lxs ->
//!                             (case r of
//!                                 | Cons ra rxs -> eq_a.(==) la ra && lxs == rxs
//!                                 | Nil -> False)
//!                         | Nil ->
//!                             (case r of
//!                                 | Cons _ _ -> False
//!                                 | Nil -> True)
//!                 { (==) }
//!         {
//!             // Since `List` is local we export it so its constructors can be used
//!             // outside the current scope
//!             List,
//!             eq,
//!             map
//!         }
//!
//! // Bring the `List` type and its constructors into scope
//! let { List, eq = list_Eq } = list_module
//! // Create `==` for `List Int`
//! let { (==) }: Eq (List Int) = list_Eq { (==) }
//! if Cons 1 Nil == Nil then
//!     error "This branch is not executed"
//! else
//!     io.print "Hello world!"
//! "#;
//!
//! let vm = new_vm();
//! match run_expr(&vm, "example", text) {
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
extern crate vm as vm_mod;

mod io;
mod crates {
    extern crate base;
    extern crate parser;
    extern crate check;
}

pub use crates::base;
pub use crates::parser;
pub use crates::check;
pub use vm_mod as vm;

pub mod import;

pub use vm::vm::VM;



use base::ast;
use base::types::TcType;
use base::symbol::{Name, NameBuf, Symbol};
use std::result::Result as StdResult;
use std::string::String as StdString;
use std::error::Error as StdError;
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
        Typecheck(err: ::base::error::InFile<::check::typecheck::TypeError<StdString>>) {
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

fn include_implicit_prelude(vm: &VM, name: &str, expr: &mut ast::LExpr<ast::TcIdent<Symbol>>) {
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
    let prelude_expr = parse_expr(vm, "", prelude_import).unwrap();
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

fn compile_script(vm: &VM,
                  filename: &str,
                  expr: &ast::LExpr<ast::TcIdent<Symbol>>)
                  -> CompiledFunction {
    use base::symbol::SymbolModule;
    use vm::compiler::Compiler;
    debug!("Compile `{}`", filename);
    let mut function = {
        let env = vm.env();
        let mut interner = vm.interner.borrow_mut();
        let mut gc = vm.gc.borrow_mut();
        let mut symbols = vm.get_mut_symbols();
        let name = Name::new(filename);
        let name = NameBuf::from(name.module());
        let symbols = SymbolModule::new(StdString::from(name.as_ref()), &mut symbols);
        let mut compiler = Compiler::new(&env, &mut interner, &mut gc, symbols);
        compiler.compile_expr(&expr)
    };
    function.id = vm.symbol(filename);
    function
}

/// Compiles `input` and if it is successful runs the resulting code and stores the resulting value
/// in the global variable named by running `filename_to_module` on `filename`.
///
/// If at any point the function fails the resulting error is returned and nothing is added to the
/// VM.
pub fn load_script(vm: &VM, filename: &str, input: &str) -> Result<()> {
    load_script2(vm, filename, input, true)
}

pub fn load_script2(vm: &VM, filename: &str, input: &str, implicit_prelude: bool) -> Result<()> {
    let (expr, typ) = try!(typecheck_expr(vm, filename, input, implicit_prelude));
    let function = compile_script(vm, filename, &expr);
    let function = vm.new_function(function);
    let closure = {
        let stack = vm.current_frame();
        vm.alloc(&stack.stack, ClosureDataDef(function, &[]))
    };
    let value = try!(vm.call_module(&typ, closure));
    try!(vm.set_global(function.name.clone(), typ, value));
    Ok(())
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

/// Loads `filename` and compiles and runs its input by calling `load_script`
pub fn load_file(vm: &VM, filename: &str) -> Result<()> {
    use std::fs::File;
    use std::io::Read;
    let mut file = try!(File::open(filename));
    let mut buffer = ::std::string::String::new();
    try!(file.read_to_string(&mut buffer));
    drop(file);
    let name = filename_to_module(filename);
    load_script(vm, &name, &buffer)
}

pub fn parse_expr(vm: &VM,
                  file: &str,
                  input: &str)
                  -> StdResult<ast::LExpr<ast::TcIdent<Symbol>>, ::parser::Error> {
    use base::symbol::SymbolModule;
    let mut symbols = vm.get_mut_symbols();
    Ok(try!(::parser::parse_tc(&mut SymbolModule::new(file.into(), &mut symbols), input)))
}

pub fn typecheck_expr<'a>(vm: &VM<'a>,
                          file: &str,
                          expr_str: &str,
                          implicit_prelude: bool)
                          -> Result<(ast::LExpr<ast::TcIdent<Symbol>>, TcType)> {
    use check::typecheck::Typecheck;
    use base::error;
    let mut expr = try!(parse_expr(vm, file, expr_str));
    if implicit_prelude {
        include_implicit_prelude(vm, file, &mut expr);
    }
    try!(vm.get_macros().run(vm, &mut expr));
    let env = vm.env();
    let mut symbols = vm.get_mut_symbols();
    let mut tc = Typecheck::new(file.into(), &mut symbols, &env);
    let typ = try!(tc.typecheck_expr(&mut expr)
                     .map_err(|err| error::InFile::new(StdString::from(file), expr_str, err)));
    Ok((expr, typ))
}

/// Compiles and runs the expression in `expr_str`. If successful the value from running the
/// expression is returned
pub fn run_expr<'a, 'vm>(vm: &'vm VM<'a>,
                         name: &str,
                         expr_str: &str)
                         -> Result<RootedValue<'a, 'vm>> {
    run_expr2(vm, name, expr_str, true)
}

pub fn run_expr2<'a, 'vm>(vm: &'vm VM<'a>,
                      name: &str,
                      expr_str: &str,
                      implicit_prelude: bool)
                      -> Result<RootedValue<'a, 'vm>> {
    let (expr, typ) = try!(typecheck_expr(vm, name, expr_str, implicit_prelude));
    let mut function = compile_script(vm, name, &expr);
    function.id = vm.symbol(name);
    let function = vm.new_function(function);
    let closure = {
        let stack = vm.current_frame();
        vm.alloc(&stack.stack, ClosureDataDef(function, &[]))
    };
    let value = try!(vm.call_module(&typ, closure));
    Ok(vm.root_value(value))
}

/// Creates a new virtual machine with support for importing other modules and with all primitives
/// loaded.
pub fn new_vm<'a>() -> VM<'a> {
    let vm = VM::new();
    vm.get_macros().insert(vm.symbol("import"), ::import::Import::new());
    ::vm::primitives::load(&vm).expect("Loaded primitives library");
    ::io::load(&vm).expect("Loaded IO library");
    vm
}
