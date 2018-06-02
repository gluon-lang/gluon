extern crate env_logger;

extern crate gluon;
#[macro_use]
extern crate gluon_codegen;

use std::io::{self, BufRead};

use gluon::vm::api::{FunctionRef, OpaqueValue};
use gluon::{new_vm, Compiler, RootedThread};

#[derive(VmType)]
#[gluon(vm_type = "examples.lisp.lisp.Expr")]
struct Expr;
type OpaqueExpr = OpaqueValue<RootedThread, Expr>;

#[derive(VmType)]
#[gluon(vm_type = "examples.lisp.lisp.LispState")]
struct LispState;
type OpaqueLispState = OpaqueValue<RootedThread, LispState>;

fn main() {
    if let Err(err) = main_() {
        eprintln!("{}", err);
    }
}

fn main_() -> gluon::Result<()> {
    env_logger::init();

    let thread = new_vm();
    Compiler::new().load_file(&thread, "examples/lisp/lisp.glu")?;

    let mut eval: FunctionRef<
        fn(String, OpaqueLispState) -> Result<(OpaqueExpr, OpaqueLispState), String>,
    > = thread.get_global("examples.lisp.lisp.eval_env_string")?;

    let mut show: FunctionRef<fn(OpaqueExpr) -> String> =
        thread.get_global("examples.lisp.lisp.show.show")?;

    let mut env: OpaqueLispState = thread.get_global("examples.lisp.lisp.default_env")?;

    let stdin = io::stdin();
    for line in stdin.lock().lines() {
        let line = line?;
        match eval.call(line, env.clone())? {
            Ok((msg, new_env)) => {
                println!("{}", show.call(msg.clone())?);
                env = new_env;
            }
            Err(err) => {
                eprintln!("{}", err);
            }
        }
    }
    Ok(())
}
