extern crate env_logger;

extern crate gluon;
#[macro_use]
extern crate gluon_codegen;

use std::io::{self, BufRead};

use gluon::{
    new_vm,
    vm::api::{FunctionRef, OpaqueValue},
    RootedThread, ThreadExt,
};

#[derive(VmType)]
#[gluon(vm_type = "examples.lisp.lisp.Expr")]
struct ExprMarker;
type Expr = OpaqueValue<RootedThread, ExprMarker>;

#[derive(VmType)]
#[gluon(vm_type = "examples.lisp.lisp.LispState")]
struct LispStateMarker;
type LispState = OpaqueValue<RootedThread, LispStateMarker>;

fn main() {
    if let Err(err) = main_() {
        eprintln!("{}", err);
    }
}

fn main_() -> gluon::Result<()> {
    env_logger::init();

    let thread = new_vm();
    thread.load_file("examples/lisp/lisp.glu")?;

    let mut eval: FunctionRef<fn(String, LispState) -> Result<(Expr, LispState), String>> =
        thread.get_global("examples.lisp.lisp.eval_env_string")?;

    let mut show: FunctionRef<fn(Expr) -> String> =
        thread.get_global("examples.lisp.lisp.show.show")?;

    let mut env: LispState = thread.get_global("examples.lisp.lisp.default_env")?;

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

#[cfg(test)]
mod tests {
    use super::*;

    use gluon::Error;

    fn eval_lisp(expr: &str) -> Result<String, Error> {
        let thread = new_vm();
        thread.load_file("examples/lisp/lisp.glu")?;

        let mut eval: FunctionRef<fn(String, LispState) -> Result<(Expr, LispState), String>> =
            thread.get_global("examples.lisp.lisp.eval_env_string")?;

        let mut show: FunctionRef<fn(Expr) -> String> =
            thread.get_global("examples.lisp.lisp.show.show")?;

        let env: LispState = thread.get_global("examples.lisp.lisp.default_env")?;

        let (msg, _) = eval.call(expr.to_string(), env.clone())??;
        Ok(show.call(msg.clone())?)
    }

    #[test]
    fn basic() {
        assert_eq!(eval_lisp("(+ 1 2 3)").unwrap(), "6");
    }
}
