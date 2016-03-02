use std::error::Error as StdError;
use base::ast::Typed;
use base::types::{TypeEnv, display_type};
use vm::vm::{VM, RootStr};
use vm::api::{IO, Function, WithVM};

use embed_lang::{typecheck_expr, load_file, new_vm};

fn type_of_expr(args: WithVM<RootStr>) -> IO<String> {
    let WithVM { vm, value: args } = args;
    IO::Value(match typecheck_expr(vm, "<repl>", &args, false) {
        Ok((expr, _)) => {
            let ref env = vm.env();
            let symbols = vm.get_symbols();
            format!("{}", display_type(&*symbols, &expr.env_type_of(env)))
        }
        Err(msg) => format!("{}", msg),
    })
}

fn find_type_info(args: WithVM<RootStr>) -> IO<String> {
    let vm = args.vm;
    let args = args.value.trim();
    IO::Value(match vm.find_type_info(args) {
        Ok((generic_args, typ)) => {
            let fmt = || -> Result<String, ::std::fmt::Error> {
                use std::fmt::Write;
                let mut buffer = String::new();
                try!(write!(&mut buffer, "type {}", args));
                for g in generic_args {
                    try!(write!(&mut buffer, " {}", vm.symbol_string(g.id)))
                }
                try!(write!(&mut buffer, " = "));
                match typ {
                    Some(typ) => {
                        let symbols = vm.get_symbols();
                        try!(write!(&mut buffer, "{}", display_type(&*symbols, typ)))
                    }
                    None => try!(write!(&mut buffer, "<abstract>")),
                }
                Ok(buffer)
            };
            fmt().unwrap()
        }
        Err(err) => format!("{}", err),
    })
}

fn f1<A, R>(f: fn(A) -> R) -> fn(A) -> R {
    f
}

fn compile_repl(vm: &VM) -> Result<(), Box<StdError>> {
    try!(vm.define_global("repl_prim",
                          record!(
        type_of_expr => f1(type_of_expr),
        find_type_info => f1(find_type_info)
    )));
    try!(load_file(vm, "std/prelude.hs"));
    try!(load_file(vm, "std/repl.hs"));
    Ok(())
}

#[allow(dead_code)]
pub fn run() -> Result<(), Box<StdError>> {
    let vm = new_vm();
    try!(compile_repl(&vm));
    let mut repl: Function<fn (()) -> IO<()>> = try!(vm.get_global("std.repl"));
    try!(repl.call(()));
    Ok(())
}

#[cfg(test)]
mod tests {
    use embed_lang::new_vm;
    use super::compile_repl;

    #[test]
    fn compile_repl_test() {
        let _ = ::env_logger::init();
        let vm = new_vm();
        compile_repl(&vm).unwrap_or_else(|err| panic!("{}", err));
    }
}
