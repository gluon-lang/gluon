use std::error::Error as StdError;
use base::ast::Typed;
use base::types::Kind;
use vm::api::{IO, Function, WithVM};
use vm::thread::{Thread, RootStr};

use gluon::{Compiler, new_vm};

fn type_of_expr(args: WithVM<RootStr>) -> IO<Result<String, String>> {
    let WithVM { vm, value: args } = args;
    let mut compiler = Compiler::new().implicit_prelude(false);
    IO::Value(match compiler.typecheck_expr(vm, "<repl>", &args) {
        Ok((expr, _)) => {
            let env = vm.get_env();
            Ok(format!("{}", expr.env_type_of(&*env)))
        }
        Err(msg) => Err(format!("{}", msg)),
    })
}

fn find_kind(args: WithVM<RootStr>) -> IO<Result<String, String>> {
    let vm = args.vm;
    let args = args.value.trim();
    IO::Value(match vm.find_type_info(args) {
        Ok(ref alias) => {
            let kind = alias.args.iter().rev().fold(Kind::star(), |acc, arg| {
                Kind::function(arg.kind.clone(), acc)
            });
            Ok(format!("{}", kind))
        }
        Err(err) => Err(format!("{}", err)),
    })
}

fn find_info(args: WithVM<RootStr>) -> IO<Result<String, String>> {
    use std::fmt::Write;
    let vm = args.vm;
    let args = args.value.trim();
    let env = vm.get_env();
    let mut buffer = String::new();
    match env.find_type_info(args) {
        Ok(alias) => {
            // Found a type alias
            let mut fmt = || -> Result<(), ::std::fmt::Error> {
                try!(write!(&mut buffer, "type {}", args));
                for g in &alias.args {
                    try!(write!(&mut buffer, " {}", g.id))
                }
                try!(write!(&mut buffer, " = "));
                match alias.typ {
                    Some(ref typ) => try!(write!(&mut buffer, "{}", typ)),
                    None => try!(write!(&mut buffer, "<abstract>")),
                }
                Ok(())
            };
            fmt().unwrap();
        }
        Err(err) => {
            // Try to find a value at `args` to print its type and documentation comment (if any)
            match env.get_binding(args) {
                Ok((_, typ)) => {
                    write!(&mut buffer, "{}: {}", args, typ).unwrap();
                }
                Err(_) => return IO::Value(Err(format!("{}", err))),
            }
        }
    }
    let maybe_comment = env.get_metadata(args)
                           .ok()
                           .and_then(|metadata| metadata.comment.as_ref());
    if let Some(comment) = maybe_comment {
        for line in comment.lines() {
            write!(&mut buffer, "\n/// {}", line).unwrap();
        }
    }
    IO::Value(Ok(buffer))
}

fn compile_repl(vm: &Thread) -> Result<(), Box<StdError + Send + Sync>> {
    fn input(s: &str) -> IO<Option<String>> {
        IO::Value(::linenoise::input(s))
    }
    try!(vm.define_global("repl_prim",
                          record!(
        type_of_expr => primitive!(1 type_of_expr),
        find_info => primitive!(1 find_info),
        find_kind => primitive!(1 find_kind),
        input => primitive!(1 input)
    )));
    let mut compiler = Compiler::new();
    try!(compiler.load_file(vm, "std/prelude.hs"));
    try!(compiler.load_file(vm, "std/repl.hs"));
    Ok(())
}

#[allow(dead_code)]
pub fn run() -> Result<(), Box<StdError + Send + Sync>> {
    let vm = new_vm();
    try!(compile_repl(&vm));
    let mut repl: Function<&Thread, fn(()) -> IO<()>> = try!(vm.get_global("std.repl"));
    try!(repl.call(()));
    Ok(())
}

#[cfg(test)]
mod tests {
    use gluon::new_vm;
    use super::compile_repl;
    use vm::api::{IO, FunctionRef};

    #[test]
    fn compile_repl_test() {
        let _ = ::env_logger::init();
        let vm = new_vm();
        compile_repl(&vm).unwrap_or_else(|err| panic!("{}", err));
        let repl: Result<FunctionRef<fn(()) -> IO<()>>, _> = vm.get_global("std.repl");
        assert!(repl.is_ok());
    }

    type QueryFn = fn(&'static str) -> IO<Result<String, String>>;

    #[test]
    fn type_of_expr() {
        let _ = ::env_logger::init();
        let vm = new_vm();
        compile_repl(&vm).unwrap_or_else(|err| panic!("{}", err));
        let mut type_of: FunctionRef<QueryFn> = vm.get_global("repl_prim.type_of_expr").unwrap();
        assert!(type_of.call("std.prelude.Option").is_ok());
    }

    #[test]
    fn find_kind() {
        let _ = ::env_logger::init();
        let vm = new_vm();
        compile_repl(&vm).unwrap_or_else(|err| panic!("{}", err));
        let mut find_kind: FunctionRef<QueryFn> = vm.get_global("repl_prim.find_kind").unwrap();
        assert_eq!(find_kind.call("std.prelude.Option"), Ok(IO::Value(Ok("* -> *".into()))));
    }

    #[test]
    fn find_info() {
        let _ = ::env_logger::init();
        let vm = new_vm();
        compile_repl(&vm).unwrap_or_else(|err| panic!("{}", err));
        let mut find_info: FunctionRef<QueryFn> = vm.get_global("repl_prim.find_info").unwrap();
        match find_info.call("std.prelude.Option") {
            Ok(IO::Value(Ok(_))) => (),
            x => assert!(false, "{:?}", x),
        }
        match find_info.call("std.prelude.id") {
            Ok(IO::Value(Ok(_))) => (),
            x => assert!(false, "{:?}", x),
        }
        match find_info.call("float") {
            Ok(IO::Value(Ok(_))) => (),
            x => assert!(false, "{:?}", x),
        }
    }
}
