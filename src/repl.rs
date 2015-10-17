use std::error::Error as StdError;
use base::ast;
use check::typecheck::{Type, TypeEnv};
use check::Typed;
use vm::vm::{VM, RootStr, Status, typecheck_expr, load_file};
use vm::api::{VMFunction, IO};

fn type_of_expr(vm: &VM) -> Status {
    let closure: &Fn(_) -> _ = &|args: RootStr| -> IO<String> {
        IO::Value(match typecheck_expr(vm, &args) {
            Ok((expr, infos)) => {
                let ref env = (vm.env(), infos);
                format!("{}", expr.env_type_of(env))
            }
            Err(msg) => format!("{}", msg)
        })
    };
    closure.unpack_and_call(vm)
}

fn find_type_info(vm: &VM) -> Status {
    let closure: &Fn(RootStr) -> IO<String> = &|args| {
        let args = args.trim();
        IO::Value(match vm.env().find_type_info(&vm.intern(args)) {
            Some((generic_args, typ)) => {
                let fmt = || -> Result<String, ::std::fmt::Error> {
                    use std::fmt::Write;
                    let mut buffer = String::new();
                    try!(write!(&mut buffer, "type {}", args));
                    for g in generic_args {
                        try!(write!(&mut buffer, " {}", g))
                    }
                    try!(write!(&mut buffer, " = "));
                    match typ {
                        Some(typ) => try!(write!(&mut buffer, "{}", typ)),
                        None => try!(write!(&mut buffer, "<abstract>"))
                    }
                    Ok(buffer)
                };
                fmt().unwrap()
            }
            None => format!("'{}' is not a type", args)
        })
    };
    closure.unpack_and_call(vm)
}

#[allow(dead_code)]
pub fn run() -> Result<(), Box<StdError>> {
    let vm = VM::new();
    let io = |t| ast::ASTType::from(ast::type_con(vm.intern("IO"), vec![t]));
    try!(vm.extern_function_io("type_of_expr", 2, Type::function(vec![Type::string()], io(Type::string())), Box::new(type_of_expr)));
    try!(vm.extern_function_io("find_type_info", 2, Type::function(vec![Type::string()], io(Type::string())), Box::new(find_type_info)));
    try!(load_file(&vm, "std/prelude.hs"));
    try!(load_file(&vm, "std/map.hs"));
    try!(load_file(&vm, "std/repl.hs"));
    Ok(())
}
