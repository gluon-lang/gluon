
extern crate env_logger;
extern crate gluon;

use gluon::{new_vm, Compiler, Thread};
use gluon::vm::internal::Value;
use gluon::vm::api::{Hole, OpaqueValue, IO};

#[macro_use]
mod support;

use support::*;

#[test]
fn read_file() {
    let _ = ::env_logger::init();

    let thread = new_vm();
    let text = r#"
        let prelude = import! std.prelude
        let array = import! std.array
        let { assert }  = import! std.test
        let io = import! std.io
        let { wrap } = io.applicative
        let { (>>=) } = prelude.make_Monad io.monad

        io.open_file "Cargo.toml" >>= \file ->
            io.read_file file 9 >>= \bytes ->
            assert (array.len bytes == 9)
            assert (array.index bytes 0 #Byte== 91b) // [
            assert (array.index bytes 1 #Byte== 112b) // p
            wrap (array.index bytes 8)
        "#;
    let result = Compiler::new()
        .run_io(true)
        .run_expr_async::<IO<u8>>(&thread, "<top>", text)
        .sync_or_error();

    match result {
        Ok((IO::Value(value), _)) => assert_eq!(value, b']'),
        Ok((IO::Exception(err), _)) => assert!(false, "{}", err),
        Err(err) => assert!(false, "{}", err),
    }
}

test_expr!{ no_io_eval,
r#"
let { error } = import! std.prim
let io = import! std.io.prim
let x = io.flat_map (\x -> error "NOOOOOOOO") (io.println "1")
in { x }
"#
}

test_expr!{ io_print,
r#"
let io = import! std.io
io.print "123"
"#
}

#[test]
fn run_expr_int() {
    let _ = ::env_logger::init();

    let text = r#"
        let io = import! std.io
        io.run_expr "123"
    "#;
    let mut vm = make_vm();
    let (result, _) = Compiler::new()
        .run_io(true)
        .run_expr_async::<IO<String>>(&mut vm, "<top>", text)
        .sync_or_error()
        .unwrap();
    match result {
        IO::Value(result) => {
            let expected = "123 : Int";
            assert_eq!(result, expected);
        }
        IO::Exception(err) => panic!("{}", err),
    }
}

test_expr!{ io run_expr_io,
r#"
let io = import! std.io.prim
io.flat_map (\x -> io.wrap 100)
            (io.run_expr "
                let io = import! \"std/io.glu\"
                io.print \"123\"
            ")
"#,
100i32
}


#[test]
fn dont_execute_io_in_run_expr_async() {
    let _ = ::env_logger::init();
    let vm = make_vm();
    let expr = r#"
let prelude  = import! std.prelude
let io = import! std.io
let { wrap } = io.applicative
wrap 123
"#;
    let value = Compiler::new()
        .run_expr_async::<OpaqueValue<&Thread, Hole>>(&vm, "example", expr)
        .sync_or_error()
        .unwrap_or_else(|err| panic!("{}", err));
    assert!(
        value.0.get_ref() != Value::Int(123),
        "Unexpected {:?}",
        value.0
    );
}
