extern crate env_logger;
extern crate gluon;
extern crate tokio;

use gluon::vm::api::{Hole, OpaqueValue, ValueRef, IO};
use gluon::{new_vm, Compiler, Thread};

#[macro_use]
mod support;

use support::*;

#[test]
fn read_file() {
    let _ = ::env_logger::try_init();

    let thread = new_vm();
    let text = r#"
        let prelude = import! std.prelude
        let array = import! std.array
        let { assert }  = import! std.test
        let io @ { ? } = import! std.io
        let { wrap } = io.applicative
        let { flat_map, (>>=) } = import! std.monad

        do file = io.open_file "Cargo.toml"
        do bytes = io.read_file file 9

        assert (array.len bytes == 9)
        assert (array.index bytes 0 #Byte== 91b) // [
        assert (array.index bytes 1 #Byte== 112b) // p

        wrap (array.index bytes 8)
        "#;
    let result = Compiler::new()
        .run_io(true)
        .run_expr::<IO<u8>>(&thread, "<top>", text);

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
    let _ = ::env_logger::try_init();

    let text = r#"
        let io = import! std.io
        let { flat_map } = io.monad
        do result = io.run_expr "123"
        io.applicative.wrap result.value
    "#;
    let mut vm = make_vm();
    let (result, _) = Compiler::new()
        .run_io(true)
        .run_expr_async::<IO<String>>(&mut vm, "<top>", text)
        .sync_or_error()
        .unwrap();
    match result {
        IO::Value(result) => {
            let expected = "123";
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
    let _ = ::env_logger::try_init();
    let vm = make_vm();
    let expr = r#"
let prelude  = import! std.prelude
let io = import! std.io
let { wrap } = io.applicative
wrap 123
"#;
    let value = Compiler::new()
        .run_expr::<OpaqueValue<&Thread, Hole>>(&vm, "example", expr)
        .unwrap_or_else(|err| panic!("{}", err));
    assert!(
        value.0.get_ref() != ValueRef::Int(123),
        "Unexpected {:?}",
        value.0
    );
}

#[test]
fn spawn_on_twice() {
    let _ = ::env_logger::try_init();

    let text = r#"
        let { applicative = { wrap }, monad = { flat_map } } = import! std.io
        let thread = import! std.thread

        do child = thread.new_thread ()
        do action = thread.spawn_on child (\_ -> wrap "abc")
        action
    "#;

    let mut runtime = self::tokio::runtime::Runtime::new().unwrap();
    let vm = make_vm();
    let (result, _) = runtime
        .block_on(
            Compiler::new()
                .run_io(true)
                .run_expr_async::<IO<String>>(&vm, "<top>", text),
        )
        .unwrap_or_else(|err| panic!("{}", err));
    match result {
        IO::Value(result) => {
            assert_eq!(result, "abc");
        }
        IO::Exception(err) => panic!("{}", err),
    }

    let (result, _) = runtime
        .block_on(
            Compiler::new()
                .run_io(true)
                .run_expr_async::<IO<String>>(&vm, "<top>", text),
        )
        .unwrap_or_else(|err| panic!("{}", err));
    match result {
        IO::Value(result) => {
            assert_eq!(result, "abc");
        }
        IO::Exception(err) => panic!("{}", err),
    }
}

#[test]
fn spawn_on_runexpr() {
    let _ = ::env_logger::try_init();

    let text = r#"
        let io@{ applicative = applicative@{ wrap }, monad = { flat_map }, ? } = import! std.io
        let thread = import! std.thread

        do child = thread.new_thread ()
        do action = thread.spawn_on child (\_ -> io.run_expr "123")
        do x = action
        do io.println x.value
        wrap x.value
    "#;

    let mut runtime = self::tokio::runtime::Runtime::new().unwrap();
    let vm = make_vm();
    let (result, _) = runtime
        .block_on(
            Compiler::new()
                .run_io(true)
                .run_expr_async::<IO<String>>(&vm, "<top>", text),
        )
        .unwrap_or_else(|err| panic!("{}", err));
    match result {
        IO::Value(result) => {
            assert_eq!(result, "123");
        }
        IO::Exception(err) => panic!("{}", err),
    }
}

#[test]
fn spawn_on_do_action_twice() {
    let _ = ::env_logger::try_init();

    let text = r#"
        let { ? } = import! std.io
        let { ref, (<-), load } = import! std.reference
        let thread = import! std.thread
        let { wrap } = import! std.applicative
        let { join } = import! std.monad

        let counter = ref 0 

        do child = thread.new_thread ()
        let action = thread.spawn_on child (\_ ->
                counter <- (load counter + 1)
                wrap ())
        do join action
        do join action
        wrap (load counter)
    "#;

    let mut runtime = self::tokio::runtime::Runtime::new().unwrap();
    let vm = make_vm();
    let (result, _) = runtime
        .block_on(
            Compiler::new()
                .run_io(true)
                .run_expr_async::<IO<i32>>(&vm, "<top>", text),
        )
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(result, IO::Value(2));
}

#[test]
fn spawn_on_force_action_twice() {
    let _ = ::env_logger::try_init();

    let text = r#"
        let { ? } = import! std.io
        let { ref, (<-), load } = import! std.reference
        let thread = import! std.thread
        let { wrap } = import! std.applicative

        let counter = ref 0 

        do child = thread.new_thread ()
        do action = thread.spawn_on child (\_ ->
                counter <- (load counter + 1)
                wrap ())
        do action
        do action
        wrap (load counter)
    "#;

    let mut runtime = self::tokio::runtime::Runtime::new().unwrap();
    let vm = make_vm();
    let (result, _) = runtime
        .block_on(
            Compiler::new()
                .run_io(true)
                .run_expr_async::<IO<i32>>(&vm, "<top>", text),
        )
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(result, IO::Value(1));
}

#[test]
fn spawn_on_runexpr_in_catch() {
    let _ = ::env_logger::try_init();

    let text = r#"
        let prelude = import! std.prelude
        let io@{ applicative, monad, ? } = import! std.io
        let { Applicative, (*>), wrap } = import! std.applicative
        let { flat_map, (>>=) } = import! std.monad
        let thread = import! std.thread

        let action =
            do eval_thread = thread.new_thread ()
            let f _ = io.run_expr "123"
            do a = thread.spawn_on eval_thread f
            do result = a
            wrap result.value
        (io.catch action wrap >>= io.println) *> wrap "123"
    "#;

    let mut runtime = self::tokio::runtime::Runtime::new().unwrap();
    let vm = make_vm();
    let (result, _) = runtime
        .block_on(
            Compiler::new()
                .run_io(true)
                .run_expr_async::<IO<String>>(&vm, "<top>", text),
        )
        .unwrap_or_else(|err| panic!("{}", err));
    match result {
        IO::Value(result) => {
            assert_eq!(result, "123");
        }
        IO::Exception(err) => panic!("{}", err),
    }

    let (result, _) = runtime
        .block_on(
            Compiler::new()
                .run_io(true)
                .run_expr_async::<IO<String>>(&vm, "<top>", text),
        )
        .unwrap_or_else(|err| panic!("{}", err));
    match result {
        IO::Value(result) => {
            assert_eq!(result, "123");
        }
        IO::Exception(err) => panic!("{}", err),
    }
}
