use std::fs;

use tempfile::NamedTempFile;

use gluon::{
    new_vm,
    vm::api::{Hole, OpaqueValue, OwnedFunction, ValueRef, IO},
    Thread, ThreadExt,
};

use tokio::runtime::Runtime;

#[macro_use]
mod support;

use crate::support::*;

#[test]
fn read_file() {
    let _ = ::env_logger::try_init();

    let thread = new_vm();
    thread.get_database_mut().run_io(true);
    let text = r#"
        let prelude = import! std.prelude
        let array = import! std.array
        let { assert }  = import! std.test
        let io @ { ? } = import! std.io
        let { wrap } = io.applicative
        let { ? } = import! std.byte
        let { unwrap } = import! std.option
        let { flat_map, (>>=) } = import! std.monad

        do file = io.open_file "Cargo.toml"
        do bytes = io.read_file file 9
        let bytes = unwrap bytes

        let _ = assert (array.len bytes == 9)
        let _ = assert (array.index bytes 0 == 91b) // [
        let _ = assert (array.index bytes 1 == 112b) // p

        wrap (array.index bytes 8)
        "#;
    let result = thread.run_expr::<IO<u8>>("<top>", text);

    match result {
        Ok((IO::Value(value), _)) => assert_eq!(value, b']'),
        Ok((IO::Exception(err), _)) => assert!(false, "{}", err),
        Err(err) => assert!(false, "{}", err),
    }
}

#[test]
fn write_and_flush_file() {
    let _ = ::env_logger::try_init();

    let file = NamedTempFile::new().unwrap();

    let thread = new_vm();
    thread.get_database_mut().run_io(true);
    let text = r#"
        let { assert } = import! std.test
        let { OpenOptions, open_file_with, write_slice_file, flush_file, ? } = import! std.io

        \path ->
            do file = open_file_with path [Write]
            do bytes_written = write_slice_file file [1b, 2b, 3b, 4b] 0 4
            let _ = assert (bytes_written == 4)
            flush_file file
    "#;

    let (mut test, _) = thread
        .run_expr::<OwnedFunction<fn(String) -> IO<()>>>("<top>", &text)
        .unwrap_or_else(|err| panic!("{}", err));

    test.call(file.path().to_str().unwrap().to_owned())
        .unwrap_or_else(|err| panic!("{}", err));

    let content = fs::read(file.path()).unwrap();
    assert_eq!(content, vec![1, 2, 3, 4]);
}

test_expr! { no_io_eval,
r#"
let { error } = import! std.prim
let io = import! std.io
let x = io.flat_map (\x -> error "NOOOOOOOO") (io.println "1")
in { x }
"#
}

test_expr! { io_print,
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
    let vm = make_vm();
    vm.get_database_mut().run_io(true);
    let (result, _) = vm.run_expr::<IO<String>>("<top>", text).unwrap();
    match result {
        IO::Value(result) => {
            let expected = "123";
            assert_eq!(result, expected);
        }
        IO::Exception(err) => panic!("{}", err),
    }
}

test_expr! { io run_expr_io,
r#"
let io = import! std.io
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
    let value = vm
        .run_expr::<OpaqueValue<&Thread, Hole>>("example", expr)
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
        do action = thread.spawn_on child (wrap "abc")
        action
    "#;

    let mut runtime = Runtime::new().unwrap();
    let vm = make_vm();
    vm.get_database_mut().run_io(true);
    let (result, _) = runtime
        .block_on(vm.run_expr_async::<IO<String>>("<top>", text))
        .unwrap_or_else(|err| panic!("{}", err));
    match result {
        IO::Value(result) => {
            assert_eq!(result, "abc");
        }
        IO::Exception(err) => panic!("{}", err),
    }

    let (result, _) = runtime
        .block_on(vm.run_expr_async::<IO<String>>("<top>", text))
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
        do action = thread.spawn_on child (io.run_expr "123")
        do x = action
        seq io.println x.value
        wrap x.value
    "#;

    let mut runtime = Runtime::new().unwrap();
    let vm = make_vm();
    vm.get_database_mut().run_io(true);
    let (result, _) = runtime
        .block_on(vm.run_expr_async::<IO<String>>("<top>", text))
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
        let { ref, modify, load } = import! std.reference
        let thread = import! std.thread
        let { wrap } = import! std.applicative
        let { join } = import! std.monad

        do counter = ref 0

        do child = thread.new_thread ()
        let action = thread.spawn_on child (modify counter (\x -> x + 1))
        seq join action
        seq join action
        load counter
    "#;

    let mut runtime = Runtime::new().unwrap();
    let vm = make_vm();
    vm.get_database_mut().run_io(true);
    let (result, _) = runtime
        .block_on(vm.run_expr_async::<IO<i32>>("<top>", text))
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(result, IO::Value(2));
}

#[test]
fn spawn_on_force_action_twice() {
    let _ = ::env_logger::try_init();

    let text = r#"
        let { ? } = import! std.io
        let { ref, modify, load } = import! std.reference
        let thread = import! std.thread
        let { wrap } = import! std.applicative

        do counter = ref 0

        do child = thread.new_thread ()
        do action = thread.spawn_on child (modify counter (\x -> x + 1))
        seq action
        seq action
        load counter
    "#;

    let mut runtime = Runtime::new().unwrap();
    let vm = make_vm();
    vm.get_database_mut().run_io(true);
    let (result, _) = runtime
        .block_on(vm.run_expr_async::<IO<i32>>("<top>", text))
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(result, IO::Value(1));
}

#[test]
fn spawn_on_runexpr_in_catch() {
    let _ = ::env_logger::try_init();

    let text = r#"
        let prelude = import! std.prelude
        let io @ { ? } = import! std.io
        let { Applicative, (*>), wrap } = import! std.applicative
        let { flat_map, (>>=) } = import! std.monad
        let thread = import! std.thread

        let action =
            do eval_thread = thread.new_thread ()
            do a = thread.spawn_on eval_thread (io.run_expr "123")
            do result = a
            wrap result.value
        (io.catch action wrap >>= io.println) *> wrap "123"
    "#;

    let mut runtime = Runtime::new().unwrap();
    let vm = make_vm();
    vm.get_database_mut().run_io(true);
    let (result, _) = runtime
        .block_on(vm.run_expr_async::<IO<String>>("<top>", text))
        .unwrap_or_else(|err| panic!("{}", err));
    match result {
        IO::Value(result) => {
            assert_eq!(result, "123");
        }
        IO::Exception(err) => panic!("{}", err),
    }

    let (result, _) = runtime
        .block_on(vm.run_expr_async::<IO<String>>("<top>", text))
        .unwrap_or_else(|err| panic!("{}", err));
    match result {
        IO::Value(result) => {
            assert_eq!(result, "123");
        }
        IO::Exception(err) => panic!("{}", err),
    }
}

#[test]
fn io_error_in_catch1() {
    let _ = ::env_logger::try_init();

    let expr = r#"
        let io = import! std.io
        io.catch (io.read_file_to_string "doesnotexist") (\_ -> io.applicative.wrap "error")
    "#;

    let vm = make_vm();

    vm.get_database_mut().implicit_prelude(false).run_io(true);

    let (result, _) = vm
        .run_expr::<IO<String>>("<top>", expr)
        .unwrap_or_else(|err| panic!("{}", err));
    let expected = IO::Value("error".to_string());

    assert_eq!(result, expected);
}

#[test]
fn io_error_in_catch2() {
    let _ = ::env_logger::try_init();

    let expr = r#"
        let { (*>) } = import! std.applicative
        let io @ { ? } = import! std.io
        io.catch (io.println "asd" *> io.read_file_to_string "doesnotexist") (\_ -> io.applicative.wrap "error")
    "#;

    let vm = make_vm();

    vm.get_database_mut().implicit_prelude(false).run_io(true);

    let (result, _) = vm
        .run_expr::<IO<String>>("<top>", expr)
        .unwrap_or_else(|err| panic!("{}", err));
    let expected = IO::Value("error".to_string());

    assert_eq!(result, expected);
}

#[test]
fn io_error_in_catch3() {
    let _ = ::env_logger::try_init();

    let expr = r#"
        let io @ { ? } = import! std.io
        let { flat_map } = import! std.monad
        do _ = io.catch (io.read_file_to_string "doesnotexist") (\_ -> io.applicative.wrap "error")
        io.catch (io.read_file_to_string "doesnotexist") (\_ -> io.applicative.wrap "error2")
    "#;

    let vm = make_vm();

    vm.get_database_mut().implicit_prelude(false).run_io(true);

    let (result, _) = vm
        .run_expr::<IO<String>>("<top>", expr)
        .unwrap_or_else(|err| panic!("{}", err));
    let expected = IO::Value("error2".to_string());

    assert_eq!(result, expected);
}
