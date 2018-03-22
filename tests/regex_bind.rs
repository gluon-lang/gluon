#![cfg(feature = "regex")]
extern crate env_logger;
extern crate gluon;

use gluon::{new_vm, Compiler};

#[test]
fn regex_match() {
    let _ = ::env_logger::try_init();

    let thread = new_vm();
    let text = r#"
        let regex = import! std.regex
        let { (|>) } = import! std.function
        let { not } = import! std.bool
        let { unwrap_ok } = import! std.result
        let { assert }  = import! std.test

        let match_a = regex.new "a" |> unwrap_ok
        assert (regex.is_match match_a "a")
        assert (not (regex.is_match match_a "b"))
        let match_hello = regex.new "hello, .*" |> unwrap_ok
        regex.is_match match_hello "hello, world"
        "#;
    let result = Compiler::new()
        .run_expr_async::<bool>(&thread, "<top>", text)
        .sync_or_error();

    assert!(result.unwrap_or_else(|err| panic!("{}", err)).0);
}

#[test]
fn regex_error() {
    let _ = ::env_logger::try_init();

    let thread = new_vm();
    let text = r#"
        let regex = import! std.regex
        let { (|>) } = import! std.function
        let { unwrap_err } = import! std.result

        regex.new ")" |> unwrap_err |> regex.error_to_string
        "#;
    let result = Compiler::new()
        .run_expr_async::<String>(&thread, "<top>", text)
        .sync_or_error();

    assert_eq!(
        result.unwrap_or_else(|err| panic!("{}", err)).0,
        "regex parse error:\n    )\n    ^\nerror: unopened group"
    );
}
