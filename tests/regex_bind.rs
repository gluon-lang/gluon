#![cfg(feature = "regex")]
extern crate gluon;
extern crate env_logger;

use gluon::{Compiler, new_vm};

#[test]
fn regex_match() {
    let _ = ::env_logger::init();

    let thread = new_vm();
    let text = r#"
        let { unwrap_ok, (|>) } = import "std/prelude.glu"
        let { assert } = import "std/test.glu"

        let match_a = regex.new "a" |> unwrap_ok
        assert (regex.is_match match_a "a")
        assert (not (regex.is_match match_a "b"))
        let match_hello = regex.new "hello, .*" |> unwrap_ok
        regex.is_match match_hello "hello, world"
        "#;
    let result = Compiler::new().run_expr::<bool>(&thread, "<top>", text).sync_or_error();

    assert!(result.unwrap().0);
}

#[test]
fn regex_error() {
    let _ = ::env_logger::init();

    let thread = new_vm();
    let text = r#"
        let { unwrap_err, (|>) } = import "std/prelude.glu"

        regex.new ")" |> unwrap_err |> regex.error_to_string
        "#;
    let result = Compiler::new().run_expr::<String>(&thread, "<top>", text).sync_or_error();

    assert_eq!(result.unwrap().0,
               "Error parsing regex near \')\' at character offset 0: Unopened parenthesis.");
}
