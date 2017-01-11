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
    let result = Compiler::new().run_expr::<bool>(&thread, "<top>", text);

    assert!(result.unwrap().0);
}

