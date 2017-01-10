extern crate gluon;
extern crate env_logger;

use gluon::{Compiler, new_vm};

#[test]
fn regex_match() {
    let _ = ::env_logger::init();

    let thread = new_vm();
    let text = r#"
        let prelude = import "std/prelude.glu"
        let { assert } = import "std/test.glu"

        assert (regex.matches "a" "a")
        assert (not (regex.matches "a" "b"))
        assert (regex.matches ".*" "a")
        regex.matches "hello, .*" "hello, world"
        "#;
    let result = Compiler::new().run_expr::<bool>(&thread, "<top>", text);

    assert!(result.unwrap().0);
}

