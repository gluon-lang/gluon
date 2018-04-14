extern crate gluon;

use gluon::{new_vm, Compiler};

#[test]
fn macro_error_with_line_column_info() {
    let thread = new_vm();
    let mut compiler = Compiler::new();
    let result = compiler.run_expr::<()>(&thread, "test", "import! undefined");
    assert_eq!(
        result
            .unwrap_err()
            .emit_string(compiler.code_map())
            .unwrap(),
        r#"error: Could not find module 'undefined'. Searched `.`.
- <test>:1:9
1 | import! undefined
  |         ^^^^^^^^^
"#
    );
}
