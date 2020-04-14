use gluon::{new_vm, ThreadExt};

#[test]
fn macro_error_with_line_column_info() {
    let thread = new_vm();
    let result = thread.run_expr::<()>("test", "import! undefined");
    assert_eq!(
        result.unwrap_err().emit_string().unwrap(),
        r#"error: Could not find module 'undefined'. Searched `.`.
- <test>:1:1
  |
1 | import! undefined
  | ^^^^^^^^^^^^^^^^^
  |
"#
    );
}
