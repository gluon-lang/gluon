use gluon::{new_vm, ThreadExt};

#[test]
fn macro_error_with_line_column_info() {
    let thread = new_vm();
    let result = thread.run_expr::<()>("test", "import! undefined");
    insta::assert_snapshot!(result.unwrap_err().emit_string().unwrap());
}
