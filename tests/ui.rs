extern crate gluon;

use gluon::{new_vm, Compiler};

#[test]
fn macro_error_with_line_column_info() {
    let thread = new_vm();
    let result = Compiler::new().run_expr::<()>(&thread, "test", "import! undefined");
    assert_eq!(
        result.unwrap_err().to_string(),
        r#"test:Line: 1, Column: 9: Could not find module 'undefined'. Searched `.`.
import! undefined
        ^~~~~~~~~
"#
    );
}
