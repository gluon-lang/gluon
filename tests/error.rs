extern crate env_logger;
extern crate gluon;

mod support;

use gluon::Compiler;

#[test]
fn dont_panic_when_error_span_is_at_eof() {
    let _ = ::env_logger::init();
    let vm = support::make_vm();
    let text = r#"abc"#;
    let result = Compiler::new().load_script(&vm, "test", text);
    assert!(result.is_err());
}
