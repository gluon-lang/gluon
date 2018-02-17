extern crate env_logger;
extern crate gluon;

mod support;

use gluon::{Compiler, Error};
use gluon::check::typecheck::TypeError;

#[test]
fn dont_panic_when_error_span_is_at_eof() {
    let _ = ::env_logger::try_init();
    let vm = support::make_vm();
    let text = r#"abc"#;
    let result = Compiler::new()
        .load_script_async(&vm, "test", text)
        .sync_or_error();
    assert!(result.is_err());
}

#[test]
fn dont_miss_errors_in_file_if_import_has_errors() {
    let _ = ::env_logger::try_init();
    let vm = support::make_vm();
    let text = r#"
        let { f } = import! tests.unrelated_type_error
        f x
    "#;
    let error = Compiler::new()
        .load_script_async(&vm, "test", text)
        .sync_or_error()
        .unwrap_err();

    match error {
        Error::Multiple(errors) => {
            let errors_string = errors.to_string();
            assert!(
                errors.into_iter().any(|err| match err {
                    Error::Typecheck(errors) => {
                        let errors: Vec<_> = errors.errors().into();
                        match errors[0].value.error {
                            TypeError::UndefinedVariable(..) => true,
                            _ => false,
                        }
                    }
                    _ => false,
                }),
                errors_string
            );
        }
        error => panic!("{}", error),
    }
}
