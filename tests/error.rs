extern crate env_logger;
extern crate gluon;

use gluon::{base, parser};

mod support;

use gluon::{Compiler, Error};
use gluon::compiler_pipeline::*;
use gluon::check::typecheck::TypeError;
use gluon::vm::Error as VMError;

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

#[test]
fn panics_contain_stacktrace() {
    let _ = ::env_logger::try_init();

    let vm = support::make_vm();
    let result = Compiler::new().run_expr::<i32>(&vm, "test", "error \"some error\"");
    match result {
        Err(Error::VM(VMError::Panic(_, Some(_)))) => (),
        _ => panic!("Expected error with stacktrace {:?}", result),
    }
}

#[test]
fn undefined_infix() {
    let _ = ::env_logger::try_init();

    use parser::{InfixError, ParseErrors};
    use base::pos::{self, BytePos};

    let expr = r#"
    let (+) x y = 1
    1 + 2
    "#;

    let vm = support::make_vm();
    let result = expr.reparse_infix(
        &mut Compiler::new().implicit_prelude(false),
        &vm,
        "test",
        expr,
    );
    match result {
        Err((_, Error::Parse(err))) => {
            let error = parser::Error::Infix(InfixError::UndefinedFixity("+".to_string()));
            let span = pos::span(BytePos::from(10), BytePos::from(13));
            assert_eq!(
                err.errors(),
                ParseErrors::from(vec![pos::spanned(span, error)])
            );
        }
        _ => panic!(),
    }
}
