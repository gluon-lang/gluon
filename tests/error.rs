use gluon::{
    base, check::typecheck::TypeError, compiler_pipeline::*, parser, vm::Error as VMError, Error,
    ThreadExt,
};

mod support;

#[test]
fn dont_panic_when_error_span_is_at_eof() {
    let _ = ::env_logger::try_init();
    let vm = support::make_vm();
    let text = r#"abc"#;
    let result = vm.load_script("test", text);
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
    let error = vm.load_script("test", text).unwrap_err();

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
    let result = vm.run_expr::<i32>("test", "error \"some error\"");
    match result {
        Err(Error::VM(VMError::Panic(_, Some(_)))) => (),
        _ => panic!("Expected error with stacktrace {:?}", result),
    }
}

#[test]
fn undefined_infix() {
    let _ = ::env_logger::try_init();

    use crate::base::pos;
    use crate::parser::{InfixError, ParseErrors};

    let expr = r#"
    let (+) x y = 1
    1 + 2
    "#;

    let vm = support::make_vm();

    vm.get_database_mut().implicit_prelude(false);

    let result = expr.reparse_infix(
        &mut vm.module_compiler(&vm.get_database()),
        &vm,
        "test",
        expr,
    );
    match result {
        Err((_, Error::Parse(err))) => {
            let error = parser::Error::Infix(InfixError::UndefinedFixity("+".to_string()));
            let map = vm.get_database().get_filemap("test").unwrap();
            let span = map.span().subspan(9.into(), 12.into());
            assert_eq!(
                err.errors(),
                ParseErrors::from(vec![pos::spanned(span, error)])
            );
        }
        _ => panic!(),
    }
}
