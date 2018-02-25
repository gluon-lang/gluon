#[macro_use]
extern crate collect_mac;
extern crate env_logger;

extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_parser as parser;

#[macro_use]
mod support;

test_check! {
    project_type,
    r#"
    type Test = Int
    let module = { Test }
    let x : module.Test = 1
    x
    "#,
    "test.Test"
}

test_check! {
    project_type_with_params,
    r#"
    type Test a = | Test a
    let module = { Test }
    let x : module.Test Int = Test 1
    x
    "#,
    "test.Test Int"
}

test_check! {
    project_type_in_alias,
    r#"
    type Test = Int
    let module = { Test }
    type Test2 = {
        test : module.Test
    }
    let x : Test2 = { test = 1 }
    x
    "#,
    "test.Test2"
}

#[test]
fn undefined_field_in_type_projection() {
    let _ = ::env_logger::try_init();
    let text = r#"
let module = { }
let x : module.Test = 1
x
"#;
    let result = support::typecheck(text);
    assert_err!(result, UndefinedField(..));
}

#[test]
fn undefined_variable_in_type_projection() {
    let _ = ::env_logger::try_init();
    let text = r#"
let x : module.Test = 1
x
"#;
    let result = support::typecheck(text);
    assert_err!(result, UndefinedVariable(..));
}

#[test]
fn type_mismatch_in_type_projection() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Test = String
let module = { Test }
let x : module.Test = 1
x
"#;
    let result = support::typecheck(text);
    assert_unify_err!(result, TypeMismatch(..));
}

#[test]
fn type_mismatch_in_type_projection_with_params() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Test a = | Test a
let module = { Test }
let x : module.Test String = Test 1
x
"#;
    let result = support::typecheck(text);
    assert_unify_err!(result, TypeMismatch(..));
}
