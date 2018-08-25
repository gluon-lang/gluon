#[macro_use]
extern crate collect_mac;
extern crate env_logger;

extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_parser as parser;

#[macro_use]

mod support;

#[test]
fn recursive_lambda() {
    let _ = env_logger::try_init();

    let text = r"
let f = \x -> g x
and g = \y -> f y
f
";
    let result = support::typecheck(text);

    assert_req!(result.map(|t| t.to_string()), Ok("forall a a0 . a -> a0"));
}

#[test]
fn use_recursive_function_in_record() {
    let _ = env_logger::try_init();

    let text = r"
let f =
    { g }
and g = \y -> f.g y
f
";
    let result = support::typecheck(text);

    assert_req!(
        result.map(|t| t.to_string()),
        Ok("forall a a0 . { g : a -> a0 }")
    );
}

#[test]
fn cant_call_recursive_value_app() {
    let _ = env_logger::try_init();

    let text = r"
let f =
    let z = g 1
    { g }
and g = \y -> f.g y
f
";
    let result = support::typecheck(text);

    assert_err!(result, RecursionCheck(..));
}

#[test]
fn cant_call_recursive_value_infix() {
    let _ = env_logger::try_init();

    let text = r"
let f =
    let z = g 1
    { g }
and g = \y -> f.g y
f
";
    let result = support::typecheck(text);

    assert_err!(result, RecursionCheck(..));
}

#[test]
fn impossible_to_refer_directly_to_self() {
    let _ = env_logger::try_init();

    let text = r"
let f = f
f
";
    let result = support::typecheck(text);

    assert_err!(result, RecursionCheck(..));
}

#[test]
fn impossible_to_refer_to_self_through_let_binding() {
    let _ = env_logger::try_init();

    let text = r"
let f =
    let x = f
    x
f
";
    let result = support::typecheck(text);

    assert_err!(result, RecursionCheck(..));
}

test_check!(
    can_refer_to_self_through_lambda,
    r"
let f =
    let x = \_ ->
        let y = f
        ()
    { x }
f
",
    "{ x : forall a . a -> () }"
);

#[test]
fn impossible_to_use_self_in_match() {
    let _ = env_logger::try_init();

    let text = r"
let f =
    match { f } with
    | { f } -> ()
f
";
    let result = support::typecheck(text);

    assert_err!(result, RecursionCheck(..));
}
