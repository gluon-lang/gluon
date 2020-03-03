extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_parser as parser;

#[macro_use]

mod support;

#[test]
fn non_recursive() {
    let _ = env_logger::try_init();

    let text = r"
let x = 1
let x = x
x
";
    let result = support::typecheck(text);

    assert_req!(result.map(|t| t.to_string()), Ok("Int"));
}

#[test]
fn recursive_lambda() {
    let _ = env_logger::try_init();

    let text = r"
rec
let f = \x -> g x
let g = \y -> f y
f
";
    let result = support::typecheck(text);

    assert_req!(result.map(|t| t.to_string()), Ok("forall a a0 . a -> a0"));
}

#[test]
fn use_recursive_function_in_record() {
    let _ = env_logger::try_init();

    let text = r"
rec
let f =
    { g }
let g = \y -> f.g y
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
rec
let f =
    let z = g 1
    { g }
let g = \y -> f.g y
f
";
    let result = support::typecheck(text);

    assert_err!(result, RecursionCheck(..));
}

#[test]
fn cant_call_function_with_uninitialized_value() {
    let _ = env_logger::try_init();

    let text = r"
rec
let g =
    let h x = f
    h ()
let f = {}
f
";
    let result = support::typecheck(text);

    assert_err!(result, RecursionCheck(..));
}

#[test]
fn cant_call_recursive_value_infix() {
    let _ = env_logger::try_init();

    let text = r"
#[infix(left, 0)]
let (+++) x y = ()

rec
let g = f +++ ()
let f = {}
f
";
    let result = support::typecheck(text);

    assert_err!(result, RecursionCheck(..));
}

#[test]
fn impossible_to_refer_directly_to_self() {
    let _ = env_logger::try_init();

    let text = r"
rec let f = f
f
";
    let result = support::typecheck(text);

    assert_err!(result, RecursionCheck(..));
}

#[test]
fn impossible_to_refer_to_self_through_let_binding() {
    let _ = env_logger::try_init();

    let text = r"
rec let f =
    let x = f
    x
f
";
    let result = support::typecheck(text);

    assert_err!(result, RecursionCheck(..));
}

#[test]
fn impossible_to_refer_to_self_through_let_binding_nested() {
    let _ = env_logger::try_init();

    let text = r"
let g y =
    rec let f =
        let x = f
        x
    f
g
";
    let result = support::typecheck(text);

    assert_err!(result, RecursionCheck(..));
}

test_check!(
    can_refer_to_self_through_lambda,
    r"
rec let f =
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
rec let f =
    match { f } with
    | { f } -> ()
f
";
    let result = support::typecheck(text);

    assert_err!(result, RecursionCheck(..));
}

test_check!(
    can_use_uninitialized_value_in_let_lambda,
    r"
rec
let g =
    let h x = f
    h
let f = {}
in
g
",
    "forall a . a -> ()"
);

test_check!(
    can_use_uninitialized_value_in_lambda,
    r"
rec let g = \x ->
    let z = g x
    1
g
",
    "forall a . a -> Int"
);

test_check!(
    recursive_variant,
    r"
type List a = | Nil | Cons a (List a)
rec let ones = Cons 1 ones
ones
",
    "test.List Int"
);

test_check!(
    dont_leak_recursive_nature_of_binding,
    r"
type List a = | Nil | Cons a (List a)
rec let ones = Cons 1 ones
match ones with
| _ -> 1
",
    "Int"
);

test_check!(
    function_can_use_later_binding,
    r"
rec
let f x =
    f y
let y = { }
f
",
    "forall a . () -> a"
);

#[test]
fn lambda_with_uninitialized_value_cant_be_called() {
    let _ = env_logger::try_init();

    let text = r"
rec
let x =
    let f = \y -> x
    let z = f ()
    { }
x
";
    let result = support::typecheck(text);

    assert_err!(result, RecursionCheck(..));
}

#[test]
fn nested_lambda_with_uninitialized_value_cant_be_called() {
    let _ = env_logger::try_init();

    let text = r"
rec
let x =
    let f = \z -> \y -> x
    let z = f ()
    { }
x
";
    let result = support::typecheck(text);

    assert_err!(result, RecursionCheck(..));
}

test_check!(
    example,
    r"
rec
let value1 =
    let f x = value2.f x #Int+ 1
    { f }
let value2 =
    let f x = value1.f x #Int+ 2
    { f }
in value1
",
    "forall a . { f : a -> Int }"
);
