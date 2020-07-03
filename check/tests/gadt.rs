extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_parser as parser;

#[macro_use]
mod support;

use crate::check::typecheck::TypeError;

test_check! {
    basic1,
    r#"
    type Test a =
        | Int : Int -> Test Int

    Int 1
    "#,
    "test.Test Int"
}

test_check_err! {
    basic_error,
    r#"
    type Test a =
        | Int : Int -> Test Int

    Int ""
    "#,
    TypeError::Unification(..)
}

test_check! {
    basic2,
    r#"
    type Test a =
        | Int : Int -> Test Int

    let f x : Test a -> Int =
        match x with
        | Int x -> x

    ()
    "#,
    "()"
}

test_check! {
    basic3,
    r#"
    type Test a =
        | Int : Int -> Test Int

    let f x : Test a -> a =
        match x with
        | Int x -> x

    ()
    "#,
    "()"
}

test_check! {
    different_types_concrete,
    r#"
    type Test a =
        | Int : Int -> Test Int
        | Float : Float -> Test Float

    let f x : Test a -> a =
        match x with
        | Int x -> x
        | Float x -> x

    ()
    "#,
    "()"
}

test_check! {
    different_types_a,
    r#"
    type Test a =
        | Int : Int -> Test Int
        | A : a -> Test a

    let f x : Test a -> a =
        match x with
        | Int x -> x
        | A x -> x

    ()
    "#,
    "()"
}

test_check_err! {
    different_types_error,
    r#"
    type Test a =
        | Int : Int -> Test Int
        | A : Test a

    let f x y : Test a -> b -> a =
        match x with
        | Int x -> x
        | A -> y

    ()
    "#,
    Unification(..)
}

test_check_err! {
    using_parameter_with_specific_type_errors,
    r#"
    type Test a =
        | Test : a -> Test Int

    let f x : Test a -> a =
        match x with
        | Test x -> x

    ()
    "#,
    Unification(..)
}

test_check_err! {
    invalid_gadt_return1,
    r#"
    type Test2 a = a
    type Test a =
        | Test : a -> Test2 Int

    ()
    "#,
    TypeConstructorReturnsWrongType { .. }
}

test_check_err! {
    invalid_gadt_return2,
    r#"
    type Test2 a = a
    type Test a =
        | Test : a -> (Int -> Int)

    ()
    "#,
    TypeConstructorReturnsWrongType { .. }
}

test_check! {
    match_on_none,
    r#"
type Option a = | None | Some a
match None with
| Some y -> y
| None -> 1
    "#,
    "Int"
}
