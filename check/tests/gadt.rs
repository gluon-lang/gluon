#[macro_use]
extern crate collect_mac;
extern crate env_logger;
#[macro_use]
extern crate quick_error;

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
