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

use check::typecheck::TypeError;

test_check! {
    convert,
    r#"
    let any x = any x
    let same : a -> a -> () = any ()

    type Test a = forall r . (| Test .. r)

    same (convert_variant! (convert_effect! test Test)) Test
    "#,
    "()"
}

test_check_err! {
    not_variant_effect,
    r#"
    convert_effect! ()
    convert_effect! 1
    "#,
    TypeError::Message(_),
    TypeError::Message(_)
}

test_check_err! {
    not_effect,
    r#"
    convert_variant! ()
    "#,
    TypeError::Message(_)
}

test_check! {
    empty_effect,
    r#"

    let f x : [| | r |] Int -> (.. r) =
        convert_variant! x
    ()
    "#,
    "()"
}

test_check! {
    different_variant_with_different_name_succeeds,
    r#"
    type Test a = forall r . (| Test Int .. r)
    type Test2 a = forall r . (| Test2 .. r)

    let f x : [| test : Test, test2 : Test2 | r |] Int -> () =
        let _ = convert_variant! x
        ()
    ()
    "#,
    "()"
}

test_check_err! {
    same_variant_with_different_arg_errors,
    r#"
    type Test b a = forall r . (| Test b .. r)

    let f x : [| test : Test Int, test2 : Test String | r |] Int -> () =
        let _ = convert_variant! x
        ()
    ()
    "#,
    TypeError::Unification(..)
}

test_check_err! {
    different_variant_with_same_name_errors,
    r#"
    type Test a = forall r . (| Test Int .. r)
    type Test2 a = forall r . (| Test .. r)

    let f x : [| test : Test, test2 : Test2 | r |] Int -> () =
        let _ = convert_variant! x
        ()
    ()
    "#,
    TypeError::Unification(..)
}

test_check_err! {
    wrong_type_after_conversion1,
    r#"
    type Test b a = forall r . (| Test b .. r)

    let f x : [| test : Test Int | r |] Int -> Test String Int =
        convert_variant! x
    ()
    "#,
    TypeError::Unification(..)
}

test_check_err! {
    wrong_type_after_conversion2,
    r#"
    type Test a = forall r . (| Test a .. r)

    let f x : [| test : Test | r |] Int -> Test String =
        convert_variant! x
    ()
    "#,
    TypeError::Unification(..)
}
