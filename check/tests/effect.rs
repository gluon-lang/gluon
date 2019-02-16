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

test_check_err! {
    effects_remains_in_lift,
    r#"
    type Lift m a = forall r . (| Lift (m a) .. r)

    type Test a = forall r . (| Test a .. r)

    let any x = any x

    let run_lift eff : forall m . [| lift : Lift m |] a -> () = any ()()
    let f x : forall m . [| test : Test, lift : Lift m | r |] Int -> () =
        run_lift x
    ()
    "#,
    TypeError::Unification(..)
}

test_check! {
    alt_effect_generalization_bug,
    r#"
type Eff r a =
    | Pure : a -> Eff r a
    | Impure : forall x . r x -> (x -> Eff r a) -> Eff r a

type Alt a = forall r . (| Empty .. r)

type Option a = | None | Some a

let any x = any x

let wrap a : a -> Eff r a = any ()

let run_alt_inner transform fail eff_1 eff_2 : (a -> b) -> (() -> Eff [| | s |] b) -> Eff [| alt : Alt | r |] a -> Eff [| alt : Alt | r |] a -> Eff [| | s |] b = any ()

let run_alt eff_1 eff_2 : Eff [| alt : Alt | r |] a -> Eff [| alt : Alt | r |] a -> Eff [| | r |] (Option a) =
    let fail _ = wrap None
    run_alt_inner Some fail eff_1 eff_2
()
    "#,
    "()"
}
