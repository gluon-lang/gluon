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

    type Test a r = | Test .. r

    same (convert_variant! (convert_effect! test Test)) Test
    "#,
    "()"
}

test_check_err! {
    not_variant_effect,
    r#"
    let _ = convert_effect! ()
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
    type Test r a = | Test Int .. r
    type Test2 r a = | Test2 .. r

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
    type Test b r a = | Test b .. r

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
    type Test r a = | Test Int .. r
    type Test2 r a = | Test .. r

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
    type Test b r a = | Test b .. r

    let f x : [| test : Test Int | r |] Int -> Test String r Int =
        convert_variant! x
    ()
    "#,
    TypeError::Unification(..)
}

test_check_err! {
    wrong_type_after_conversion2,
    r#"
    type Test r a = | Test a .. r

    let f x : [| test : Test | r |] Int -> Test r String =
        convert_variant! x
    ()
    "#,
    TypeError::Unification(..)
}

test_check_err! {
    effects_remains_in_lift,
    r#"
    type Lift m r a = | Lift (m a) .. r

    type Test r a = | Test a .. r

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

type Alt r a = | Empty .. r

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

test_check! {
    inject_open_variant,
    r#"
type OpenVariant r a = .. r
let inject_rest x : forall e . OpenVariant r a -> [| | r |] a = convert_effect! x
()
    "#,
    "()"
}

test_check! {
    state_effect_get_only,
    r#"
rec
type Arr r a b = a -> Eff r b

type Eff r a =
    | Impure : forall x . r x -> Arr r x a -> Eff r a
in

let any x = any x

type State s r a = | Get : State s r s .. r

let extract_state x : forall s . [| state : State s | r |] a -> State s r a = convert_variant! x

let run_state s eff : forall s . s -> Eff [| state : State s | r |] a -> Eff [| | r |] { state : s, value : a} =
    let loop state ve : s -> Eff [| state : State s | r |] a -> Eff [| | r |] { state : s, value : a } =
        match ve with
        | Impure e f ->
            match extract_state e with
            | Get ->
                loop state (f state)
            | rest -> any ()
    loop s eff

()
    "#,
    "()"
}

test_check! {
    state_effect_get_put,
    r#"
rec
type Arr r a b = a -> Eff r b

type Eff r a =
    | Impure : forall x . r x -> Arr r x a -> Eff r a
in

let any x = any x

type State s r a =
    | Get : State s r s
    | Put : s -> State s r ()
    .. r

let extract_state x : forall s . [| state : State s | r |] a -> State s r a = convert_variant! x

let run_state s eff : forall s . s -> Eff [| state : State s | r |] a -> Eff [| | r |] { state : s, value : a} =
    let loop state ve : s -> Eff [| state : State s | r |] a -> Eff [| | r |] { state : s, value : a } =
        match ve with
        | Impure e f ->
            match extract_state e with
            | Get ->
                loop state (f state)
            | Put state ->
                loop state (f ())
            | rest -> any ()
    loop s eff

()
    "#,
    "()"
}

test_check! {
    st_effect_bug,
    r#"
let any x = any x

rec
type Arr r a b = a -> Eff r b

type Eff r a =
    | Impure : forall x . r x -> Arr r x a -> Eff r a
in

type STRef s a = { __ref : a }
type State s r a =
    | New : forall b . b -> State s r (STRef s b)
    | Write : forall b . b -> STRef s b -> State s r ()
    .. r

let extract_state x : forall s . [| st : State s | r |] a -> State s r a = convert_variant! x

let run_state eff : (forall s . Eff [| st : State s | r |] a) -> Eff [| | r |] a =
    let loop ve : forall s . Eff [| st : State s | r |] a -> _ =
        match ve with
        | Impure e f ->
            match extract_state e with
            | New a ->
                let r : STRef _ _ = { __ref = a }
                loop (f r)
            | Write a r ->
                loop (f ())
            | rest -> any ()
    loop eff

()
    "#,
    "()"
}
