extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_parser as parser;

use crate::base::{
    kind::{Kind, KindCache},
    mk_ast_arena,
    types::{Field, TypeContext},
};
use crate::check::kindcheck::KindCheck;

use crate::support::{intern, typ, MockEnv, MockIdentEnv};

#[macro_use]
mod support;

#[test]
fn infer_fields() {
    let _ = env_logger::try_init();

    let text = r#"
let f vec = vec.x #Int+ vec.y
f
"#;
    let result = support::typecheck(text);
    assert_req!(
        result.map(|t| t.to_string()),
        Ok("forall a . { x : Int, y : Int | a } -> Int".to_string())
    );
}

#[test]
fn infer_additional_fields() {
    let _ = env_logger::try_init();

    let text = r#"
let f vec = vec.x #Int+ vec.y
f { x = 1, y = 2, z = 3 }
"#;
    let result = support::typecheck(text);
    assert_eq!(result, Ok(typ("Int")));
}

#[test]
fn field_access_on_record_with_type() {
    let _ = env_logger::try_init();

    let text = r#"
type Test = Int
let record = { Test, x = 1, y = "" }
record.y
"#;
    let result = support::typecheck(text);
    assert_eq!(result, Ok(typ("String")));
}

test_check! {
    record_unpack,
    r#"
let f record =
    let { x, y } = record
    y
f { y = 1.0, z = 0, x = 123 }
"#,
    "Float"
}

// Test that arguments that have an applied (`Test a`) type properly unify even if they are not
// explicitly specified. The risk is that `x: Test a` is just resolved to `{ value : a }` which
// then fails to unify if it is unified with only typevariables (`$0 $1`)
#[test]
fn late_merge_with_signature() {
    let _ = env_logger::try_init();

    let text = r#"
type Monad m = { flat_map : forall a b . (a -> m b) -> m a -> m b }
type Test a = { value : a }
let monad : Monad Test = {
    flat_map = \f x -> f x.value
}
monad
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn equality_of_records_with_differing_fields() {
    let _ = env_logger::try_init();

    let text = r#"
let eq x y : a -> a -> () = ()
let f v1 v2 =
    let _ = v1.x
    let _ = v2.y
    eq v1 v2
()
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn associated_types() {
    let _ = env_logger::try_init();

    let text = r#"
type Test = Int
type Test2 = Float
let { Test } = { Test, Test2, x = 2 }
()
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn unused_associated_types_pattern_match() {
    let _ = env_logger::try_init();

    let text = r#"
type Test = Int
let { x } = { Test, x = 2 }
()
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn if_else_different_records() {
    let _ = env_logger::try_init();

    let text = r#"
if True then
    { y = "" }
else
    { x = 1 }
"#;
    let result = support::typecheck(text);
    assert!(result.is_err());
}

#[test]
fn missing_field() {
    let _ = env_logger::try_init();

    let text = r#"
let f vec = vec.x #Int+ vec.y
f { x = 1 }
"#;
    let result = support::typecheck(text);

    assert!(result.is_err());
}

#[test]
fn different_order_of_fields() {
    let _ = env_logger::try_init();

    let text = r#"
if True then
    { x = 1, y = "" }
else
    { y = "", x = 1 }
"#;
    let result = support::typecheck(text);

    // FIXME Change to `ok` when field order no longer matters
    assert!(result.is_err());
}

#[test]
fn different_order_of_fields_does_not_cause_polymorphism() {
    let _ = env_logger::try_init();

    let text = r#"
let record =
    if True then
        { x = 1, y = "" }
    else
        { y = "", x = 1 }
record.z
"#;
    let result = support::typecheck(text);

    assert!(result.is_err());
}

#[test]
fn record_unpack_missing_field() {
    let _ = env_logger::try_init();

    let text = r#"
let f record =
    let { x, y } = record
    y
f { y = 1.0, z = 0 }
"#;
    let result = support::typecheck(text);
    assert!(result.is_err());
}

#[test]
fn missing_associated_types() {
    let _ = env_logger::try_init();

    let text = r#"
type Test = Int
type Test2 = Float
let { Test3 } = { Test, Test2, x = 2 }
()
"#;
    let result = support::typecheck(text);
    assert!(result.is_err());
}

#[test]
fn row_kinds() {
    mk_ast_arena!(arena);
    let mut arena = (*arena).borrow();
    let env = MockEnv::new();
    let mut ident_env = MockIdentEnv::new();
    let mut kindcheck = KindCheck::new(&env, &mut ident_env, KindCache::new());

    let mut typ = arena.empty_row();
    let result = kindcheck.kindcheck_expected(&mut typ, &Kind::row());
    assert_eq!(result, Ok(Kind::row()));

    let mut typ = arena.clone().extend_row(
        arena.alloc_extend(vec![Field::new(intern("x").into(), arena.int())]),
        arena.empty_row(),
    );
    let result = kindcheck.kindcheck_expected(&mut typ, &Kind::row());
    assert_eq!(result, Ok(Kind::row()));
}

#[test]
fn row_kinds_error() {
    mk_ast_arena!(arena);
    let mut arena = (*arena).borrow();
    let env = MockEnv::new();
    let mut ident_env = MockIdentEnv::new();
    let mut kindcheck = KindCheck::new(&env, &mut ident_env, KindCache::new());

    let mut typ = arena.clone().extend_row(
        arena.alloc_extend(vec![Field::new(intern("x").into(), arena.int())]),
        arena.int(),
    );
    let result = kindcheck.kindcheck_expected(&mut typ, &Kind::row());
    assert!(result.is_err());

    let mut typ = arena.clone().extend_row(
        arena.alloc_extend(vec![Field::new(intern("x").into(), arena.empty_row())]),
        arena.empty_row(),
    );
    let result = kindcheck.kindcheck_expected(&mut typ, &Kind::row());
    assert!(result.is_err());
}

#[test]
fn polymorphic_variants() {
    let _ = env_logger::try_init();

    let text = r#"
type AA r = | A Int .. r
type BB r = | B String .. r
if True then
    A 123
else
    B "abc"
"#;
    let result = support::typecheck(text);

    assert_req!(
        result.map(|t| t.to_string()),
        Ok("forall a .\n    | A Int\n    | B String\n    .. a")
    );
}

#[test]
fn closed_row() {
    let _ = env_logger::try_init();
    let text = r#"
type AA = | A Int
type BB r = | B String .. r
if True then
    A 123
else
    B "abc"
"#;
    let result = support::typecheck(text);

    assert_unify_err!(result, Other(MissingFields(..)));
}

#[test]
fn state_effect() {
    let _ = env_logger::try_init();
    let text = r#"
type Eff r a =
    | Pure a
    | Impure : forall x . (r x) ->  (x -> Eff r a) -> Eff r a

type State s r a =
    | Get : State s r s
    | Put : s -> State s r ()
    .. r

let any x = any x

let wrap x : a -> Eff r a = any ()

let inject_rest x : forall e . (.. r) -> [| | r |] a = any ()

let extract_state x : forall s . [| state : State s | r |] a -> State s r a = any ()

let loop state ve : s -> Eff [| state : State s | r |] a -> Eff [| | r |] { state : s, value : a } =
    match ve with
    | Pure value -> wrap { state, value }
    | Impure e f ->
        match extract_state e with
        | Get ->
            loop state (f state)
        | Put state ->
            loop state (f ())
        | rest ->
            Impure (inject_rest rest) (\x -> loop state (f x))

()
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}
