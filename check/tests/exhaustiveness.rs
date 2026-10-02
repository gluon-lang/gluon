extern crate gluon_base as base;
extern crate gluon_check as check;

#[macro_use]
mod support;

#[test]
fn non_exhaustive_enum() {
    let _ = env_logger::try_init();
    let text = r#"
type Color = | Red | Green | Blue
let f c =
    match c with
    | Red -> 1
    | Green -> 2
f Blue
"#;
    let result = support::typecheck(text);
    assert_err!(result, NonExhaustiveMatch(..));
}

#[test]
fn exhaustive_enum() {
    let _ = env_logger::try_init();
    let text = r#"
type Color = | Red | Green | Blue
let f c =
    match c with
    | Red -> 1
    | Green -> 2
    | Blue -> 3
f Red
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "expected pass, got {:?}", result);
}

#[test]
fn wildcard_exhaustive() {
    let _ = env_logger::try_init();
    let text = r#"
type Color = | Red | Green | Blue
let f c =
    match c with
    | Red -> 1
    | _ -> 2
f Red
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "expected pass, got {:?}", result);
}

#[test]
fn nested_non_exhaustive() {
    let _ = env_logger::try_init();
    let text = r#"
type Option a = | None | Some a
let f o =
    match o with
    | Some (Some x) -> x
    | None -> 0
f None
"#;
    let result = support::typecheck(text);
    assert_err!(result, NonExhaustiveMatch(..));
}

#[test]
fn nested_exhaustive() {
    let _ = env_logger::try_init();
    let text = r#"
type Option a = | None | Some a
let f o =
    match o with
    | Some (Some x) -> x
    | Some None -> 1
    | None -> 0
f None
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "expected pass, got {:?}", result);
}

#[test]
fn tuple_non_exhaustive() {
    let _ = env_logger::try_init();
    let text = r#"
type Bool2 = | T | F
let f p =
    match p with
    | (T, x) -> 1
f (T, T)
"#;
    let result = support::typecheck(text);
    assert_err!(result, NonExhaustiveMatch(..));
}

#[test]
fn redundant_arm() {
    let _ = env_logger::try_init();
    let text = r#"
type Color = | Red | Green | Blue
let f c =
    match c with
    | Red -> 1
    | Green -> 2
    | Blue -> 3
    | Red -> 4
f Red
"#;
    let result = support::typecheck(text);
    assert_err!(result, UnreachableMatchArm);
}

#[test]
fn non_exhaustive_literal() {
    let _ = env_logger::try_init();
    let text = r#"
let f n =
    match n with
    | 1 -> "one"
    | 2 -> "two"
f 3
"#;
    let result = support::typecheck(text);
    assert_err!(result, NonExhaustiveMatch(..));
}

#[test]
fn literal_wildcard_exhaustive() {
    let _ = env_logger::try_init();
    let text = r#"
let f n =
    match n with
    | 1 -> "one"
    | _ -> "other"
f 3
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "expected pass, got {:?}", result);
}

#[test]
fn record_non_exhaustive() {
    let _ = env_logger::try_init();
    let text = r#"
type Flag = | On | Off
let f r =
    match r with
    | { flag = On } -> 1
f { flag = On }
"#;
    let result = support::typecheck(text);
    assert_err!(result, NonExhaustiveMatch(..));
}

#[test]
fn record_exhaustive() {
    let _ = env_logger::try_init();
    let text = r#"
type Flag = | On | Off
let f r =
    match r with
    | { flag = On } -> 1
    | { flag = Off } -> 2
f { flag = On }
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "expected pass, got {:?}", result);
}

#[test]
fn variable_exhaustive() {
    let _ = env_logger::try_init();
    let text = r#"
type Color = | Red | Green | Blue
let f c =
    match c with
    | Red -> 1
    | other -> 2
f Red
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "expected pass, got {:?}", result);
}

#[test]
fn wildcard_after_every_constructor_is_unreachable() {
    let _ = env_logger::try_init();
    let text = r#"
type Color = | Red | Green | Blue
let f c =
    match c with
    | Red -> 1
    | Green -> 2
    | Blue -> 3
    | _ -> 4
f Red
"#;
    let result = support::typecheck(text);
    assert_err!(result, UnreachableMatchArm);
}

#[test]
fn record_literal_with_polymorphic_field_exhaustive() {
    let _ = env_logger::try_init();
    let text = r#"
type Test a = | A a | B
match { x = B } with
| { x = A y } -> y
| { x = B } -> 100
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "expected pass, got {:?}", result);
}

#[test]
fn record_literal_with_polymorphic_field_non_exhaustive() {
    let _ = env_logger::try_init();
    let text = r#"
type Test a = | A a | B
match { x = B } with
| { x = A y } -> y
"#;
    let result = support::typecheck(text);
    assert_err!(result, NonExhaustiveMatch(..));
}
