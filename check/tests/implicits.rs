#[macro_use]
extern crate collect_mac;
extern crate env_logger;
#[macro_use]
extern crate pretty_assertions;

extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_parser as parser;

use base::ast;
use base::types::{Field, Type};

#[macro_use]
#[allow(unused_macros)]
mod support;

#[test]
fn single_implicit_arg() {
    let _ = ::env_logger::init();
    let text = r#"

let f x y: [Int] -> Int -> Int = x
/// @implicit
let i = 123
f 42
"#;
    let result = support::typecheck(text);

    assert_eq!(result, Ok(Type::int()));
}

#[test]
fn multiple_implicit_args() {
    let _ = ::env_logger::init();
    let text = r#"

let f x y z w: [Int] -> [String] -> String -> Int -> Int = x
/// @implicit
let i = 123
/// @implicit
let x = "abc"
f x 42
"#;
    let result = support::typecheck(text);

    assert_eq!(result, Ok(Type::int()));
}

#[test]
fn just_a_implicit_arg() {
    let _ = ::env_logger::init();
    let text = r#"

let f x: [Int] -> Int = x
/// @implicit
let i = 123
f
"#;
    let result = support::typecheck(text);

    assert_eq!(result, Ok(Type::int()));
}

#[test]
fn function_implicit_arg() {
    let _ = ::env_logger::init();
    let text = r#"

let f eq l r: [a -> a -> Bool] -> a -> a -> Bool = eq l r
/// @implicit
let eq_int l r : Int -> Int -> Bool = True
/// @implicit
let eq_string l r : String -> String -> Bool = True
f 1 2
f "" ""
()
"#;
    let result = support::typecheck(text);

    assert_req!(result, Ok(Type::unit()));
}

#[test]
fn infix_implicit_arg() {
    let _ = ::env_logger::init();
    let text = r#"

let (==) eq l r: [a -> a -> Bool] -> a -> a -> Bool = eq l r
/// @implicit
let eq_int l r : Int -> Int -> Bool = True
/// @implicit
let eq_string l r : String -> String -> Bool = True
"" == ""
"#;
    let (mut expr, _result) = support::typecheck_expr(text);

    loop {
        match expr.value {
            ast::Expr::LetBindings(_, body) => {
                expr = *body;
            }
            _ => match expr.value {
                ast::Expr::App { ref args, .. } if args.len() == 3 => {
                    break;
                }
                _ => assert!(false),
            },
        }
    }
}

#[test]
fn implicit_from_record_field() {
    let _ = ::env_logger::init();
    let text = r#"

let f eq l r: [a -> a -> Bool] -> a -> a -> Bool = eq l r
/// @implicit
let eq_int l r : Int -> Int -> Bool = True
let eq_string =
    /// @implicit
    let eq l r : String -> String -> Bool = True
    { eq }
f 1 2
f "" ""
()
"#;
    let result = support::typecheck(text);

    assert_req!(result, Ok(Type::unit()));
}

#[test]
fn implicit_on_type() {
    let _ = ::env_logger::init();
    let text = r#"
/// @implicit
type Test = | Test
let f x y: [a] -> a -> a = x
let i = Test
f Test
"#;
    let result = support::typecheck(text);

    let test = support::alias(
        "Test",
        &[],
        Type::variant(vec![
            Field::new(support::intern("Test"), support::typ("Test")),
        ]),
    );
    assert_eq!(result, Ok(test));
}
