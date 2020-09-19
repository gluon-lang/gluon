#[macro_use]
extern crate collect_mac;

#[macro_use]
extern crate pretty_assertions;

extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_completion as completion;
extern crate gluon_parser as parser;

use crate::base::{
    ast::Sp,
    kind::{ArcKind, Kind},
    pos::{BytePos, Span},
    types::{ArcType, Field, Type},
};

use either::Either;

#[allow(unused)]
mod support;
use crate::support::{intern, loc, typ, MockEnv};

fn find_span_type(s: &str, pos: BytePos) -> Result<(Span<BytePos>, Either<ArcKind, ArcType>), ()> {
    let env = MockEnv::new();

    let (expr, result) = support::typecheck_expr(s);
    let expr = expr.expr();
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let extract = (completion::SpanAt, completion::TypeAt { env: &env });
    completion::completion(extract, expr.span, &expr, pos)
}

fn find_span_type2(s: &str) -> Result<(Span<BytePos>, Either<ArcKind, ArcType>), ()> {
    let pos = {
        let marker = s.find("// ^").expect("Position marker") + "// ".len();
        let previous_line_end = s[..marker].rfind('\n').expect("Previous line");
        let previous_line_start = s[..previous_line_end].rfind('\n').expect("Previous line");
        previous_line_start + (marker - previous_line_end)
    };
    find_span_type(s, BytePos::from(pos as u32 + 1))
}

fn find_all_symbols(s: &str, pos: BytePos) -> Result<(String, Vec<Span<BytePos>>), ()> {
    let (expr, result) = support::typecheck_expr(s);
    let expr = expr.expr();
    assert!(result.is_ok(), "{}", result.unwrap_err());

    completion::find_all_symbols(expr.span, &expr, pos)
}

fn find_kind2(s: &str) -> Result<ArcKind, ()> {
    find_span_type2(s).map(|t| {
        t.1.as_ref()
            .left()
            .cloned()
            .unwrap_or_else(|| panic!("Expected kind, got: {}", t.1))
    })
}

fn find_kind(s: &str, pos: BytePos) -> Result<ArcKind, ()> {
    find_span_type(s, pos).map(|t| t.1.left().expect("Kind"))
}

fn find_type(s: &str, pos: BytePos) -> Result<ArcType, ()> {
    find_span_type(s, pos).map(|t| t.1.right().expect("Type"))
}

fn find_type_loc(s: &str, line: usize, column: usize) -> Result<ArcType, ()> {
    let pos = loc(s, line, column);
    find_span_type(s, pos).map(|t| t.1.right().expect("Type"))
}

fn symbol(s: &str, pos: BytePos) -> Result<String, ()> {
    let (expr, result) = support::typecheck_expr(s);
    let expr = expr.expr();
    assert!(result.is_ok(), "{}", result.unwrap_err());

    completion::symbol(expr.span, &expr, pos).map(|s| s.declared_name().to_string())
}

#[test]
fn identifier() {
    let env = MockEnv::new();

    let (expr, result) = support::typecheck_expr("let abc = 1 in abc");
    let expr = expr.expr();
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let result = completion::find(&env, expr.span, &expr, BytePos::from(15));
    let expected = Ok(Either::Right(typ("Int")));
    assert_eq!(result, expected);

    let result = completion::find(&env, expr.span, &expr, BytePos::from(16));
    let expected = Ok(Either::Right(typ("Int")));
    assert_eq!(result, expected);

    let result = completion::find(&env, expr.span, &expr, BytePos::from(17));
    let expected = Ok(Either::Right(typ("Int")));
    assert_eq!(result, expected);

    let result = completion::find(&env, expr.span, &expr, BytePos::from(18));
    let expected = Ok(Either::Right(typ("Int")));
    assert_eq!(result, expected);
}

#[test]
fn literal_string() {
    let result = find_type(r#" "asd" "#, BytePos::from(1));
    let expected = Ok(typ("String"));

    assert_eq!(result, expected);
}

#[test]
fn in_let() {
    let result = find_type(
        r#"
rec
let f x = 1
let g x = "asd"
1
"#,
        BytePos::from(29),
    );
    let expected = Ok(typ("String"));

    assert_eq!(result, expected);
}

#[test]
fn let_in_let() {
    let result = find_type(
        r#"
let f =
    let g y =
        123
    g
f
"#,
        BytePos::from(33),
    );
    let expected = Ok(typ("Int"));

    assert_eq!(result, expected);
}

#[test]
fn function_app() {
    let _ = env_logger::try_init();

    let text = r#"
let f x = f x
1
"#;
    let result = find_type(text, loc(text, 1, 10));
    let expected = Ok("a -> a0".to_string());

    assert_eq!(result.map(|typ| typ.to_string()), expected);
}

#[test]
fn binop() {
    let _ = env_logger::try_init();

    let env = MockEnv::new();

    let text = r#"
#[infix(left, 4)]
let (++) l r =
    let _ = l #Int+ 1
    let _ = r #Float+ 1.0
    l
1 ++ 2.0
"#;
    let (expr, result) = support::typecheck_expr(text);
    let expr = expr.expr();
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let result = completion::find(&env, expr.span, &expr, loc(text, 6, 3));
    let expected = Ok(Either::Right(Type::function(
        vec![typ("Int"), typ("Float")],
        typ("Int"),
    )));
    assert_eq!(result, expected);

    let result = completion::find(&env, expr.span, &expr, loc(text, 6, 1));
    let expected = Ok(Either::Right(typ("Int")));
    assert_eq!(result, expected);

    let result = completion::find(&env, expr.span, &expr, loc(text, 6, 7));
    let expected = Ok(Either::Right(typ("Float")));
    assert_eq!(result, expected);
}

#[test]
fn field_access() {
    let _ = env_logger::try_init();

    let typ_env = MockEnv::new();

    let (expr, result) = support::typecheck_expr(
        r#"
let r = { x = 1 }
r.x
"#,
    );
    let expr = expr.expr();
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let result = completion::find(&typ_env, expr.span, &expr, BytePos::from(19));
    let expected = Ok(Either::Right(Type::record(
        vec![],
        vec![Field::new(intern("x"), typ("Int"))],
    )));
    assert_eq!(result.map(|x| x.map_right(support::close_record)), expected);

    let result = completion::find(&typ_env, expr.span, &expr, BytePos::from(22));
    let expected = Ok(Either::Right(typ("Int")));
    assert_eq!(result, expected);
}

#[test]
fn find_do_binding_type() {
    let _ = env_logger::try_init();

    let result = find_type_loc(
        r#"
type Option a = | None | Some a
let flat_map f x =
    match x with
    | Some y -> f y
    | None -> None

do x = Some 1
None
"#,
        7,
        4,
    );
    let expected = Ok("Int".to_string());

    assert_eq!(result.map(|typ| typ.to_string()), expected);
}

#[test]
fn parens_expr() {
    let _ = env_logger::try_init();

    let text = r#"
let id x = x
(id 1)
"#;
    let (expr, result) = support::typecheck_expr(text);
    let expr = expr.expr();
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let env = MockEnv::new();
    let extract = (completion::SpanAt, completion::TypeAt { env: &env });

    let result = completion::completion(extract, expr.span, &expr, loc(text, 2, 0));
    let expected = Ok((
        Span::new(loc(text, 2, 0), loc(text, 2, 6)),
        Either::Right(Type::int()),
    ));
    assert_eq!(result, expected);

    let result = completion::completion(extract, expr.span, &expr, loc(text, 2, 2));
    let expected = Ok((
        Span::new(loc(text, 2, 1), loc(text, 2, 3)),
        Either::Right(Type::function(vec![Type::int()], Type::int())),
    ));
    assert_eq!(result, expected);
}

#[test]
fn suggest_pattern_at_record_brace() {
    let _ = env_logger::try_init();

    let text = r#"
let { x } = { x = 1 }
x
"#;

    let result = find_span_type(text, loc(text, 1, 5));
    let expected = Ok((
        Span::new(loc(text, 1, 4), loc(text, 1, 9)),
        Either::Right(Type::record(
            vec![],
            vec![Field {
                name: intern("x"),
                typ: Type::int(),
            }],
        )),
    ));
    assert_eq!(result, expected);
}

#[test]
fn in_record() {
    let _ = env_logger::try_init();

    let result = find_type(
        r#"
{
    test = 123,
    s = "asd"
}
"#,
        BytePos::from(15),
    );
    let expected = Ok(typ("Int"));

    assert_eq!(result, expected);
}

#[test]
fn record_constructor_field() {
    let _ = env_logger::try_init();

    let result = find_type(r#"{ test = 123 }"#, BytePos::from(4));
    let expected = Ok(typ("Int"));

    assert_eq!(result, expected);
}

#[test]
fn function_arg() {
    let _ = env_logger::try_init();

    let result = find_type(
        r#"
let f x = x #Int+ 1
""
"#,
        BytePos::from(8),
    );
    let expected = Ok(Type::int());

    assert_eq!(result, expected);
}

#[test]
fn lambda_arg() {
    let _ = env_logger::try_init();

    let text = r#"
let f : Int -> String -> String = \x y -> y
1.0
"#;
    let result = find_type(text, loc(text, 1, 37));
    let expected = Ok(Type::string());

    assert_eq!(result, expected);
}

#[test]
fn unit() {
    let _ = env_logger::try_init();

    let result = find_type("()", BytePos::from(1));
    let expected = Ok(Type::unit());

    assert_eq!(result, expected);
}

#[test]
fn find_all_symbols_test() {
    let _ = env_logger::try_init();

    let text = r#"
let test = 1
let dummy =
    let test = 3
    test
test #Int+ test #Int+ dummy
"#;
    let result = find_all_symbols(text, 6.into());

    assert_eq!(
        result,
        Ok((
            "test".to_string(),
            vec![
                Span::new(loc(text, 1, 4), loc(text, 1, 8)),
                Span::new(loc(text, 5, 0), loc(text, 5, 4)),
                Span::new(loc(text, 5, 11), loc(text, 5, 15)),
            ]
        ))
    );
}

#[derive(PartialEq, Debug)]
struct Symbols {
    name: String,
    children: Vec<Symbols>,
}

impl From<&'_ str> for Symbols {
    fn from(s: &str) -> Self {
        Self {
            name: s.into(),
            children: Vec::new(),
        }
    }
}

fn simple_symbols(symbols: Vec<Sp<completion::CompletionSymbol<'_, '_>>>) -> Vec<Symbols> {
    symbols
        .into_iter()
        .map(|s| Symbols {
            name: s.value.name.to_string(),
            children: simple_symbols(s.value.children),
        })
        .collect()
}

#[test]
fn all_symbols_test() {
    let _ = env_logger::try_init();

    let text = r#"
let test = 1
let dummy a =
    let test = 3
    test
type Abc a = {
    field: a,
}
type Enum =
    | A { a: Int }
    | B
// Unpacked values are not counted because they probably originated in another module
let { x, y } = { x = 1, y = 2 }
1
"#;

    let (expr, result) = support::typecheck_expr(text);
    let expr = expr.expr();
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let symbols = completion::all_symbols(expr.span, &expr);

    assert_eq!(
        simple_symbols(symbols),
        vec![
            "test".into(),
            Symbols {
                name: "dummy".into(),
                children: vec!["a".into(), "test".into()]
            },
            Symbols {
                name: "test.Abc".into(),
                children: vec!["field".into()]
            },
            Symbols {
                name: "test.Enum".into(),
                children: vec![
                    Symbols {
                        name: "A".into(),
                        children: vec!["a".into()]
                    },
                    "B".into()
                ],
            }
        ]
    );
}

#[test]
fn completion_on_type() {
    let _ = env_logger::try_init();

    let text = r#"
type Test a = | Test a
let x : Test Int = Test 1
1.0
"#;
    let result = find_kind(text, loc(text, 2, 11));
    let expected = Ok(Kind::function(Kind::typ(), Kind::typ()));

    assert_eq!(result, expected);
}

#[test]
fn completion_on_builtin_type() {
    let _ = env_logger::try_init();

    let text = r#"
type Test a = | Test a
let x : Test Int = Test 1
1.0
"#;
    let result = find_kind(text, loc(text, 2, 15));
    let expected = Ok(Kind::typ());

    assert_eq!(result, expected);
}

#[test]
fn completion_on_declared_type() {
    let _ = env_logger::try_init();

    let text = r#"
type Test a = | Test a
let x : Test Int = Test 1
1.0
"#;
    let result = find_kind(text, loc(text, 1, 7));
    let expected = Ok(Kind::function(Kind::typ(), Kind::typ()));

    assert_eq!(result, expected);
}

#[test]
#[ignore]
fn completion_on_function_type() {
    let _ = env_logger::try_init();

    let text = r#"
let f x : Int -> Int = x
            // ^
1.0
"#;
    let result = find_kind2(text);
    let expected = Ok(Kind::typ());

    assert_eq!(result, expected);
}

#[test]
fn completion_on_type_field() {
    let _ = env_logger::try_init();

    let text = r#"
type Test = | Test
{
    Test,
    // ^
}
"#;
    let result = find_kind2(text);

    assert_eq!(result, Ok(Kind::typ()));
}

#[test]
fn type_symbol() {
    let _ = env_logger::try_init();

    let text = r#"
type Test a = | Test a
let x : Test Int = Test 1
1.0
"#;
    let result = symbol(text, loc(text, 2, 10));

    assert_eq!(result, Ok("Test".into()));
}
