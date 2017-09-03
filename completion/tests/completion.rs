#[macro_use]
extern crate collect_mac;
extern crate env_logger;

extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_completion as completion;
extern crate gluon_parser as parser;

use base::metadata::Metadata;
use base::pos::{self, BytePos, Span};
use base::types::{ArcType, Field, Type};
use completion::{Suggestion};

mod support;
use support::{intern, typ, MockEnv};

fn find_span_type(s: &str, pos: BytePos) -> Result<(Span<BytePos>, ArcType), ()> {
    let env = MockEnv::new();

    let (mut expr, result) = support::typecheck_expr(s);
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let extract = (completion::SpanAt, completion::TypeAt { env: &env });
    completion::completion(extract, &mut expr, pos)
}

fn find_all_symbols(s: &str, pos: BytePos) -> Result<(String, Vec<Span<BytePos>>), ()> {
    let (expr, result) = support::typecheck_expr(s);
    assert!(result.is_ok(), "{}", result.unwrap_err());

    completion::find_all_symbols(&expr, pos)
}

fn find_type(s: &str, pos: BytePos) -> Result<ArcType, ()> {
    find_span_type(s, pos).map(|t| t.1)
}

fn suggest_types(s: &str, pos: BytePos) -> Result<Vec<Suggestion>, ()> {
    let env = MockEnv::new();

    let (mut expr, result) = support::typecheck_partial_expr(s);
    let mut vec = completion::suggest(&env, &mut expr, pos);
    vec.sort_by(|l, r| l.name.cmp(&r.name));
    Ok(vec)
}

fn suggest(s: &str, pos: BytePos) -> Result<Vec<String>, ()> {
    suggest_types(s, pos).map(|vec| {
        vec.into_iter().map(|suggestion| suggestion.name).collect()
    })
}

fn get_metadata(s: &str, pos: BytePos) -> Option<Metadata> {
    let env = MockEnv::new();

    let (mut expr, result) = support::typecheck_expr(s);
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let (_, metadata_map) = check::metadata::metadata(&env, &mut expr);
    completion::get_metadata(&metadata_map, &mut expr, pos).cloned()
}

fn suggest_metadata(s: &str, pos: BytePos, name: &str) -> Option<Metadata> {
    let env = MockEnv::new();

    let (mut expr, _result) = support::typecheck_expr(s);

    let (_, metadata_map) = check::metadata::metadata(&env, &mut expr);
    completion::suggest_metadata(&metadata_map, &env, &mut expr, pos, name).cloned()
}


#[test]
fn identifier() {
    let env = MockEnv::new();

    let (mut expr, result) = support::typecheck_expr("let abc = 1 in abc");
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let result = completion::find(&env, &mut expr, BytePos::from(15));
    let expected = Ok(typ("Int"));
    assert_eq!(result, expected);

    let result = completion::find(&env, &mut expr, BytePos::from(16));
    let expected = Ok(typ("Int"));
    assert_eq!(result, expected);

    let result = completion::find(&env, &mut expr, BytePos::from(17));
    let expected = Ok(typ("Int"));
    assert_eq!(result, expected);

    let result = completion::find(&env, &mut expr, BytePos::from(18));
    let expected = Ok(typ("Int"));
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
let f x = 1
and g x = "asd"
1
"#,
        BytePos::from(25),
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
    let _ = env_logger::init();

    let result = find_type(
        r#"
let f x = f x
1
"#,
        BytePos::from(11),
    );
    let expected = Ok(Type::function(vec![typ("a0")], typ("a1")));

    assert_eq!(result, expected);
}

#[test]
fn binop() {
    let _ = env_logger::init();

    let env = MockEnv::new();

    let (mut expr, result) = support::typecheck_expr(
        r#"
let (++) l r =
    l #Int+ 1
    r #Float+ 1.0
    l
1 ++ 2.0
"#,
    );
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let result = completion::find(&env, &mut expr, BytePos::from(57));
    let expected = Ok(Type::function(vec![typ("Int"), typ("Float")], typ("Int")));
    assert_eq!(result, expected);

    let result = completion::find(&env, &mut expr, BytePos::from(54));
    let expected = Ok(typ("Int"));
    assert_eq!(result, expected);

    let result = completion::find(&env, &mut expr, BytePos::from(59));
    let expected = Ok(typ("Float"));
    assert_eq!(result, expected);
}

#[test]
fn field_access() {
    let _ = env_logger::init();

    let typ_env = MockEnv::new();

    let (mut expr, result) = support::typecheck_expr(
        r#"
let r = { x = 1 }
r.x
"#,
    );
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let result = completion::find(&typ_env, &mut expr, BytePos::from(19));
    let expected = Ok(Type::record(
        vec![],
        vec![Field::new(intern("x"), typ("Int"))],
    ));
    assert_eq!(result.map(support::close_record), expected);

    let result = completion::find(&typ_env, &mut expr, BytePos::from(22));
    let expected = Ok(typ("Int"));
    assert_eq!(result, expected);
}

#[test]
fn parens_expr() {
    let _ = env_logger::init();

    let text = r#"
let id x = x
(id 1)
"#;
    let (mut expr, result) = support::typecheck_expr(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let env = MockEnv::new();
    let extract = (completion::SpanAt, completion::TypeAt { env: &env });

    let result = completion::completion(extract, &mut expr, BytePos::from(14));
    let expected = Ok((Span::new(14.into(), 20.into()), Type::int()));
    assert_eq!(result, expected);

    let result = completion::completion(extract, &mut expr, BytePos::from(15));
    let expected = Ok((
        Span::new(15.into(), 17.into()),
        Type::function(vec![Type::int()], Type::int()),
    ));
    assert_eq!(result, expected);
}

#[test]
fn parens_pattern() {
    let _ = env_logger::init();

    let text = r#"
let { x } = { x = 1 }
x
"#;
    let (mut expr, result) = support::typecheck_expr(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let env = MockEnv::new();
    let extract = (completion::SpanAt, completion::TypeAt { env: &env });

    let result = completion::completion(extract, &mut expr, BytePos::from(5));
    let expected = Ok((
        Span::new(5.into(), 10.into()),
        Type::record(
            vec![],
            vec![
                Field {
                    name: intern("x"),
                    typ: Type::int(),
                },
            ],
        ),
    ));
    assert_eq!(result, expected);
}

#[test]
fn in_record() {
    let _ = env_logger::init();

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
fn function_arg() {
    let _ = env_logger::init();

    let result = find_type(
        r#"
let f x = x #Int+ 1
""
"#,
        BytePos::from(7),
    );
    let expected = Ok(Type::int());

    assert_eq!(result, expected);
}

#[test]
fn lambda_arg() {
    let _ = env_logger::init();

    let result = find_type(
        r#"
let f : Int -> String -> String = \x y -> y
1.0
"#,
        BytePos::from(38),
    );
    let expected = Ok(Type::string());

    assert_eq!(result, expected);
}

#[test]
fn unit() {
    let _ = env_logger::init();

    let result = find_type("()", BytePos::from(1));
    let expected = Ok(Type::unit());

    assert_eq!(result, expected);
}

#[test]
fn suggest_identifier_when_prefix() {
    let _ = env_logger::init();

    let result = suggest(
        r#"
let test = 1
let tes = ""
let aaa = test
te
"#,
        BytePos::from(43),
    );
    let expected = Ok(vec!["tes".into(), "test".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_arguments() {
    let _ = env_logger::init();

    let result = suggest(
        r#"
let f test =
    \test2 -> tes
123
"#,
        BytePos::from(31),
    );
    let expected = Ok(vec!["test".into(), "test2".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_after_unrelated_type_error() {
    let _ = env_logger::init();

    let result = suggest(
        r#"
let record = { aa = 1, ab = 2, c = "" }
1.0 #Int+ 2
record.a
"#,
        BytePos::from(104),
    );
    let expected = Ok(vec!["aa".into(), "ab".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_through_aliases() {
    let _ = env_logger::init();

    let result = suggest(
        r#"
type Test a = { abc: a -> Int }
type Test2 = Test String
let record: Test2 = { abc = \x -> 0 }
record.ab
"#,
        BytePos::from(108),
    );
    let expected = Ok(vec!["abc".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_after_dot() {
    let _ = env_logger::init();

    let result = suggest(
        r#"
let record = { aa = 1, ab = 2, c = "" }
record.
"#,
        BytePos::from(48),
    );
    let expected = Ok(vec!["aa".into(), "ab".into(), "c".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_from_record_unpack() {
    let _ = env_logger::init();

    let result = suggest(
        r#"
let { aa, c } = { aa = 1, ab = 2, c = "" }
a
"#,
        BytePos::from(45),
    );
    let expected = Ok(vec!["aa".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_from_record_unpack_unordered() {
    let _ = env_logger::init();

    let result = suggest_types(
        r#"
let { c, aa } = { aa = 1, ab = 2.0, c = "" }
a
"#,
        BytePos::from(47),
    );
    let expected = Ok(vec![
        Suggestion {
            name: "aa".into(),
            typ: Type::int(),
        },
    ]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_on_record_in_field_access() {
    let _ = env_logger::init();

    let result = suggest(
        r#"
let record = { aa = 1, ab = 2, c = "" }
record.aa
"#,
        BytePos::from(45),
    );
    let expected = Ok(vec!["record".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_end_of_identifier() {
    let _ = env_logger::init();

    let result = suggest(
        r#"
let abc = 1
let abb = 2
abc
"#,
        BytePos::from(28),
    );
    let expected = Ok(vec!["abc".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_after_identifier() {
    let _ = env_logger::init();

    let result = suggest(
        r#"
let abc = 1
let abb = 2
abc
"#,
        BytePos::from(32),
    );
    let expected = Ok(vec!["abb".into(), "abc".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_between_expressions() {
    let _ = env_logger::init();

    let text = r#"
let abc = 1
let abb = 2
test  test1
""  123
"#;
    let result = suggest(text, BytePos::from(30));
    let expected = Ok(vec!["abb".into(), "abc".into()]);

    assert_eq!(result, expected);

    let result = suggest(text, BytePos::from(40));
    let expected = Ok(vec!["abb".into(), "abc".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_alternative() {
    let _ = env_logger::init();

    let text = r#"
type Test = | A Int | B Int String
match A 3 with
| //
"#;
    let result = suggest(text, BytePos::from(53));
    let expected = Ok(vec!["A".into(), "B".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_incomplete_pattern_name() {
    let _ = env_logger::init();

    let text = r#"
type Test = | A Int | BC Int String
match A 3 with
| B -> 3
"#;
    let result = suggest(text, BytePos::from(55));
    let expected = Ok(vec!["BC".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_implicit_import() {
    let _ = env_logger::init();

    let text = r#"
type Test = | Abc Int
match Abc 1 with
| //
"#;
    let env = MockEnv::new();

    let (mut expr, _result) = support::typecheck_partial_expr(text);
    expr.span.expansion_id = pos::UNKNOWN_EXPANSION;
    let result: Vec<_> = completion::suggest(&env, &mut expr, 42.into())
        .into_iter()
        .map(|s| s.name)
        .collect();

    let expected = ["Abc".to_string()];
    assert_eq!(result, expected);
}

#[test]
fn suggest_implicit_import_from_pattern() {
    let _ = env_logger::init();

    let text = r#"
let { Test } =
    type Test = | Abc Int
    { Test }
match Abc 1 with
| //
"#;
    let env = MockEnv::new();

    let (mut expr, _result) = support::typecheck_partial_expr(text);
    expr.span.expansion_id = pos::UNKNOWN_EXPANSION;
    let result: Vec<_> = completion::suggest(&env, &mut expr, 74.into())
        .into_iter()
        .map(|s| s.name)
        .collect();

    let expected = ["Abc".to_string()];
    assert_eq!(result, expected);
}

#[test]
fn metadata_at_variable() {
    let _ = env_logger::init();

    let text = r#"
/// test
let abc = 1
let abb = 2
abb
abc
"#;
    let result = get_metadata(text, BytePos::from(37));

    let expected = None;
    assert_eq!(result, expected);

    let result = get_metadata(text, BytePos::from(41));

    let expected = Some(Metadata {
        comment: Some("test".to_string()),
        ..Metadata::default()
    });
    assert_eq!(result, expected);
}

#[test]
fn metadata_at_binop() {
    let _ = env_logger::init();

    let text = r#"
/// test
let (+++) x y = 1
1 +++ 3
"#;
    let result = get_metadata(text, BytePos::from(32));

    let expected = Some(Metadata {
        comment: Some("test".to_string()),
        ..Metadata::default()
    });
    assert_eq!(result, expected);
}


#[test]
fn metadata_at_field_access() {
    let _ = env_logger::init();

    let text = r#"
let module = {
        /// test
        abc = 1,
        abb = 2
    }
module.abc
"#;
    let result = get_metadata(text, BytePos::from(81));

    let expected = Some(Metadata {
        comment: Some("test".to_string()),
        ..Metadata::default()
    });
    assert_eq!(result, expected);
}

#[test]
fn suggest_metadata_at_variable() {
    let _ = env_logger::init();

    let text = r#"
/// test
let abc = 1
let abb = 2
ab
"#;
    let result = suggest_metadata(text, BytePos::from(36), "abc");

    let expected = Some(Metadata {
        comment: Some("test".to_string()),
        ..Metadata::default()
    });
    assert_eq!(result, expected);
}

#[test]
fn suggest_metadata_at_field_access() {
    let _ = env_logger::init();

    let text = r#"
let module = {
        /// test
        abc = 1,
        abb = 2
    }
module.ab
"#;
    let result = suggest_metadata(text, BytePos::from(81), "abc");

    let expected = Some(Metadata {
        comment: Some("test".to_string()),
        ..Metadata::default()
    });
    assert_eq!(result, expected);
}

#[test]
fn find_all_symbols_test() {
    let _ = env_logger::init();

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
                Span::new(5.into(), 9.into()),
                Span::new(52.into(), 56.into()),
                Span::new(63.into(), 67.into()),
            ]
        ))
    );
}

#[test]
fn all_symbols_test() {
    let _ = env_logger::init();

    let text = r#"
let test = 1
let dummy =
    let test = 3
    test
type Abc a = a Int
// Unpacked values are not counted because they probably originated in another module
let { x, y } = { x = 1, y = 2 }
1
"#;

    let (expr, result) = support::typecheck_expr(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let symbols = completion::all_symbols(&expr);

    assert_eq!(symbols.len(), 4);
}
