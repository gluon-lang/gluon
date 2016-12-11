#[macro_use]
extern crate collect_mac;
extern crate env_logger;

extern crate gluon_base as base;
extern crate gluon_parser as parser;
extern crate gluon_check as check;

use base::pos::BytePos;
use base::types::{Field, Type, ArcType};
use check::completion;

mod support;
use support::{MockEnv, intern, typ};

fn find_type(s: &str, pos: BytePos) -> Result<ArcType, ()> {
    let env = MockEnv::new();

    let (mut expr, result) = support::typecheck_expr(s);
    assert!(result.is_ok(), "{}", result.unwrap_err());

    completion::find(&env, &mut expr, pos)
}

fn suggest(s: &str, pos: BytePos) -> Result<Vec<String>, ()> {
    let env = MockEnv::new();

    let (mut expr, _result) = support::typecheck_partial_expr(s);
    let mut vec: Vec<String> = {
        completion::suggest(&env, &mut expr, pos)
            .into_iter()
            .map(|ident| ident.name)
            .collect()
    };
    vec.sort();

    Ok(vec)
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
    let result = find_type(r#"
let f x = 1
and g x = "asd"
1
"#,
                           BytePos::from(25));
    let expected = Ok(typ("String"));

    assert_eq!(result, expected);
}

#[test]
fn let_in_let() {
    let result = find_type(r#"
let f =
    let g y =
        123
    g
f
"#,
                           BytePos::from(33));
    let expected = Ok(typ("Int"));

    assert_eq!(result, expected);
}

#[test]
fn function_app() {
    let _ = env_logger::init();

    let result = find_type(r#"
let f x = f x
1
"#,
                           BytePos::from(11));
    let expected = Ok(Type::function(vec![typ("a0")], typ("a1")));

    assert_eq!(result, expected);
}

#[test]
fn binop() {
    let _ = env_logger::init();

    let env = MockEnv::new();

    let (mut expr, result) = support::typecheck_expr(r#"
let (++) l r =
    l #Int+ 1
    r #Float+ 1.0
    l
1 ++ 2.0
"#);
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

    let (mut expr, result) = support::typecheck_expr(r#"
let r = { x = 1 }
r.x
"#);
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let result = completion::find(&typ_env, &mut expr, BytePos::from(19));
    let expected = Ok(Type::record(vec![], vec![Field::new(intern("x"), typ("Int"))]));
    assert_eq!(result.map(support::close_record), expected);

    let result = completion::find(&typ_env, &mut expr, BytePos::from(22));
    let expected = Ok(typ("Int"));
    assert_eq!(result, expected);
}

#[test]
fn in_record() {
    let _ = env_logger::init();

    let result = find_type(r#"
{
    test = 123,
    s = "asd"
}
"#,
                           BytePos::from(15));
    let expected = Ok(typ("Int"));

    assert_eq!(result, expected);
}

#[test]
fn suggest_identifier_when_prefix() {
    let _ = env_logger::init();

    let result = suggest(r#"
let test = 1
let tes = ""
let aaa = test
te
"#,
                         BytePos::from(43));
    let expected = Ok(vec!["tes".into(), "test".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_arguments() {
    let _ = env_logger::init();

    let result = suggest(r#"
let f test =
    \test2 -> tes
123
"#,
                         BytePos::from(31));
    let expected = Ok(vec!["test".into(), "test2".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_after_unrelated_type_error() {
    let _ = env_logger::init();

    let result = suggest(r#"
let record = { aa = 1, ab = 2, c = "" }
1.0 #Int+ 2
record.a
"#,
                         BytePos::from(104));
    let expected = Ok(vec!["aa".into(), "ab".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_through_aliases() {
    let _ = env_logger::init();

    let result = suggest(r#"
type Test a = { abc: a -> Int }
type Test2 = Test String
let record: Test2 = { abc = \x -> 0 }
record.ab
"#,
                         BytePos::from(108));
    let expected = Ok(vec!["abc".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_after_dot() {
    let _ = env_logger::init();

    let result = suggest(r#"
let record = { aa = 1, ab = 2, c = "" }
record.
"#,
                         BytePos::from(48));
    let expected = Ok(vec!["aa".into(), "ab".into(), "c".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_from_record_unpack() {
    let _ = env_logger::init();

    let result = suggest(r#"
let { aa, c } = { aa = 1, ab = 2, c = "" }
a
"#,
                         BytePos::from(45));
    let expected = Ok(vec!["aa".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_on_record_in_field_access() {
    let _ = env_logger::init();

    let result = suggest(r#"
let record = { aa = 1, ab = 2, c = "" }
record.aa
"#,
                         BytePos::from(45));
    let expected = Ok(vec!["record".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_end_of_identifier() {
    let _ = env_logger::init();

    let result = suggest(r#"
let abc = 1
let abb = 2
abc
"#,
                         BytePos::from(28));
    let expected = Ok(vec!["abc".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_after_identifier() {
    let _ = env_logger::init();

    let result = suggest(r#"
let abc = 1
let abb = 2
abc
"#,
                         BytePos::from(32));
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
