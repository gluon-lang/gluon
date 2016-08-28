extern crate env_logger;

extern crate gluon_base as base;
extern crate gluon_parser as parser;
extern crate gluon_check as check;

use base::pos::BytePos;
use base::types::{Field, Type, TcType};
use check::completion;

mod support;
use support::{MockEnv, intern, typ};

fn find_type(s: &str, pos: BytePos) -> Result<TcType, ()> {
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

    let result = completion::find(&env, &mut expr, BytePos(15));
    let expected = Ok(typ("Int"));
    assert_eq!(result, expected);

    let result = completion::find(&env, &mut expr, BytePos(16));
    let expected = Ok(typ("Int"));
    assert_eq!(result, expected);

    let result = completion::find(&env, &mut expr, BytePos(17));
    let expected = Ok(typ("Int"));
    assert_eq!(result, expected);

    let result = completion::find(&env, &mut expr, BytePos(18));
    let expected = Ok(typ("Int"));
    assert_eq!(result, expected);
}

#[test]
fn literal_string() {
    let result = find_type(r#" "asd" "#, BytePos(1));
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
                           BytePos(25));
    let expected = Ok(typ("String"));

    assert_eq!(result, expected);
}

#[test]
fn function_call() {
    let result = find_type(r#"
let f x = f x
1
"#,
                           BytePos(11));
    let expected = Ok(Type::function(vec![typ("a0")], typ("a1")));

    assert_eq!(result, expected);
}

#[test]
fn binop() {
    let env = MockEnv::new();

    let (mut expr, result) = support::typecheck_expr(r#"
let (++) l r =
    l #Int+ 1
    r #Float+ 1.0
    l
1 ++ 2.0
"#);
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let result = completion::find(&env, &mut expr, BytePos(57));
    let expected = Ok(Type::function(vec![typ("Int"), typ("Float")], typ("Int")));
    assert_eq!(result, expected);

    let result = completion::find(&env, &mut expr, BytePos(54));
    let expected = Ok(typ("Int"));
    assert_eq!(result, expected);

    let result = completion::find(&env, &mut expr, BytePos(59));
    let expected = Ok(typ("Float"));
    assert_eq!(result, expected);
}

#[test]
fn field_access() {
    let typ_env = MockEnv::new();

    let (mut expr, result) = support::typecheck_expr(r#"
let r = { x = 1 }
r.x
"#);
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let result = completion::find(&typ_env, &mut expr, BytePos(19));
    let expected = Ok(Type::record(vec![],
                                   vec![Field {
                                            name: intern("x"),
                                            typ: typ("Int"),
                                        }]));
    assert_eq!(result, expected);

    let result = completion::find(&typ_env, &mut expr, BytePos(22));
    let expected = Ok(typ("Int"));
    assert_eq!(result, expected);
}

#[test]
fn in_record() {
    let result = find_type(r#"
{
    test = 123,
    s = "asd"
}
"#,
                           BytePos(15));
    let expected = Ok(typ("Int"));

    assert_eq!(result, expected);
}

#[test]
fn suggest_identifier_when_prefix() {
    let result = suggest(r#"
let test = 1
let tes = ""
let aaa = test
te
"#,
                         BytePos(43));
    let expected = Ok(vec!["tes".into(), "test".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_arguments() {
    let result = suggest(r#"
let f test =
    \test2 -> tes
123
"#,
                         BytePos(31));
    let expected = Ok(vec!["test".into(), "test2".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_after_unrelated_type_error() {
    let result = suggest(r#"
let record = { aa = 1, ab = 2, c = "" }
1.0 #Int+ 2
record.a
"#,
                         BytePos(104));
    let expected = Ok(vec!["aa".into(), "ab".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_through_aliases() {
    let result = suggest(r#"
type Test a = { abc: a -> Int }
type Test2 = Test String
let record: Test2 = { abc = \x -> 0 }
record.ab
"#,
                         BytePos(108));
    let expected = Ok(vec!["abc".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_after_dot() {
    let result = suggest(r#"
let record = { aa = 1, ab = 2, c = "" }
record.
"#,
                         BytePos(48));
    let expected = Ok(vec!["aa".into(), "ab".into(), "c".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_from_record_unpack() {
    let result = suggest(r#"
let { aa, c } = { aa = 1, ab = 2, c = "" }
a
"#,
                         BytePos(45));
    let expected = Ok(vec!["aa".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_on_record_in_field_access() {
    let result = suggest(r#"
let record = { aa = 1, ab = 2, c = "" }
record.aa
"#,
                         BytePos(45));
    let expected = Ok(vec!["record".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_end_of_identifier() {
    let result = suggest(r#"
let abc = 1
let abb = 2
abc
"#,
                         BytePos(28));
    let expected = Ok(vec!["abc".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_after_identifier() {
    let result = suggest(r#"
let abc = 1
let abb = 2
abc
"#,
                         BytePos(32));
    let expected = Ok(vec!["abb".into(), "abc".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_between_expressions() {
    let text = r#"
let abc = 1
let abb = 2
test  test1
""  123
"#;
    let result = suggest(text, BytePos(30));
    let expected = Ok(vec!["abb".into(), "abc".into()]);

    assert_eq!(result, expected);

    let result = suggest(text, BytePos(40));
    let expected = Ok(vec!["abb".into(), "abc".into()]);

    assert_eq!(result, expected);
}