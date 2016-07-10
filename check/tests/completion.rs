extern crate env_logger;

extern crate gluon_base as base;
extern crate gluon_parser as parser;
extern crate gluon_check as check;

use base::ast;
use base::ast::Location;
use base::types::{Type, TcType};

use check::completion;

mod functions;
use functions::*;

fn find_type(s: &str, location: Location) -> Result<TcType, ()> {
    let (mut expr, result) = typecheck_expr(s);
    assert!(result.is_ok(), "{}", result.unwrap_err());
    completion::find(&ast::EmptyEnv::new(), &mut expr, location)
}

fn suggest(s: &str, location: Location) -> Result<Vec<String>, ()> {
    let (mut expr, _result) = typecheck_partial_expr(s);
    let vec = completion::suggest(&ast::EmptyEnv::new(), &mut expr, location);
    let mut vec: Vec<String> = vec.into_iter().map(|ident| ident.name.declared_name().to_string()).collect();
    vec.sort();
    Ok(vec)
}

#[test]
fn identifier() {
    let (mut expr, result) = typecheck_expr("let abc = 1 in abc");
    assert!(result.is_ok(), "{}", result.unwrap_err());
    let result = completion::find(&ast::EmptyEnv::new(), &mut expr, Location { row: 1, column: 16, absolute: 0 });
    assert_eq!(result, Ok(typ("Int")));
    let result = completion::find(&ast::EmptyEnv::new(), &mut expr, Location { row: 1, column: 17, absolute: 0 });
    assert_eq!(result, Ok(typ("Int")));
    let result = completion::find(&ast::EmptyEnv::new(), &mut expr, Location { row: 1, column: 18, absolute: 0 });
    assert_eq!(result, Ok(typ("Int")));
    let result = completion::find(&ast::EmptyEnv::new(), &mut expr, Location { row: 1, column: 19, absolute: 0 });
    assert_eq!(result, Ok(typ("Int")));
}

#[test]
fn literal_string() {
    let result = find_type(r#" "asd" "#, Location { row: 1, column: 2, absolute: 0 });
    assert_eq!(result, Ok(typ("String")));
}

#[test]
fn in_let() {
    let result = find_type(
r#"
let f x = 1
and g x = "asd"
1
"#, Location { row: 3, column: 15, absolute: 0 });
    assert_eq!(result, Ok(typ("String")));
}

#[test]
fn function_call() {
    let result = find_type(
r#"
let f x = f x
1
"#, Location { row: 2, column: 11, absolute: 0 });
    assert_eq!(result, Ok(Type::function(vec![typ("a0")], typ("a1"))));
}

#[test]
fn binop() {
    let (mut expr, result) = typecheck_expr(
r#"
let (++) l r =
    l #Int+ 1
    r #Float+ 1.0
    l
1 ++ 2.0
"#);
    assert!(result.is_ok(), "{}", result.unwrap_err());
    let result = completion::find(&ast::EmptyEnv::new(), &mut expr, Location { row: 6, column: 4, absolute: 0 });
    assert_eq!(result, Ok(Type::function(vec![typ("Int"), typ("Float")], typ("Int"))));
    let result = completion::find(&ast::EmptyEnv::new(), &mut expr, Location { row: 6, column: 1, absolute: 0 });
    assert_eq!(result, Ok(typ("Int")));
    let result = completion::find(&ast::EmptyEnv::new(), &mut expr, Location { row: 6, column: 6, absolute: 0 });
    assert_eq!(result, Ok(typ("Float")));
}

#[test]
fn in_record() {
    let result = find_type(
r#"
{
    test = 123,
    s = "asd"
}
"#, Location { row: 3, column: 14, absolute: 0 });
    assert_eq!(result, Ok(typ("Int")));
}

#[test]
fn suggest_identifier_when_prefix() {
    let result = suggest(
r#"
let test = 1
let tes = ""
let aaa = ""
te
"#,
Location { row: 5, column: 1, absolute: 0 });
    assert_eq!(result, Ok(vec!["tes".into(), "test".into()]));
}

#[test]
fn suggest_arguments() {
    let result = suggest(
r#"
let f test =
    \test2 -> tes
123
"#,
Location { row: 3, column: 17, absolute: 0 });
    assert_eq!(result, Ok(vec!["test".into(), "test2".into()]));
}

#[test]
fn suggest_after_unrelated_type_error() {
    let result = suggest(
r#"
let record = { aa = 1, ab = 2, c = "" }
1.0 #Int+ 2
record.a
"#,
Location { row: 4, column: 8, absolute: 0 });
    assert_eq!(result, Ok(vec!["aa".into(), "ab".into()]));
}

#[test]
fn suggest_through_aliases() {
    let result = suggest(
r#"
type Test a = { abc: a -> Int }
type Test2 = Test String
let record: Test2 = { abc = \x -> 0 }
record.ab
"#,
Location { row: 5, column: 8, absolute: 0 });
    assert_eq!(result, Ok(vec!["abc".into()]));
}

#[test]
fn suggest_after_dot() {
    let result = suggest(
r#"
let record = { aa = 1, ab = 2, c = "" }
record.
"#,
Location { row: 3, column: 7, absolute: 0 });
    assert_eq!(result, Ok(vec!["aa".into(), "ab".into(), "c".into()]));
}

#[test]
fn suggest_from_record_unpack() {
    let result = suggest(
r#"
let { aa, c } = { aa = 1, ab = 2, c = "" }
a
"#,
Location { row: 3, column: 7, absolute: 0 });
    assert_eq!(result, Ok(vec!["aa".into()]));
}

#[test]
fn suggest_on_record_in_field_access() {
    let result = suggest(
r#"
let record = { aa = 1, ab = 2, c = "" }
record.aa
"#,
Location { row: 3, column: 4, absolute: 0 });
    assert_eq!(result, Ok(vec!["record".into()]));
}
