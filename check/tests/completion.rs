extern crate env_logger;

extern crate gluon_base as base;
extern crate gluon_parser as parser;
extern crate gluon_check as check;

use base::ast;
use base::pos::{BytePos, CharPos, Location};
use base::types::{Type, TcType};
use check::completion;

mod support;
use support::{MockEnv, typ};

fn find_type(s: &str, location: Location) -> Result<TcType, ()> {
    let env = MockEnv::new();

    let (mut expr, result) = support::typecheck_expr(s);
    assert!(result.is_ok(), "{}", result.unwrap_err());

    completion::find(&env, &mut expr, location)
}

fn suggest(s: &str, location: Location) -> Result<Vec<String>, ()> {
    let env = MockEnv::new();

    let (mut expr, _result) = support::typecheck_partial_expr(s);
    let mut vec: Vec<String> = {
        completion::suggest(&env, &mut expr, location)
            .into_iter()
            .map(|ident| ident.name.declared_name().to_string())
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

    let result = completion::find(&env,
                                  &mut expr,
                                  Location {
                                      line: 1,
                                      column: CharPos(16),
                                      absolute: BytePos(0),
                                  });
    let expected = Ok(typ("Int"));
    assert_eq!(result, expected);

    let result = completion::find(&env,
                                  &mut expr,
                                  Location {
                                      line: 1,
                                      column: CharPos(17),
                                      absolute: BytePos(0),
                                  });
    let expected = Ok(typ("Int"));
    assert_eq!(result, expected);

    let result = completion::find(&env,
                                  &mut expr,
                                  Location {
                                      line: 1,
                                      column: CharPos(18),
                                      absolute: BytePos(0),
                                  });
    let expected = Ok(typ("Int"));
    assert_eq!(result, expected);

    let result = completion::find(&env,
                                  &mut expr,
                                  Location {
                                      line: 1,
                                      column: CharPos(19),
                                      absolute: BytePos(0),
                                  });
    let expected = Ok(typ("Int"));
    assert_eq!(result, expected);
}

#[test]
fn literal_string() {
    let result = find_type(r#" "asd" "#,
                           Location {
                               line: 1,
                               column: CharPos(2),
                               absolute: BytePos(0),
                           });
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
                           Location {
                               line: 3,
                               column: CharPos(15),
                               absolute: BytePos(0),
                           });
    let expected = Ok(typ("String"));

    assert_eq!(result, expected);
}

#[test]
fn function_call() {
    let result = find_type(r#"
let f x = f x
1
"#,
                           Location {
                               line: 2,
                               column: CharPos(11),
                               absolute: BytePos(0),
                           });
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

    let result = completion::find(&env,
                                  &mut expr,
                                  Location {
                                      line: 6,
                                      column: CharPos(4),
                                      absolute: BytePos(0),
                                  });
    let expected = Ok(Type::function(vec![typ("Int"), typ("Float")], typ("Int")));
    assert_eq!(result, expected);

    let result = completion::find(&env,
                                  &mut expr,
                                  Location {
                                      line: 6,
                                      column: CharPos(1),
                                      absolute: BytePos(0),
                                  });
    let expected = Ok(typ("Int"));
    assert_eq!(result, expected);

    let result = completion::find(&env,
                                  &mut expr,
                                  Location {
                                      line: 6,
                                      column: CharPos(6),
                                      absolute: BytePos(0),
                                  });
    let expected = Ok(typ("Float"));
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
                           Location {
                               line: 3,
                               column: CharPos(14),
                               absolute: BytePos(0),
                           });
    let expected = Ok(typ("Int"));

    assert_eq!(result, expected);
}

#[test]
fn suggest_identifier_when_prefix() {
    let result = suggest(r#"
let test = 1
let tes = ""
let aaa = ""
te
"#,
                         Location {
                             line: 5,
                             column: CharPos(1),
                             absolute: BytePos(0),
                         });
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
                         Location {
                             line: 3,
                             column: CharPos(17),
                             absolute: BytePos(0),
                         });
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
                         Location {
                             line: 4,
                             column: CharPos(8),
                             absolute: BytePos(0),
                         });
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
                         Location {
                             line: 5,
                             column: CharPos(8),
                             absolute: BytePos(0),
                         });
    let expected = Ok(vec!["abc".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_after_dot() {
    let result = suggest(r#"
let record = { aa = 1, ab = 2, c = "" }
record.
"#,
                         Location {
                             line: 3,
                             column: CharPos(7),
                             absolute: BytePos(0),
                         });
    let expected = Ok(vec!["aa".into(), "ab".into(), "c".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_from_record_unpack() {
    let result = suggest(r#"
let { aa, c } = { aa = 1, ab = 2, c = "" }
a
"#,
                         Location {
                             line: 3,
                             column: CharPos(7),
                             absolute: BytePos(0),
                         });
    let expected = Ok(vec!["aa".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_on_record_in_field_access() {
    let result = suggest(r#"
let record = { aa = 1, ab = 2, c = "" }
record.aa
"#,
                         Location {
                             line: 3,
                             column: CharPos(4),
                             absolute: BytePos(0),
                         });
    let expected = Ok(vec!["record".into()]);

    assert_eq!(result, expected);
}
