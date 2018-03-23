#[macro_use]
extern crate collect_mac;
extern crate either;
extern crate env_logger;

extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_completion as completion;
extern crate gluon_parser as parser;

use std::path::PathBuf;

use either::Either;

use base::ast::{expr_to_path, walk_mut_expr, Expr, MutVisitor, SpannedExpr, TypedIdent};
use base::pos::{self, BytePos};
use base::types::Type;
use base::source::Source;
use base::symbol::Symbol;
use completion::{Suggestion, SuggestionQuery};

#[allow(unused)]
mod support;
use support::MockEnv;

fn suggest_types(s: &str, pos: BytePos) -> Result<Vec<Suggestion>, ()> {
    suggest_query(&SuggestionQuery::new(), s, pos)
}

fn suggest_query(query: &SuggestionQuery, s: &str, pos: BytePos) -> Result<Vec<Suggestion>, ()> {
    let env = MockEnv::new();

    struct ReplaceImport;

    impl<'a> MutVisitor<'a> for ReplaceImport {
        type Ident = Symbol;

        fn visit_expr(&mut self, expr: &mut SpannedExpr<Symbol>) {
            let replacement = match expr.value {
                Expr::App {
                    ref func, ref args, ..
                } => match func.value {
                    Expr::Ident(ref id) if id.name.declared_name() == "import!" => {
                        let mut path = "@".to_string();
                        expr_to_path(&args[0], &mut path).unwrap();
                        Some(Expr::Ident(TypedIdent {
                            name: Symbol::from(path),
                            typ: Type::hole(),
                        }))
                    }
                    _ => None,
                },
                _ => None,
            };
            match replacement {
                Some(replacement) => expr.value = replacement,
                None => walk_mut_expr(self, expr),
            }
        }
    }

    let (mut expr, _result) = support::typecheck_partial_expr(s);

    ReplaceImport.visit_expr(&mut expr);

    let mut vec = query.suggest(&env, &expr, pos);
    vec.sort_by(|l, r| l.name.cmp(&r.name));
    Ok(vec)
}

fn suggest_loc(s: &str, row: usize, column: usize) -> Result<Vec<String>, ()> {
    suggest(
        s,
        Source::new(s)
            .lines()
            .offset(row.into(), column.into())
            .expect("Position is not in source"),
    )
}
fn suggest_query_loc(
    query: &SuggestionQuery,
    s: &str,
    row: usize,
    column: usize,
) -> Result<Vec<String>, ()> {
    suggest_query(
        query,
        s,
        Source::new(s)
            .lines()
            .offset(row.into(), column.into())
            .expect("Position is not in source"),
    ).map(|vec| vec.into_iter().map(|suggestion| suggestion.name).collect())
}

fn suggest(s: &str, pos: BytePos) -> Result<Vec<String>, ()> {
    suggest_types(s, pos).map(|vec| vec.into_iter().map(|suggestion| suggestion.name).collect())
}

#[test]
fn suggest_identifier_when_prefix() {
    let _ = env_logger::try_init();

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
    let _ = env_logger::try_init();

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
    let _ = env_logger::try_init();

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
    let _ = env_logger::try_init();

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
fn suggest_generic_constructor() {
    let _ = env_logger::try_init();

    let result = suggest(
        r#"
type Test a = | Test a
Te
"#,
        BytePos::from(26),
    );
    let expected = Ok(vec!["Test".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_after_dot() {
    let _ = env_logger::try_init();

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
    let _ = env_logger::try_init();

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
    let _ = env_logger::try_init();

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
            typ: Either::Right(Type::int()),
        },
    ]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_as_pattern() {
    let _ = env_logger::try_init();

    let text = r#"
let abc@ { y } = { y = 1 }
a
"#;
    let result = suggest_loc(text, 2, 1);
    let expected = Ok(vec!["abc".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_on_record_in_field_access() {
    let _ = env_logger::try_init();

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
    let _ = env_logger::try_init();

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
    let _ = env_logger::try_init();

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
    let _ = env_logger::try_init();

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
    let _ = env_logger::try_init();

    let text = r#"
type Test = | A Int | B Int String
match A 3 with
| //
"#;
    let result = suggest_loc(text, 3, 1);
    let expected = Ok(vec!["A".into(), "B".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_incomplete_pattern_name() {
    let _ = env_logger::try_init();

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
fn suggest_record_field_in_pattern_at_ident() {
    let _ = env_logger::try_init();

    let text = r#"
let { ab } = { x = 1, abc = "", abcd = 2 }
()
"#;
    let result = suggest(text, BytePos::from(9));
    let expected = Ok(vec!["abc".into(), "abcd".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_record_field_in_pattern_at_nothing() {
    let _ = env_logger::try_init();

    let text = r#"
let { ab } = { x = 1, abc = "", abcd = 2 }
()
"#;
    let result = suggest(text, BytePos::from(10));
    let expected = Ok(vec!["abc".into(), "abcd".into(), "x".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_record_field_in_pattern_before_field() {
    let _ = env_logger::try_init();

    let text = r#"
let { a abc } = { x = 1, abc = "", abcd = 2 }
()
"#;
    let result = suggest_loc(text, 1, 7);
    let expected = Ok(vec!["abcd".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_alias_field_in_pattern() {
    let _ = env_logger::try_init();

    let text = r#"
type Test = { x : Int, abc : String, abcd : Int }
let { ab } = { x = 1, abc = "", abcd = 2 }
()
"#;
    let result = suggest_loc(text, 2, 8);
    let expected = Ok(vec!["abc".into(), "abcd".into()]);

    assert_eq!(result, expected);
}

fn find_gluon_root() -> PathBuf {
    use std::env;
    use std::fs;
    let mut dir = env::current_dir().unwrap();
    while fs::metadata(dir.join("std")).is_err() {
        dir = dir.parent().unwrap().into();
    }
    dir
}

#[test]
fn suggest_module_import() {
    let _ = env_logger::try_init();

    let text = r#"
import! st
"#;
    let query = SuggestionQuery {
        paths: vec![find_gluon_root()],
        ..SuggestionQuery::default()
    };
    let result = suggest_query_loc(&query, text, 1, 10);
    let expected = Ok(vec!["std".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_module_import_nested() {
    let _ = env_logger::try_init();

    let text = r#"
import! std.p
"#;
    let query = SuggestionQuery {
        paths: vec![find_gluon_root()],
        ..SuggestionQuery::default()
    };
    let result = suggest_query_loc(&query, text, 1, 12);
    let expected = Ok(vec!["parser".into(), "prelude".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_module_import_on_dot() {
    let _ = env_logger::try_init();

    let text = r#"
import! std.
"#;
    let query = SuggestionQuery {
        paths: vec![find_gluon_root()],
        ..SuggestionQuery::default()
    };
    let result = suggest_query_loc(&query, text, 1, 12);
    assert!(result.is_ok());

    let suggestions = result.unwrap();
    assert!(
        suggestions.iter().any(|s| s == "prelude"),
        "{:?}",
        suggestions
    );
}

#[test]
fn suggest_module_import_typed() {
    let _ = env_logger::try_init();

    let text = r#"
import! std.prelud
"#;
    let query = SuggestionQuery {
        paths: vec![find_gluon_root()],
        ..SuggestionQuery::default()
    };
    let result = suggest_query(
        &query,
        text,
        Source::new(text)
            .lines()
            .offset(1.into(), 12.into())
            .expect("Position is not in source"),
    );
    assert!(result.is_ok());

    let expected = Ok(vec![
        Suggestion {
            name: "prelude".into(),
            typ: Either::Right(Type::int()),
        },
    ]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_module_import_with_module() {
    let _ = env_logger::try_init();

    let text = r#"
import! example.
"#;
    let query = SuggestionQuery {
        paths: vec![find_gluon_root()],
        modules: vec!["example.test".into()],
        ..SuggestionQuery::default()
    };
    let result = suggest_query_loc(&query, text, 1, 16);
    let expected = Ok(vec!["test".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_module_import_with_inner_module() {
    let _ = env_logger::try_init();

    let text = r#"
import! example.
"#;
    let query = SuggestionQuery {
        paths: vec![find_gluon_root()],
        modules: vec!["example.test.inner".into()],
        ..SuggestionQuery::default()
    };
    let result = suggest_query_loc(&query, text, 1, 16);
    let expected = Ok(vec!["test".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_module_import_with_inner_module_last() {
    let _ = env_logger::try_init();

    let text = r#"
import! example.test.inn
"#;
    let query = SuggestionQuery {
        paths: vec![find_gluon_root()],
        modules: vec!["example.test.inner".into()],
        ..SuggestionQuery::default()
    };
    let result = suggest_query_loc(&query, text, 1, 24);
    let expected = Ok(vec!["inner".into()]);

    assert_eq!(result, expected);
}

#[test]
fn dont_suggest_variant_at_record_field() {
    let _ = env_logger::try_init();

    let text = r#"
type Test = | Test Int
let { } = { abc = "" }
()
"#;
    let result = suggest_loc(text, 2, 6);
    let expected = Ok(vec!["abc".into()]);

    assert_eq!(result, expected);
}

#[test]
fn dont_suggest_field_already_in_pattern() {
    let _ = env_logger::try_init();

    let text = r#"
type Test = | Test Int
let { abc, a, Test } = { Test, x = 1, abc = "", abcd = 2 }
()
"#;
    let result = suggest_loc(text, 2, 12);
    let expected = Ok(vec!["abcd".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_exact_field_match_in_pattern() {
    let _ = env_logger::try_init();

    let text = r#"
let { abc } = { abc = "" }
()
"#;
    let result = suggest_loc(text, 1, 8);
    let expected = Ok(vec!["abc".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_type_field_in_record_pattern_at_ident() {
    let _ = env_logger::try_init();

    let text = r#"
type Test = | Test Int
let { T } = { Test, x = 1 }
()
"#;
    let result = suggest_loc(text, 2, 7);
    let expected = Ok(vec!["Test".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_type_field_in_record_pattern_at_empty() {
    let _ = env_logger::try_init();

    let text = r#"
type Test = | Test Int
let {  } = { Test, x = 1 }
()
"#;
    let result = suggest_loc(text, 2, 7);
    let expected = Ok(vec!["Test".into(), "x".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_in_type_binding() {
    let _ = env_logger::try_init();

    let text = r#"
type Test = Int
type Abc = Te
()
"#;
    let result = suggest_loc(text, 2, 13);
    let expected = Ok(vec!["Test".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_type_variable_in_type_binding() {
    let _ = env_logger::try_init();

    let text = r#"
type Test a b ab = { x : a, y : b, z: ab }
()
"#;
    let result = suggest_loc(text, 1, 26);
    let expected = Ok(vec!["a".into(), "ab".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_in_type_of_let_binding() {
    let _ = env_logger::try_init();

    let text = r#"
type Test = Int
type Abc = Te
let x: T = 1
()
"#;
    let result = suggest_loc(text, 3, 8);
    let expected = Ok(vec!["Test".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_from_forall_params() {
    let _ = env_logger::try_init();

    let text = r#"
let f x _ : forall abc b . a -> b -> abc = x
()
"#;
    let result = suggest_loc(text, 1, 28);
    let expected = Ok(vec!["abc".into()]);

    assert_eq!(result, expected);
}

#[test]
fn suggest_implicit_import() {
    let _ = env_logger::try_init();

    let text = r#"
type Test = | Abc Int
match Abc 1 with
| //
"#;
    let env = MockEnv::new();

    let (mut expr, _result) = support::typecheck_partial_expr(text);
    expr.span.expansion_id = pos::UNKNOWN_EXPANSION;
    let result: Vec<_> = completion::suggest(&env, &expr, 42.into())
        .into_iter()
        .map(|s| s.name)
        .collect();

    let expected = ["Abc".to_string()];
    assert_eq!(result, expected);
}

#[test]
fn suggest_implicit_import_from_pattern() {
    let _ = env_logger::try_init();

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
    let result: Vec<_> = completion::suggest(&env, &expr, 74.into())
        .into_iter()
        .map(|s| s.name)
        .collect();

    let expected = ["Abc".to_string()];
    assert_eq!(result, expected);
}
