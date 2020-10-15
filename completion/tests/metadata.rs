#[macro_use]
extern crate collect_mac;

extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_completion as completion;
extern crate gluon_parser as parser;

use crate::base::{
    ast::Argument,
    metadata::{Attribute, Comment, CommentType, Metadata},
    pos::BytePos,
};

#[allow(unused)]
mod support;
use crate::support::{intern, loc, MockEnv};

fn line_comment<S>(s: S) -> Comment
where
    S: Into<String>,
{
    Comment {
        typ: CommentType::Line,
        content: s.into(),
    }
}

fn get_metadata(s: &str, pos: BytePos) -> Option<Metadata> {
    let env = MockEnv::new();

    let (expr, result) = support::typecheck_expr(s);
    let expr = expr.expr();
    assert!(result.is_ok(), "{}", result.unwrap_err());

    let (_, metadata_map) = check::metadata::metadata(&env, &expr);
    completion::get_metadata(&metadata_map, expr.span, &expr, pos)
        .cloned()
        .map(|mut meta| {
            meta.definition.take();
            meta
        })
}

fn suggest_metadata(s: &str, pos: BytePos, name: &str) -> Option<Metadata> {
    let env = MockEnv::new();

    let (expr, _result) = support::typecheck_expr(s);
    let expr = expr.expr();

    let (_, metadata_map) = check::metadata::metadata(&env, &expr);
    completion::suggest_metadata(&metadata_map, &env, expr.span, &expr, pos, name).map(|meta| {
        let mut meta = Metadata::clone(meta);
        meta.definition.take();
        meta
    })
}

#[test]
fn metadata_at_variable() {
    let _ = env_logger::try_init();

    let text = r#"
/// test
let abc = 1
let abb = 2
let _ = abb
abc
"#;
    let result = get_metadata(text, BytePos::from(45));

    let expected = Some(Metadata {
        ..Metadata::default()
    });
    assert_eq!(result, expected);

    let result = get_metadata(text, BytePos::from(49));

    let expected = Some(Metadata {
        comment: Some(line_comment("test".to_string())),
        ..Metadata::default()
    });
    assert_eq!(result, expected);
}

#[test]
fn metadata_at_binop() {
    let _ = env_logger::try_init();

    let text = r#"
/// test
#[infix(left, 4)]
let (+++) x y = 1
1 +++ 3
"#;
    let result = get_metadata(text, BytePos::from(50));

    let expected = Some(Metadata {
        comment: Some(line_comment("test".to_string())),
        attributes: vec![Attribute {
            name: "infix".into(),
            arguments: Some("left, 4".into()),
        }],
        args: ["x@4_11", "y@4_13"]
            .iter()
            .map(|arg| Argument::explicit(intern(arg)))
            .collect(),
        ..Metadata::default()
    });
    assert_eq!(result, expected);
}

#[test]
fn metadata_at_field_access() {
    let _ = env_logger::try_init();

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
        comment: Some(line_comment("test".to_string())),
        ..Metadata::default()
    });
    assert_eq!(result, expected);
}

#[test]
fn metadata_at_type_pattern() {
    let _ = env_logger::try_init();

    let text = r#"
let { Test } =
    /// test
    type Test = Int
    { Test }
()
"#;
    let result = get_metadata(text, loc(text, 1, 7));

    let expected = Some(Metadata {
        comment: Some(line_comment("test".to_string())),
        ..Metadata::default()
    });
    assert_eq!(result, expected);
}

#[test]
fn suggest_metadata_at_variable() {
    let _ = env_logger::try_init();

    let text = r#"
/// test
let abc = 1
let abb = 2
ab
"#;
    let result = suggest_metadata(text, BytePos::from(36), "abc");

    let expected = Some(Metadata {
        comment: Some(line_comment("test".to_string())),
        ..Metadata::default()
    });
    assert_eq!(result, expected);
}

#[test]
fn suggest_metadata_at_field_access() {
    let _ = env_logger::try_init();

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
        comment: Some(line_comment("test".to_string())),
        ..Metadata::default()
    });
    assert_eq!(result, expected);
}
