extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_parser as parser;

use std::sync::Arc;

use crate::base::{
    ast::{Argument, RootExpr},
    metadata::{Attribute, Comment, CommentType, Metadata, MetadataEnv},
    symbol::{Symbol, SymbolRef},
};

fn metadata(env: &dyn MetadataEnv, expr: &mut RootExpr<Symbol>) -> Metadata {
    Metadata::clone(&check::metadata::metadata(env, expr.expr_mut()).0)
}

mod support;

use crate::support::intern;

struct MockEnv;

impl MetadataEnv for MockEnv {
    fn get_metadata(&self, _id: &SymbolRef) -> Option<Arc<Metadata>> {
        None
    }
}

fn line_comment(s: &str) -> Comment {
    Comment {
        typ: CommentType::Line,
        content: s.into(),
    }
}

#[test]
fn propagate_metadata_let_in() {
    let _ = env_logger::try_init();

    let text = r#"
/// The identity function
let id x = x
id
"#;
    let (mut expr, result) = support::typecheck_expr(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());

    let metadata = metadata(&MockEnv, &mut expr);
    assert_eq!(
        metadata,
        Metadata {
            definition: metadata.definition.clone(),
            comment: Some(line_comment("The identity function")),
            args: vec![Argument::explicit(intern("x@3_8"))],
            ..Metadata::default()
        }
    );
}

#[test]
fn propagate_metadata_let_record() {
    let _ = env_logger::try_init();

    let text = r#"
/// The identity function
let id x = x
{ id }
"#;
    let (mut expr, result) = support::typecheck_expr(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());

    let metadata = metadata(&MockEnv, &mut expr);
    assert_eq!(
        metadata.module.get("id").map(|m| &**m),
        Some(&Metadata {
            definition: metadata.module.get("id").and_then(|m| m.definition.clone()),
            comment: Some(line_comment("The identity function")),
            args: vec![Argument::explicit(intern("x@3_8"))],
            ..Metadata::default()
        })
    );
}

#[test]
fn propagate_metadata_type_record() {
    let _ = env_logger::try_init();

    let text = r#"
/// A test type
type Test = Int
{ Test }
"#;
    let (mut expr, result) = support::typecheck_expr(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());

    let metadata = metadata(&MockEnv, &mut expr);
    assert_eq!(
        metadata.module.get("Test").map(|m| &**m),
        Some(&Metadata {
            definition: metadata
                .module
                .get("Test")
                .and_then(|m| m.definition.clone()),
            comment: Some(line_comment("A test type")),
            ..Metadata::default()
        })
    );
}

#[test]
fn propagate_metadata_parens() {
    let _ = env_logger::try_init();

    let text = r#"
/// The identity function
let id x = x
id
"#;
    let (mut expr, result) = support::typecheck_expr(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());

    let metadata = metadata(&MockEnv, &mut expr);
    assert_eq!(
        metadata,
        Metadata {
            definition: Some(intern("id@3_5")),
            comment: Some(line_comment("The identity function")),
            args: vec![Argument::explicit(intern("x@3_8"))],
            ..Metadata::default()
        }
    );
}

#[test]
fn propagate_metadata_record_field_comment() {
    let _ = env_logger::try_init();

    let text = r#"
{
    /// The identity function
    id = \x -> x
}
"#;
    let (mut expr, result) = support::typecheck_expr(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());

    let metadata = metadata(&MockEnv, &mut expr);
    assert_eq!(
        metadata.module.get("id").map(|m| &**m),
        Some(&Metadata {
            definition: metadata.module.get("id").and_then(|m| m.definition.clone()),
            comment: Some(line_comment("The identity function")),
            ..Metadata::default()
        })
    );
}

#[test]
fn projection_has_metadata() {
    let _ = env_logger::try_init();

    let text = r#"
let x = {
    /// The identity function
    id = \x -> x
}
x.id
"#;
    let (mut expr, result) = support::typecheck_expr(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());

    let metadata = metadata(&MockEnv, &mut expr);
    assert_eq!(
        metadata,
        Metadata {
            definition: metadata.definition.clone(),
            comment: Some(line_comment("The identity function")),
            ..Metadata::default()
        }
    );
}

#[test]
fn propagate_metadata_from_field_in_type() {
    let _ = env_logger::try_init();

    let text = r#"
type Test = {
    /// A field
    x : Int
}
{ Test }
"#;
    let (mut expr, result) = support::typecheck_expr(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());

    let metadata = metadata(&MockEnv, &mut expr);
    assert_eq!(
        metadata
            .module
            .get("Test")
            .and_then(|metadata| metadata.module.get("x"))
            .map(|m| &**m),
        Some(&Metadata {
            comment: Some(line_comment("A field")),
            ..Metadata::default()
        })
    );
}

#[test]
fn propagate_metadata_from_types_to_values() {
    let _ = env_logger::try_init();

    let text = r#"
/// A type
type Test = {
    /// A field
    x : Int,
    /// Another field
    y : String,
}

/// Shadowing comment
let test: Test = {
    x = 1,
    /// Shadowing field comment
    y = "",
}
{ test }
"#;
    let (mut expr, result) = support::typecheck_expr(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());

    let metadata = metadata(&MockEnv, &mut expr);
    assert_eq!(
        metadata
            .module
            .get("test")
            .and_then(|metadata| metadata.module.get("x"))
            .map(|m| &**m),
        Some(&Metadata {
            comment: Some(line_comment("A field")),
            ..Metadata::default()
        })
    );
    assert_eq!(
        metadata
            .module
            .get("test")
            .and_then(|metadata| metadata.module.get("y"))
            .map(|m| &**m),
        Some(&Metadata {
            comment: Some(line_comment("Shadowing field comment")),
            ..Metadata::default()
        })
    );
    assert_eq!(
        metadata
            .module
            .get("test")
            .and_then(|metadata| metadata.comment.as_ref()),
        Some(&line_comment("Shadowing comment"))
    );
}

#[test]
fn propagate_metadata_from_types_through_arg() {
    let _ = env_logger::try_init();

    let text = r#"
type Test a = {
    /// A field
    x : a,
}

let x ?test : [Test a] -> a = test.x
{ x }
"#;
    let (mut expr, result) = support::typecheck_expr(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());

    let metadata = metadata(&MockEnv, &mut expr);
    assert_eq!(
        metadata.module.get("x").map(|m| &**m),
        Some(&Metadata {
            definition: metadata.module.get("x").and_then(|m| m.definition.clone()),
            comment: Some(line_comment("A field")),
            args: vec![Argument::implicit(intern("test@7_8"))],
            ..Metadata::default()
        })
    );
}

#[test]
fn propagate_metadata_through_argument() {
    let _ = env_logger::try_init();

    let text = r#"
type Test a = {
    /// A field
    x : a,
}

let x ?test : [Test a] -> a = test.x
{ x }
"#;
    let (mut expr, result) = support::typecheck_expr(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());

    let metadata = metadata(&MockEnv, &mut expr);
    assert_eq!(
        metadata.module.get("x").map(|m| &**m),
        Some(&Metadata {
            definition: metadata.module.get("x").and_then(|m| m.definition.clone()),
            comment: Some(line_comment("A field")),
            args: vec![Argument::implicit(intern("test@7_8"))],
            ..Metadata::default()
        })
    );
}

#[test]
fn propagate_metadata_through_implicits1() {
    let _ = env_logger::try_init();

    let text = r#"
#[attribute]
type Test a = {
    x : a,
}

type Wrap a = | Wrap a

let x ?test : [Test a] -> Test (Wrap a) = { x = Wrap test.x }
{ x }
"#;
    let (mut expr, result) = support::typecheck_expr(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());

    let metadata = metadata(&MockEnv, &mut expr);
    assert_eq!(
        metadata.module.get("x").map(|m| &**m),
        Some(&Metadata {
            definition: metadata.module.get("x").and_then(|m| m.definition.clone()),
            attributes: vec![Attribute {
                name: "attribute".into(),
                arguments: None,
            }],
            args: vec![Argument::implicit(intern("test@9_8"))],
            ..Metadata::default()
        })
    );
}

#[test]
fn propagate_metadata_through_implicits2() {
    let _ = env_logger::try_init();

    let text = r#"
type Test a = {
    #[attribute]
    x : a,
}

type Wrap a = | Wrap a

let x ?test : [Test a] -> a = test.x
{ x }
"#;
    let (mut expr, result) = support::typecheck_expr(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());

    let metadata = metadata(&MockEnv, &mut expr);
    assert_eq!(
        metadata.module.get("x").map(|m| &**m),
        Some(&Metadata {
            definition: metadata.module.get("x").and_then(|m| m.definition.clone()),
            attributes: vec![Attribute {
                name: "attribute".into(),
                arguments: None,
            }],
            args: vec![Argument::implicit(intern("test@9_8"))],
            ..Metadata::default()
        })
    );
}
