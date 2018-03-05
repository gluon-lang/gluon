#[macro_use]
extern crate collect_mac;
extern crate env_logger;

extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_parser as parser;

use base::ast::SpannedExpr;
use base::metadata::{Metadata, MetadataEnv};
use base::symbol::{Symbol, SymbolRef};

fn metadata(env: &MetadataEnv, expr: &mut SpannedExpr<Symbol>) -> Metadata {
    check::metadata::metadata(env, expr).0
}

mod support;

struct MockEnv;

impl MetadataEnv for MockEnv {
    fn get_metadata(&self, _id: &SymbolRef) -> Option<&Metadata> {
        None
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
            comment: Some("The identity function".into()),
            module: Default::default(),
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
        metadata.module.get("id"),
        Some(&Metadata {
            comment: Some("The identity function".into()),
            module: Default::default(),
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
        metadata.module.get("Test"),
        Some(&Metadata {
            comment: Some("A test type".into()),
            module: Default::default(),
        })
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
        metadata.module.get("id"),
        Some(&Metadata {
            comment: Some("The identity function".into()),
            module: Default::default(),
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
            comment: Some("The identity function".into()),
            module: Default::default(),
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
            .and_then(|metadata| metadata.module.get("x")),
        Some(&Metadata {
            comment: Some("A field".into()),
            module: Default::default(),
        })
    );
}
