extern crate gluon_base as base;
extern crate gluon_parser as parser;

mod support;

use base::ast::{TypedIdent, Pattern};
use base::pos::{self, BytePos};

use parser::{Error, ParseErrors};

use support::*;

#[test]
fn empty_input() {
    let result = parse("");
    assert!(result.is_err());
    let (expr, err) = result.unwrap_err();
    assert_eq!(expr, Some(error()));

    let error = Error::UnexpectedEof;
    let span = pos::span(BytePos::from(0), BytePos::from(0));
    assert_eq!(err, ParseErrors::from(vec![pos::spanned(span, error)]));
}

#[test]
fn missing_match_expr() {
    let expr = r#"
    match with
    | x -> x
    "#;
    let result = parse(expr);
    assert!(result.is_err());
    let (expr, err) = result.unwrap_err();
    assert_eq!(expr,
               Some(case(error(),
                         vec![(Pattern::Ident(TypedIdent::new(intern("x"))), id("x"))])));

    let error = Error::UnexpectedToken("With".into());
    let span = pos::span(BytePos::from(11), BytePos::from(15));
    assert_eq!(err, ParseErrors::from(vec![pos::spanned(span, error)]));
}
