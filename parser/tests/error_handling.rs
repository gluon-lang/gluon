extern crate env_logger;
#[macro_use]
extern crate pretty_assertions;

extern crate gluon_base as base;
extern crate gluon_parser as parser;

mod support;

use crate::base::ast::{Expr, Pattern, PatternField, TypedIdent};
use crate::base::pos::{self, BytePos, Span, Spanned};
use crate::base::types::Type;

use crate::parser::{Error, ParseErrors, TokenizeError};

use crate::support::*;

// The expected tokens aren't very interesting since they may change fairly often
fn remove_expected(errors: ParseErrors) -> ParseErrors {
    let f = |mut err: Spanned<Error, _>| {
        match err.value {
            Error::UnexpectedToken(_, ref mut expected)
            | Error::UnexpectedEof(ref mut expected) => expected.clear(),
            _ => (),
        }
        err.span = Span::default();
        err
    };
    ParseErrors::from(errors.into_iter().map(f).collect::<Vec<_>>())
}

#[test]
fn empty_input() {
    let _ = ::env_logger::try_init();

    let result = parse("");
    assert!(result.is_err());
    let (expr, err) = result.unwrap_err();
    assert_eq!(expr, Some(error()));

    let error = Error::UnexpectedEof(vec![]);
    let span = pos::span(BytePos::from(0), BytePos::from(0));
    assert_eq!(
        remove_expected(err),
        ParseErrors::from(vec![pos::spanned(span, error)])
    );
}

#[test]
fn missing_match_expr() {
    let _ = ::env_logger::try_init();

    let expr = r#"
    match with
    | x -> x
    "#;
    let result = parse(expr);
    assert!(result.is_err());
    let (expr, err) = result.unwrap_err();
    assert_eq!(
        clear_span(expr.unwrap()),
        case(
            error(),
            vec![(Pattern::Ident(TypedIdent::new(intern("x"))), id("x"))],
        )
    );

    let error = Error::UnexpectedToken("With".into(), vec![]);
    let span = pos::span(BytePos::from(0), BytePos::from(0));
    assert_eq!(
        remove_expected(err),
        ParseErrors::from(vec![pos::spanned(span, error)])
    );
}

#[test]
fn wrong_indent_expression() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
let y =
    let x = 1
    x
   2
y
"#,
    );
    let span = pos::span(BytePos::from(0), BytePos::from(0));
    let errors = ParseErrors::from(vec![
        pos::spanned(span, Error::UnexpectedToken("IntLiteral".into(), vec![])),
        pos::spanned(span, Error::UnexpectedToken("CloseBlock".into(), vec![])),
    ]);

    assert_eq!(remove_expected(result.unwrap_err().1), errors);
}

#[test]
fn unclosed_string() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
"abc
"#,
    );
    assert!(result.is_err());
}

#[test]
fn tokenizer_error_is_returned() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
12345678901234567890 test
"#,
    );

    let error = Error::Token(TokenizeError::NonParseableInt);
    let span = pos::span(BytePos::from(0), BytePos::from(0));
    let errors = ParseErrors::from(vec![pos::spanned(span, error)]);

    assert_eq!(remove_expected(result.unwrap_err().1), errors);
}

#[test]
fn tokenizer_error_at_eof_is_returned() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
12345678901234567890
"#,
    );

    let error = Error::Token(TokenizeError::NonParseableInt);
    let span = pos::span(BytePos::from(0), BytePos::from(0));
    let errors = ParseErrors::from(vec![pos::spanned(span, error)]);

    assert_eq!(remove_expected(result.unwrap_err().1), errors);
}

#[test]
fn no_infinite_loop_from_default_block() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
let x = 1

    x,
    y = 1
}
"#,
    );
    assert!(result.is_err());
}

#[test]
fn missing_pattern() {
    let _ = ::env_logger::try_init();

    let expr = r#"
    match 1 with
    | -> x
    "#;
    let result = parse(expr);
    assert!(result.is_err());
    let (expr, err) = result.unwrap_err();
    assert_eq!(
        clear_span(expr.unwrap()),
        case(int(1), vec![(Pattern::Error, id("x"))])
    );

    let error = Error::UnexpectedToken("RArrow".into(), vec![]);
    let span = pos::span(BytePos::from(0), BytePos::from(0));
    assert_eq!(
        remove_expected(err),
        ParseErrors::from(vec![pos::spanned(span, error)])
    );
}

#[test]
fn incomplete_alternative() {
    let _ = ::env_logger::try_init();

    let expr = r#"
    match 1 with
    | //
    "#;
    let result = parse(expr);
    assert!(result.is_err());
    let (expr, err) = result.unwrap_err();
    assert_eq!(
        clear_span(expr.unwrap()),
        case(int(1), vec![(Pattern::Error, error())])
    );

    let error = Error::UnexpectedToken("CloseBlock".into(), vec![]);
    let span = pos::span(BytePos::from(0), BytePos::from(0));
    assert_eq!(
        remove_expected(err),
        ParseErrors::from(vec![pos::spanned(span, error)])
    );
}

#[test]
fn incomplete_alternative_before_complete_alternative() {
    let _ = ::env_logger::try_init();

    let expr = r#"
    match 1 with
    | //
    | x -> x
    "#;
    let result = parse(expr);
    assert!(result.is_err());
    let (expr, err) = result.unwrap_err();
    assert_eq!(
        clear_span(expr.unwrap()),
        case(
            int(1),
            vec![
                (Pattern::Error, error()),
                (Pattern::Ident(TypedIdent::new(intern("x"))), id("x")),
            ],
        )
    );

    let error = Error::UnexpectedToken("Pipe".into(), vec![]);
    let span = pos::span(BytePos::from(0), BytePos::from(0));
    assert_eq!(
        remove_expected(err),
        ParseErrors::from(vec![pos::spanned(span, error)])
    );
}

#[test]
fn incomplete_alternative_with_partial_pattern() {
    let _ = ::env_logger::try_init();

    let expr = r#"
    match 1 with
    | { x = }
    "#;
    let result = parse(expr);
    assert!(result.is_err());
    let (expr, err) = result.unwrap_err();
    assert_eq!(
        clear_span(expr.unwrap()),
        case(
            int(1),
            vec![(
                Pattern::Record {
                    typ: Type::hole(),
                    types: vec![],
                    fields: vec![PatternField {
                        name: no_loc(intern("x")),
                        value: Some(no_loc(Pattern::Error)),
                    }],
                    implicit_import: None,
                },
                error(),
            )],
        )
    );

    let errors = vec![
        no_loc(Error::UnexpectedToken("RBrace".into(), vec![])),
        no_loc(Error::UnexpectedToken("CloseBlock".into(), vec![])),
    ];
    assert_eq!(remove_expected(err), ParseErrors::from(errors));
}

#[test]
fn incomplete_let_binding() {
    let _ = ::env_logger::try_init();

    let expr = r#"
    let test =
    1
    "#;
    let result = parse(expr);
    assert!(result.is_err());
    let (expr, err) = result.unwrap_err();
    assert_eq!(
        clear_span(expr.unwrap()),
        let_("test", no_loc(Expr::Error(None)), int(1),)
    );

    let errors = vec![no_loc(Error::UnexpectedToken("CloseBlock".into(), vec![]))];
    assert_eq!(remove_expected(err), ParseErrors::from(errors));
}

#[test]
fn incomplete_let_binding_2() {
    let _ = ::env_logger::try_init();

    let expr = r#"
    let test = io
    "#;
    let result = parse(expr);
    assert!(result.is_err());
    let (expr, err) = result.unwrap_err();

    let errors = vec![no_loc(Error::UnexpectedToken("CloseBlock".into(), vec![]))];
    assert_eq!(remove_expected(err), ParseErrors::from(errors));

    assert_eq!(
        clear_span(expr.unwrap()),
        let_("test", id("io"), no_loc(Expr::Error(None)))
    );
}

#[test]
fn unterminated_char_literal() {
    let _ = ::env_logger::try_init();

    let expr = r#"
    'a
    "#;
    let result = parse(expr);
    assert!(result.is_err());
    let (_expr, err) = result.unwrap_err();

    let error = Error::Token(TokenizeError::UnterminatedCharLiteral);
    let span = pos::span(BytePos::from(6), BytePos::from(6));
    assert_eq!(err, ParseErrors::from(vec![pos::spanned(span, error)]));
}

#[test]
fn missing_close_paren() {
    let _ = ::env_logger::try_init();

    let expr = r#"
    let x =
        (1
    x
    "#;
    let result = parse(expr);
    assert!(result.is_err());
    let (_expr, err) = result.unwrap_err();

    let error = Error::UnexpectedEof([")", ",", "]"].iter().map(|s| s.to_string()).collect());
    let span = pos::span(BytePos::from(35), BytePos::from(35));
    assert_eq!(err, ParseErrors::from(vec![pos::spanned(span, error)]));
}

#[test]
fn invalid_case() {
    let _ = env_logger::try_init();

    assert!(parse(r#"type X = { Test : Type } in ()"#).is_err());
    assert!(parse(r#"type x = { } in ()"#).is_err());
    assert!(parse(r#"type x = | Test in ()"#).is_err());
}

#[test]
fn old_expression() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
let f x = x
and g y = f
1
"#,
    );
    let span = pos::span(BytePos::from(0), BytePos::from(0));
    let errors = ParseErrors::from(vec![pos::spanned(
        span,
        Error::Token(TokenizeError::UnexpectedAnd),
    )]);

    assert_eq!(remove_expected(result.unwrap_err().1), errors);
}

#[test]
fn only_identifiers_are_allowed_on_recursive_patterns() {
    let _ = env_logger::try_init();

    assert!(parse(r#"rec let { } = { } in 1"#).is_err());
    assert!(parse(r#"rec let () = { } in 1"#).is_err());
    assert!(parse(r#"rec let x @ { }  = { x } in 1"#).is_err());
}

#[test]
fn invalid_variant() {
    let _ = env_logger::try_init();

    assert!(parse(r#"type X = | r in ()"#).is_err());
}
