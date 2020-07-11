#[macro_use]
extern crate pretty_assertions;

extern crate gluon_base as base;
extern crate gluon_parser as parser;

mod support;

use {
    base::{
        ast::{Expr, Pattern, PatternField, TypedIdent},
        mk_ast_arena,
        pos::{self, BytePos},
        types::Type,
    },
    parser::{Error, ParseErrors, Token, TokenizeError},
};

use crate::support::*;

test_parse_error! {
    empty_input,
    "",
    |_: base::ast::ArenaRef<'_, '_, String>| error(),
    {
        let error = Error::UnexpectedEof(vec![]);
        let span = pos::span(BytePos::from(0), BytePos::from(0));
        ParseErrors::from(vec![pos::spanned(span, error)])
    }
}

test_parse_error! {
    missing_match_expr,
    r#"
    match with
    | x -> x
    "#,
    |arena| case(arena,
            error(),
            vec![(Pattern::Ident(TypedIdent::new(intern("x"))), id("x"))],
        ),
    {

        let error = Error::UnexpectedToken(Token::With, vec![]);
        let span = pos::span(BytePos::from(0), BytePos::from(0));
        ParseErrors::from(vec![pos::spanned(span, error)])
    }
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
        pos::spanned(span, Error::UnexpectedToken(Token::IntLiteral(2), vec![])),
        pos::spanned(span, Error::UnexpectedToken(Token::CloseBlock, vec![])),
    ]);

    assert_eq!(remove_expected(result.unwrap_err().1), errors);
}

test_parse_error! {
    unclosed_string,
    r#"
"abc
123"#,
    |_: base::ast::ArenaRef<'_, '_, String>| string("abc\n123"),
    {
        let error = Error::Token(parser::TokenizeError::UnterminatedStringLiteral);
        let span = pos::span(BytePos::from(0), BytePos::from(0));
        ParseErrors::from(vec![pos::spanned(span, error)])
    }
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

test_parse_error! {
    missing_pattern,
    r#"
    match 1 with
    | -> x
    "#,
    |arena| case(arena, int(1), vec![(Pattern::Error, id("x"))]),
    {
        let error = Error::UnexpectedToken(Token::RArrow, vec![]);
        let span = pos::span(BytePos::from(0), BytePos::from(0));
        ParseErrors::from(vec![pos::spanned(span, error)])
    }
}

test_parse_error! {
    incomplete_alternative,
    r#"
    match 1 with
    | //
    "#,
    |arena| case(arena, int(1), vec![(Pattern::Error, error())]),
    {

        let error = Error::UnexpectedToken(Token::CloseBlock, vec![]);
        let span = pos::span(BytePos::from(0), BytePos::from(0));
        ParseErrors::from(vec![pos::spanned(span, error)])
    }
}

test_parse_error! {
    incomplete_alternative_before_complete_alternative,
    r#"
    match 1 with
    | //
    | x -> x
    "#,
    |arena| case(arena,
            int(1),
            vec![
                (Pattern::Error, error()),
                (Pattern::Ident(TypedIdent::new(intern("x"))), id("x")),
            ],
        ),
    {
        let error = Error::UnexpectedToken(Token::Pipe, vec![]);
        let span = pos::span(BytePos::from(0), BytePos::from(0));
        ParseErrors::from(vec![pos::spanned(span, error)])
    }
}

test_parse_error! {
    incomplete_alternative_with_partial_pattern,
    r#"
    match 1 with
    | { x = }
    "#,
    |arena| case(arena,
            int(1),
            vec![(
                Pattern::Record {
                    typ: Type::hole(),
                    fields: arena.alloc_extend(vec![PatternField::Value {
                        name: no_loc(intern("x")),
                        value: Some(no_loc(Pattern::Error)),
                    }]),
                    implicit_import: None,
                },
                error(),
            )],
        ),
    vec![
        no_loc(Error::UnexpectedToken(Token::RBrace, vec![])),
        no_loc(Error::UnexpectedToken(Token::CloseBlock, vec![])),
    ],
}

test_parse_error! {
    incomplete_let_binding,
    r#"
    let test =
    1
    "#,
    |arena| let_(arena, "test", no_loc(Expr::Error(None)), int(1),),
    vec![no_loc(Error::UnexpectedToken(Token::CloseBlock, vec![]))]
}

test_parse_error! {
    incomplete_let_binding_2,
    r#"
    let test = io
    "#,
    |arena| let_(arena, "test", id("io"), no_loc(Expr::Error(None))),
    vec![no_loc(Error::UnexpectedToken(Token::CloseBlock, vec![]))],
}

test_parse_error! {
    incomplete_let_binding_3,
    r#"
    let test
    1
    "#,
    |arena| let_(arena, "test", no_loc(Expr::Error(None)), int(1),),
    vec![no_loc(Error::UnexpectedToken(Token::In, vec![]))],
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
    let span = pos::span(BytePos::from(6), BytePos::from(8));
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

    let error = Error::UnexpectedEof([")", ","].iter().map(|s| s.to_string()).collect());
    let span = pos::span(BytePos::from(30), BytePos::from(30));
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

test_parse_error! {
error_in_do_1,
        r#"
do x
1
"#,
    |arena| do_(arena, "x", no_loc(Expr::Error(None)), int(1)),
    vec![no_loc(Error::UnexpectedToken(Token::In, vec![]))],
}

#[test]
fn error_in_do_2() {
    let _ = ::env_logger::try_init();

    let result = parse(
        r#"
do
1
"#,
    );

    let e = clear_span(result.unwrap_err().0.expect("Expression"));
    mk_ast_arena!(arena);
    assert_eq!(
        *e.expr(),
        do_2(
            arena.borrow(),
            Some(no_loc(Pattern::Error)),
            no_loc(Expr::Error(None)),
            int(1),
        )
    );
}
