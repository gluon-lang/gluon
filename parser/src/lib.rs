//! The parser is a bit more complex than it needs to be as it needs to be fully specialized to
//! avoid a recompilation every time a later part of the compiler is changed. Due to this the
//! string interner and therefore also garbage collector needs to compiled before the parser.

#[macro_use]
extern crate log;
#[macro_use]
extern crate quick_error;
extern crate gluon_base as base;
extern crate combine;
extern crate combine_language;
extern crate lalrpop_util;

use std::error::Error as StdError;
use std::fmt;

use base::ast::{Expr, IdentEnv, SpannedExpr};
use base::error::Errors;
use base::pos::{self, BytePos, Spanned};
use base::symbol::Symbol;
use base::types::ArcType;

use combine::primitives::{StreamOnce, Error as CombineError};

use infix::{OpTable, Reparser};
use lexer::{Lexer, Token};

mod grammar;
mod infix;
mod lexer;

type LalrpopError<'input> = lalrpop_util::ParseError<BytePos,
                                                     Token<&'input str>,
                                                     CombineError<String, String>>;

/// Shrink hidden spans to fit the visible expressions and flatten singleton blocks.
fn shrink_hidden_spans<Id>(mut expr: SpannedExpr<Id>) -> SpannedExpr<Id> {
    match expr.value {
        Expr::IfElse(_, _, ref last) |
        Expr::LetBindings(_, ref last) |
        Expr::TypeBindings(_, ref last) => expr.span.end = last.span.end,
        Expr::Lambda(ref lambda) => expr.span.end = lambda.body.span.end,
        Expr::Block(ref mut exprs) => {
            match exprs.len() {
                0 => (),
                1 => return exprs.pop().unwrap(),
                _ => expr.span.end = exprs.last().unwrap().span.end,
            }
        }
        Expr::Match(_, ref alts) => {
            if let Some(last_alt) = alts.last() {
                let end = last_alt.expr.span.end;
                expr.span.end = end;
            }
        }
        Expr::App(_, _) |
        Expr::Ident(_) |
        Expr::Literal(_) |
        Expr::Projection(_, _, _) |
        Expr::Infix(_, _, _) |
        Expr::Array(_) |
        Expr::Record { .. } |
        Expr::Tuple(_) => (),
    }
    expr
}

#[derive(Debug, PartialEq)]
pub struct ParseError {
    pub errors: Vec<CombineError<String, String>>,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        CombineError::fmt_errors(&self.errors, f)
    }
}

impl StdError for ParseError {
    fn description(&self) -> &str {
        "Parse error"
    }
}

fn transform_lalrpop_error(err: LalrpopError) -> Spanned<CombineError<String, String>, BytePos> {
    use lalrpop_util::ParseError::*;
    match err {
        InvalidToken { location } => {
            pos::spanned2(location,
                          location,
                          CombineError::Message("Invalid token".into()))
        }
        UnrecognizedToken { token, .. } => {
            match token {
                Some(token) => {
                    pos::spanned2(token.0,
                                  token.2,
                                  CombineError::Unexpected(format!("{}", token.1).into()))
                }
                None => {
                    pos::spanned2(0.into(),
                                  0.into(),
                                  CombineError::Unexpected("Unrecognized token".into()))
                }
            }
        }
        ExtraToken { token } => {
            pos::spanned2(token.0,
                          token.2,
                          CombineError::Message(format!("Found an extra token `{}`", token.1)
                              .into()))
        }
        User { error } => pos::spanned2(0.into(), 0.into(), error),
    }
}

fn transform_errors(errors: Vec<LalrpopError>) -> Vec<Error> {
    errors.into_iter()
        .map(|err| {
            let Spanned { span, value: err } = transform_lalrpop_error(err);
            let err = ParseError { errors: vec![err] };
            Error::Parser(pos::spanned(span, err))
        })
        .collect()
}

quick_error! {
    #[derive(Debug, PartialEq)]
    pub enum Error {
        Parser(err: Spanned<ParseError, BytePos>) {
            description(err.value.description())
            display("{}", err)
            from()
        }
        Infix(err: infix::ReparseError) {
            description(err.description())
            display("{}", err)
            from()
        }
    }
}

// Dummy type for ParseError which has the correct associated types
#[derive(Clone)]
pub struct StreamType(());

impl StreamOnce for StreamType {
    type Item = String;
    type Range = String;
    type Position = BytePos;

    fn uncons(&mut self) -> Result<String, CombineError<String, String>> {
        unimplemented!()
    }

    fn position(&self) -> Self::Position {
        unimplemented!()
    }
}

pub enum FieldPattern<Id> {
    Type(Id, Option<Id>),
    Value(Id, Option<Id>),
}

pub enum FieldExpr<Id> {
    Type(Id, Option<ArcType<Id>>),
    Value(Id, Option<SpannedExpr<Id>>),
}

// Hack around LALRPOP's limited type syntax
type MutIdentEnv<'env, Id> = &'env mut IdentEnv<Ident = Id>;
type ErrorEnv<'err, 'input> = &'err mut Errors<lalrpop_util::ParseError<BytePos,
                                                                        Token<&'input str>,
                                                                        CombineError<String,
                                                                                     String>>>;

pub fn parse_partial_expr<Id>
    (symbols: &mut IdentEnv<Ident = Id>,
     input: &str)
     -> Result<SpannedExpr<Id>, (Option<SpannedExpr<Id>>, Errors<Error>)>
    where Id: Clone,
{
    let lexer = Lexer::new(input);
    let mut parse_errors = Errors::new();

    match grammar::parse_TopExpr(input, symbols, &mut parse_errors, lexer) {
        // TODO: handle errors
        Ok(mut expr) => {
            let mut errors = Errors { errors: transform_errors(parse_errors.errors) };
            let mut reparser = Reparser::new(OpTable::default(), symbols);
            if let Err(reparse_errors) = reparser.reparse(&mut expr) {
                errors.errors.extend(reparse_errors.errors.into_iter().map(Error::Infix));
            }
            if errors.has_errors() {
                Err((Some(expr), errors))
            } else {
                Ok(expr)
            }
        }
        Err(err) => {
            parse_errors.error(err);
            Err((None, Errors { errors: transform_errors(parse_errors.errors) }))
        }
    }
}

pub fn parse_expr(symbols: &mut IdentEnv<Ident = Symbol>,
                  input: &str)
                  -> Result<SpannedExpr<Symbol>, Errors<Error>> {
    parse_partial_expr(symbols, input).map_err(|t| t.1)
}

#[cfg(feature = "test")]
pub fn parse_string<'env, 'input>
    (symbols: &'env mut IdentEnv<Ident = String>,
     input: &'input str)
     -> Result<SpannedExpr<String>, (Option<SpannedExpr<String>>, Errors<Error>)> {
    parse_partial_expr(symbols, input)
}
