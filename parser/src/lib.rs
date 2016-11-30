//! The parser is a bit more complex than it needs to be as it needs to be fully specialized to
//! avoid a recompilation every time a later part of the compiler is changed. Due to this the
//! string interner and therefore also garbage collector needs to compiled before the parser.

#[macro_use]
extern crate log;
#[macro_use]
extern crate quick_error;
extern crate gluon_base as base;
extern crate lalrpop_util;

use base::ast::{Expr, IdentEnv, SpannedExpr};
use base::error::Errors;
use base::pos::{self, BytePos, Span, Spanned};
use base::symbol::Symbol;
use base::types::ArcType;

use infix::{OpTable, Reparser};
use layout::{Layout, Error as LayoutError};
use token::{Token, Tokenizer};

mod grammar;
mod infix;
mod layout;
mod token;

type LalrpopError<'input> = lalrpop_util::ParseError<BytePos, Token<'input>, Error>;

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

fn transform_errors<'a, Iter>(errors: Iter) -> Errors<Spanned<Error, BytePos>>
    where Iter: IntoIterator<Item = LalrpopError<'a>>,
{
    errors.into_iter()
        .map(Error::from_lalrpop)
        .collect()
}

quick_error! {
    #[derive(Debug, PartialEq)]
    pub enum Error {
        Layout(err: LayoutError) {
            description(err.description())
            display("{}", err)
            from()
        }
        InvalidToken {
            description("invalid token")
            display("Invalid token")
        }
        UnexpectedToken(token: String) {
            description("unexpected token")
            display("Unexpected token: {}", token)
        }
        UnexpectedEof {
            description("unexpected end of file")
            display("Undexpected end of file")
        }
        ExtraToken(token: String) {
            description("extra token")
            display("Extra token: {}", token)
        }
        Infix(err: infix::ReparseError) {
            description(err.description())
            display("{}", err)
            from()
        }
    }
}

impl Error {
    fn from_lalrpop(err: LalrpopError) -> Spanned<Error, BytePos> {
        use lalrpop_util::ParseError::*;

        match err {
            InvalidToken { location } => pos::spanned2(location, location, Error::InvalidToken),
            UnrecognizedToken { token: Some((lpos, token, rpos)), .. } => {
                pos::spanned2(lpos, rpos, Error::UnexpectedToken(token.to_string()))
            }
            UnrecognizedToken { token: None, .. } => {
                pos::spanned2(0.into(), 0.into(), Error::UnexpectedEof)
            }
            ExtraToken { token: (lpos, token, rpos) } => {
                pos::spanned2(lpos, rpos, Error::ExtraToken(token.to_string()))
            }
            User { error } => pos::spanned2(0.into(), 0.into(), error),
        }
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
type ErrorEnv<'err, 'input> = &'err mut Errors<LalrpopError<'input>>;

pub type ParseErrors = Errors<Spanned<Error, BytePos>>;

pub fn parse_partial_expr<Id>(symbols: &mut IdentEnv<Ident = Id>,
                              input: &str)
                              -> Result<SpannedExpr<Id>, (Option<SpannedExpr<Id>>, ParseErrors)>
    where Id: Clone,
{
    let tokenizer = Tokenizer::new(input).map(|token| token.unwrap()); // FIXME

    let layout = Layout::new(tokenizer).map(|token| {
        let token = token?;
        debug!("Lex {:?}", token.value);
        let Span { start, end, .. } = token.span;
        Ok((start.absolute, token.value, end.absolute))
    });

    let mut parse_errors = Errors::new();

    match grammar::parse_TopExpr(input, symbols, &mut parse_errors, layout) {
        Ok(mut expr) => {
            let mut errors = transform_errors(parse_errors);
            let mut reparser = Reparser::new(OpTable::default(), symbols);
            if let Err(reparse_errors) = reparser.reparse(&mut expr) {
                errors.extend(reparse_errors.into_iter()
                        .map(|err| {
                            pos::spanned2(BytePos::from(0), BytePos::from(0), Error::Infix(err))
                        }));
            }
            if errors.has_errors() {
                Err((Some(expr), errors))
            } else {
                Ok(expr)
            }
        }
        Err(err) => {
            parse_errors.push(err);
            Err((None, transform_errors(parse_errors)))
        }
    }
}

pub fn parse_expr(symbols: &mut IdentEnv<Ident = Symbol>,
                  input: &str)
                  -> Result<SpannedExpr<Symbol>, ParseErrors> {
    parse_partial_expr(symbols, input).map_err(|t| t.1)
}

#[cfg(feature = "test")]
pub fn parse_string<'env, 'input>
    (symbols: &'env mut IdentEnv<Ident = String>,
     input: &'input str)
     -> Result<SpannedExpr<String>, (Option<SpannedExpr<String>>, ParseErrors)> {
    parse_partial_expr(symbols, input)
}
