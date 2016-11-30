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
use base::pos::{self, BytePos, Column, Line, Location, Spanned};
use base::symbol::Symbol;
use base::types::ArcType;

use infix::{OpTable, Reparser, Error as InfixError};
use layout::{LayoutContext, Error as LayoutError};
use token::{SpannedToken, Token, Tokenizer, Error as TokenizeError};

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
        Token(err: TokenizeError) {
            description(err.description())
            display("{}", err)
            from()
        }
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
        Infix(err: InfixError) {
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

struct Lexer<'input> {
    tokenizer: Tokenizer<'input>,
    layout: LayoutContext<'input>,
}

impl<'input> Lexer<'input> {
    fn new(input: &'input str) -> Lexer<'input> {
        Lexer {
            tokenizer: Tokenizer::new(input),
            layout: LayoutContext::new(),
        }
    }

    fn next_spanned(&mut self) -> Option<Result<SpannedToken<'input>, Error>> {
        match self.layout.next() {
            Err(err) => Some(Err(Error::Layout(err))),
            Ok(Some(Spanned { value: Token::EOF, .. })) => None,
            Ok(Some(token)) => Some(Ok(token)),
            Ok(None) => {
                match self.tokenizer.next() {
                    Some(Ok(token)) => {
                        self.layout.push(token);
                        self.next_spanned()
                    }
                    Some(Err(err)) => Some(Err(Error::Token(err))),
                    None => {
                        // Blegh
                        let location = Location {
                            line: Line::from(0),
                            column: Column::from(0),
                            absolute: BytePos::from(0),
                        };
                        let token = pos::spanned2(location, location, Token::EOF);
                        self.layout.push(token);
                        self.next_spanned()
                    }
                }
            }
        }
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Result<(BytePos, Token<'input>, BytePos), Error>;

    fn next(&mut self) -> Option<Result<(BytePos, Token<'input>, BytePos), Error>> {
        self.next_spanned().map(|token| {
            token.map(|token| {
                let start = token.span.start.absolute;
                let end = token.span.end.absolute;
                let token = token.value;

                (start, token, end)
            })
        })
    }
}

pub fn parse_partial_expr<Id>(symbols: &mut IdentEnv<Ident = Id>,
                              input: &str)
                              -> Result<SpannedExpr<Id>, (Option<SpannedExpr<Id>>, ParseErrors)>
    where Id: Clone,
{
    let mut parse_errors = Errors::new();
    let lexer = Lexer::new(input);

    match grammar::parse_TopExpr(input, symbols, &mut parse_errors, lexer) {
        Ok(mut expr) => {
            let mut errors = transform_errors(parse_errors);
            let mut reparser = Reparser::new(OpTable::default(), symbols);

            if let Err(reparse_errors) = reparser.reparse(&mut expr) {
                errors.extend(reparse_errors.into_iter().map(|err| err.map(Error::Infix)));
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
