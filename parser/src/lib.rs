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

use std::error::Error as StdError;
use std::fmt;
use std::marker::PhantomData;

use base::ast::{IdentEnv, SpannedExpr};
use base::error::Errors;
use base::pos::{self, BytePos, Spanned};
use base::symbol::Symbol;
use base::types::ArcType;

use combine::primitives::{StreamOnce, Error as CombineError};

use infix::{OpTable, Reparser};
use lexer::Lexer;

mod grammar;
mod infix;
mod lexer;

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

fn parse_expr_<Id>(symbols: &mut IdentEnv<Ident = Id>,
                   input: &str)
                   -> Result<SpannedExpr<Id>, Errors<Error>>
    where Id: Clone,
{
    let lexer = Lexer::new(input);

    match grammar::parse_TopExpr(input, symbols, lexer) {
        // TODO: handle errors
        Ok(mut expr) => {
            let mut reparser = Reparser::new(OpTable::default(), symbols);
            if let Err(errors) = reparser.reparse(&mut expr) {
                return Err(Errors {
                    errors: errors.errors.into_iter().map(Error::Infix).collect(),
                });
            }
            Ok(expr)
        }
        Err(err) => {
            let err =
                ParseError { errors: vec![CombineError::Message(format!("{:?}", err).into())] };
            Err(Errors {
                errors: vec![Error::Parser(pos::spanned2(BytePos::from(0), BytePos::from(0), err))],
            })
        }
    }
}

pub fn parse_expr(symbols: &mut IdentEnv<Ident = Symbol>,
                  input: &str)
                  -> Result<SpannedExpr<Symbol>, Errors<Error>> {
    parse_expr_(symbols, input)
}

#[cfg(feature = "test")]
pub fn parse_string<'env, 'input>
    (symbols: &'env mut IdentEnv<Ident = String>,
     input: &'input str)
     -> Result<SpannedExpr<String>, (Option<SpannedExpr<String>>, Errors<Error>)> {
    parse_expr_(symbols, input).map_err(|err| (None, err))
}
