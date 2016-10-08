//! The parser is a bit more complex than it needs to be as it needs to be fully specialized to
//! avoid a recompilation every time a later part of the compiler is changed. Due to this the
//! string interner and therefore also garbage collector needs to compiled before the parser.

#[macro_use]
extern crate log;
extern crate gluon_base as base;
extern crate combine;
extern crate combine_language;

use std::fmt;

use base::ast::{IdentEnv, SpannedExpr};
use base::error::Errors;
use base::pos::{self, BytePos, Spanned};
use base::symbol::Symbol;
use base::types::ArcType;

use combine::primitives::{StreamOnce, Error as CombineError};

use infix::OpTable;
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

pub type Error = Errors<Spanned<ParseError, BytePos>>;

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

pub fn parse_expr(symbols: &mut IdentEnv<Ident = Symbol>,
                  input: &str)
                  -> Result<SpannedExpr<Symbol>, Error> {
    let lexer = Lexer::new(input);
    let operators = OpTable::default();

    match grammar::parse_TopExpr(input, symbols, lexer) {
        // TODO: handle errors
        Ok(expr) => Ok(infix::reparse(expr, symbols, &operators).unwrap()),
        Err(err) => {
            let err = ParseError { errors: vec![CombineError::Message(format!("{:?}", err).into())] };
            Err(Errors { errors: vec![pos::spanned2(BytePos::from(0), BytePos::from(0), err)] })
        }
    }
}

#[cfg(feature = "test")]
pub fn parse_string<'env, 'input>
    (symbols: &'env mut IdentEnv<Ident = String>,
     input: &'input str)
     -> Result<SpannedExpr<String>, (Option<SpannedExpr<String>>, Error)> {
    let lexer = Lexer::new(input);
    let operators = OpTable::default();

    match grammar::parse_TopExpr(input, symbols, lexer) {
        // TODO: handle errors
        Ok(expr) => Ok(infix::reparse(expr, symbols, &operators).unwrap()),
        Err(err) => {
            let err = ParseError { errors: vec![CombineError::Message(format!("{:?}", err).into())] };
            Err((None, Errors { errors: vec![pos::spanned2(BytePos::from(0), BytePos::from(0), err)] }))
        }
    }
}
