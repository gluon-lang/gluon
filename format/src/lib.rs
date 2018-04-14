//! Code formatter.
#![doc(html_root_url = "https://docs.rs/gluon_formatter/0.7.1")] // # GLUON

#[macro_use]
extern crate gluon_base as base;
extern crate gluon;
extern crate itertools;
extern crate pretty;

use gluon::{Compiler, Error, Thread, Result};
use gluon::compiler_pipeline::*;

use base::ast::{self, SpannedExpr};
use base::pos::UNKNOWN_EXPANSION;
use base::source::Source;
use base::symbol::Symbol;

mod pretty_print;

fn has_format_disabling_errors(file: &str, err: &Error) -> bool {
    match *err {
        Error::Multiple(ref errors) => errors.iter().any(|err| has_format_disabling_errors(file, err)),
        Error::Parse(ref err) => err.source_name == file,
        _ => false,
    }
}

pub fn pretty_expr(input: &str, expr: &SpannedExpr<Symbol>) -> String {
    let newline = match input.find(|c: char| c == '\n' || c == '\r') {
        Some(i) => {
            if input[i..].starts_with("\r\n") {
                "\r\n"
            } else if input[i..].starts_with("\r") {
                "\r"
            } else {
                "\n"
            }
        }
        None => "\n",
    };

    let source = Source::new(input);
    let arena = pretty::Arena::new();
    let printer = pretty_print::Printer::new(&arena, &source);
    printer.format(100, newline, &expr)
}

pub fn format_expr(compiler: &mut Compiler, thread: &Thread, file: &str, input: &str) -> Result<String> {
    let expr = match input.reparse_infix(compiler, thread, file, input) {
        Ok(expr) => expr.expr,
        Err((Some(expr), err)) => {
            if has_format_disabling_errors(file, &err) {
                return Err(err);
            }
            expr.expr
        }
        Err((None, err)) => return Err(err),
    };

    fn skip_implicit_prelude(l: &SpannedExpr<Symbol>) -> &SpannedExpr<Symbol> {
        match l.value {
            ast::Expr::LetBindings(_, ref e) if l.span.expansion_id == UNKNOWN_EXPANSION => {
                skip_implicit_prelude(e)
            }
            _ => l,
        }
    }

    Ok(pretty_expr(input, skip_implicit_prelude(&expr)))
}
