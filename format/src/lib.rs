//! Code formatter.
#![doc(html_root_url = "https://docs.rs/gluon_formatter/0.7.1")] // # GLUON

#[macro_use]
extern crate gluon_base as base;
extern crate gluon_parser as parser;
extern crate itertools;
extern crate pretty;

use base::ast::SpannedExpr;
use base::source::Source;
use base::symbol::{Symbol, Symbols};
use base::types::TypeCache;

mod pretty_print;

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

pub fn format_expr(input: &str) -> Result<String, parser::ParseErrors> {
    let type_cache = TypeCache::new();
    let expr = parser::parse_expr(&mut Symbols::new(), &type_cache, input)?;

    Ok(pretty_expr(input, &expr))
}
