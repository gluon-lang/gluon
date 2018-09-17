//! Code formatter.
#![doc(html_root_url = "https://docs.rs/gluon_formatter/0.9.0")] // # GLUON

extern crate codespan;
extern crate gluon;
#[macro_use]
extern crate gluon_base as base;
extern crate itertools;
extern crate pretty;

use gluon::compiler_pipeline::*;
use gluon::{Compiler, Error, Result, Thread};

use base::ast::{self, SpannedExpr};
use base::pos::{BytePos, Span};
use base::symbol::Symbol;

mod pretty_print;

fn has_format_disabling_errors(file: &codespan::FileName, err: &Error) -> bool {
    match *err {
        Error::Multiple(ref errors) => errors
            .iter()
            .any(|err| has_format_disabling_errors(file, err)),
        Error::Parse(ref err) => err.source_name() == file,
        _ => false,
    }
}

pub fn pretty_expr(input: &str, expr: &SpannedExpr<Symbol>) -> String {
    Formatter::default().pretty_expr(input, expr)
}

pub fn format_expr(
    compiler: &mut Compiler,
    thread: &Thread,
    file: &str,
    input: &str,
) -> Result<String> {
    Formatter::default().format_expr(compiler, thread, file, input)
}

#[derive(Default, Debug, Clone)]
pub struct Formatter {
    /// Prints the source code after macro expansion
    ///
    /// NOTE: This is only provided for debug purposes and is likely to have have bugs
    pub expanded: bool,
}

impl Formatter {
    pub fn pretty_expr(&self, input: &str, expr: &SpannedExpr<Symbol>) -> String {
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

        let source = codespan::FileMap::new("test".into(), input.into());
        let arena = pretty::Arena::<()>::new();
        let printer = pretty_print::Printer::new(&arena, &source, self.clone());
        printer.format(100, newline, &expr)
    }

    pub fn format_expr(
        &self,
        compiler: &mut Compiler,
        thread: &Thread,
        file: &str,
        input: &str,
    ) -> Result<String> {
        let expr = match input.reparse_infix(compiler, thread, file, input) {
            Ok(expr) => expr.expr,
            Err((Some(expr), err)) => {
                if has_format_disabling_errors(&codespan::FileName::from(file.to_string()), &err) {
                    return Err(err);
                }
                expr.expr
            }
            Err((None, err)) => return Err(err),
        };

        fn skip_implicit_prelude(
            span: Span<BytePos>,
            l: &SpannedExpr<Symbol>,
        ) -> &SpannedExpr<Symbol> {
            match l.value {
                ast::Expr::LetBindings(_, ref e) if !span.contains(l.span) => {
                    skip_implicit_prelude(span, e)
                }
                _ => l,
            }
        }

        let file_map = compiler.get_filemap(file).unwrap();
        Ok(self.pretty_expr(input, skip_implicit_prelude(file_map.span(), &expr)))
    }
}
