//! Code formatter.
#![doc(html_root_url = "https://docs.rs/gluon_formatter/0.6.1")] // # GLUON

extern crate itertools;
extern crate pretty;
#[macro_use]
extern crate gluon_base as base;
extern crate gluon_parser as parser;

mod pretty_print;

pub fn format_expr(input: &str) -> Result<String, parser::ParseErrors> {
    use base::source::Source;
    use base::symbol::Symbols;
    use base::types::TypeCache;

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

    let type_cache = TypeCache::new();
    let expr = parser::parse_expr(&mut Symbols::new(), &type_cache, input)?;

    let source = Source::new(input);
    let arena = pretty::Arena::new();
    let printer = pretty_print::Printer::new(&arena, &source);
    Ok(printer.format(100, newline, &expr))
}
