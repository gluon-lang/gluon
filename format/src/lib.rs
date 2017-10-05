//! Code formatter.
#![doc(html_root_url = "https://docs.rs/gluon_formatter/0.5.0")] // # GLUON

extern crate gluon_base as base;
extern crate gluon_parser as parser;
extern crate pretty;

use parser::ParseErrors;

pub fn format_expr(input: &str) -> Result<String, ParseErrors> {
    use pretty::Arena;

    use base::pretty_print::Printer;
    use base::source::Source;
    use base::symbol::Symbols;
    use base::types::TypeCache;
    use parser::parse_expr;

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
    let expr = parse_expr(&mut Symbols::new(), &type_cache, input)?;

    let source = Source::new(input);
    let arena = Arena::new();
    let printer = Printer::new(&arena, &source);
    Ok(printer.format(100, newline, &expr))
}
