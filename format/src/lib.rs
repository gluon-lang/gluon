//! Code formatter.
#![doc(html_root_url = "https://docs.rs/gluon_formatter/0.5.0")] // # GLUON

extern crate pretty;
extern crate gluon_base as base;
extern crate gluon_parser as parser;

use pretty::Arena;

use base::source::Source;
use parser::ParseErrors;

struct Printer<'a: 'e, 'e>(base::types::Printer<'a, 'e>);

impl<'a: 'e, 'e> Printer<'a, 'e> {
    fn new(arena: &'a Arena<'a>, source: &'e Source<'a>) -> Self {
        Printer(base::types::Printer { arena, source })
    }
}

impl<'a: 'e, 'e> std::ops::Deref for Printer<'a, 'e> {
    type Target = base::types::Printer<'a, 'e>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub fn format_expr(input: &str) -> Result<String, ParseErrors> {
    use pretty::Arena;

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
