#[macro_use]
extern crate bencher;

extern crate gluon_base as base;
extern crate gluon_parser as parser;

use bencher::{Bencher, black_box};

use base::symbol::{Symbols, SymbolModule};
use base::types::TypeCache;

fn prelude(b: &mut Bencher) {
    use std::fs::File;
    use std::io::Read;
    let mut text = String::new();
    File::open("std/prelude.glu")
        .unwrap()
        .read_to_string(&mut text)
        .unwrap();
    b.iter(|| {
        let mut symbols = Symbols::new();
        let mut symbols = SymbolModule::new("".into(), &mut symbols);
        let expr = parser::parse_expr(&mut symbols, &TypeCache::new(), &text)
            .unwrap_or_else(|err| panic!("{:?}", err));
        black_box(expr)
    })
}

benchmark_group!(parser, prelude);
benchmark_main!(parser);
