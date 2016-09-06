#![feature(test)]

extern crate test;

extern crate gluon_base as base;
extern crate gluon_parser as parser;

use base::symbol::{Symbols, SymbolModule};

#[bench]
fn prelude(b: &mut ::test::Bencher) {
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
        let expr = parser::parse_expr(&mut symbols, &text)
            .unwrap_or_else(|(_, err)| panic!("{:?}", err));
        ::test::black_box(expr)
    })
}
