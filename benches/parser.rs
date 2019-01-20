#[macro_use]
extern crate criterion;

extern crate gluon_base as base;
extern crate gluon_parser as parser;

use criterion::{Bencher, Criterion};

use crate::base::symbol::{SymbolModule, Symbols};
use crate::base::types::TypeCache;

fn parse_prelude(b: &mut Bencher) {
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
        parser::parse_expr(&mut symbols, &TypeCache::default(), &text)
            .unwrap_or_else(|err| panic!("{:?}", err))
    })
}

fn parse_benchmark(c: &mut Criterion) {
    c.bench_function("std/prelude", parse_prelude);
}

criterion_group!(parser, parse_benchmark);
criterion_main!(parser);
