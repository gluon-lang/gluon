extern crate gluon_base as base;
extern crate gluon_parser as parser;

use std::fs;

use criterion::{criterion_group, criterion_main, Bencher, Criterion};

use crate::base::{
    symbol::{SymbolModule, Symbols},
    types::TypeCache,
};

fn parse_file(b: &mut Bencher, file: &str) {
    let text = fs::read_to_string(file).unwrap();

    b.iter(|| {
        let mut symbols = Symbols::new();
        let mut symbols = SymbolModule::new("".into(), &mut symbols);
        parser::parse_expr(&mut symbols, &TypeCache::default(), &text)
            .unwrap_or_else(|err| panic!("{:?}", err))
    })
}

fn parse_benchmark(c: &mut Criterion) {
    c.bench_function("std/prelude", |b| parse_file(b, "../std/prelude.glu"));
    c.bench_function("examples/lisp", |b| {
        parse_file(b, "../examples/lisp/lisp.glu")
    });
    c.bench_function("examples/http", |b| {
        parse_file(b, "../examples/http/server.glu")
    });
}

criterion_group!(parser, parse_benchmark);
criterion_main!(parser);
