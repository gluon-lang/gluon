extern crate gluon_base as base;
extern crate gluon_parser as parser;

use std::fs;

use criterion::{criterion_group, criterion_main, Bencher, Criterion};

use crate::base::{
    ast, mk_ast_arena,
    symbol::{SymbolModule, Symbols},
    types::TypeCache,
};

fn parse_file(b: &mut Bencher, file: &str) {
    let text = fs::read_to_string(file).unwrap();

    b.iter(|| {
        let mut symbols = Symbols::new();
        let mut symbols = SymbolModule::new("".into(), &mut symbols);
        mk_ast_arena!(arena);
        let expr = parser::parse_expr(arena.borrow(), &mut symbols, &TypeCache::default(), &text)
            .unwrap_or_else(|err| panic!("{:?}", err));
        let expr = arena.alloc(expr);
        ast::RootExpr::new(arena.clone(), expr)
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
