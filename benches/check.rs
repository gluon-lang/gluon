#![feature(test)]

extern crate test;

extern crate gluon_base as base;
extern crate gluon_parser as parser;
extern crate gluon_check as check;
extern crate gluon;

use std::fs::File;
use std::io::Read;

use base::symbol::{Symbols, SymbolModule};
use check::typecheck::Typecheck;
use gluon::new_vm;

#[bench]
fn prelude(b: &mut ::test::Bencher) {
    let vm = new_vm();
    let env = vm.get_env();
    let mut symbols = Symbols::new();
    let mut expr = {
        let mut symbols = SymbolModule::new("".into(), &mut symbols);
        let mut text = String::new();
        File::open("std/prelude.glu").unwrap().read_to_string(&mut text).unwrap();
        ::parser::parse_tc(&mut symbols, &text).unwrap_or_else(|err| panic!("{}", err))
    };
    vm.get_macros().run(&vm, &mut expr).unwrap();
    b.iter(|| {
        let mut tc = Typecheck::new("".into(), &mut symbols, &*env);
        let result = tc.typecheck_expr(&mut expr.clone());
        if let Err(ref err) = result {
            println!("{}", err);
            assert!(false);
        }
        ::test::black_box(result)
    })
}

#[bench]
fn clone_prelude(b: &mut ::test::Bencher) {
    let vm = new_vm();
    let env = vm.get_env();
    let mut symbols = Symbols::new();
    let mut expr = {
        let mut symbols = SymbolModule::new("".into(), &mut symbols);
        let mut text = String::new();
        File::open("std/prelude.glu").unwrap().read_to_string(&mut text).unwrap();
        ::parser::parse_tc(&mut symbols, &text).unwrap_or_else(|err| panic!("{}", err))
    };
    vm.get_macros().run(&vm, &mut expr).unwrap();
    let mut tc = Typecheck::new("".into(), &mut symbols, &*env);
    tc.typecheck_expr(&mut expr).unwrap_or_else(|err| panic!("{}", err));
    b.iter(|| {
        ::test::black_box(expr.clone())
    })
}
