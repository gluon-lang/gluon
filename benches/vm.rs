#![feature(test)]

extern crate test;

extern crate base;
extern crate parser;
extern crate check;
extern crate vm;

use std::fs::File;
use std::io::Read;

use base::symbol::SymbolModule;
use check::typecheck::Typecheck;
use vm::vm::VM;

#[bench]
fn prelude(b: &mut ::test::Bencher) {
    let vm = VM::new();
    let env = vm.env();
    let mut symbols = vm.get_mut_symbols();
    let expr = {
        let mut symbols = SymbolModule::new("".into(), &mut symbols);
        let mut text = String::new();
        File::open("std/prelude.hs").unwrap().read_to_string(&mut text).unwrap();
        ::parser::parse_tc(&mut symbols, &text)
                       .unwrap_or_else(|err| panic!("{:?}", err))
    };
    b.iter(|| {
        let mut tc = Typecheck::new("".into(), &mut symbols);
        tc.add_environment(&env);
        let result = tc.typecheck_expr(&mut expr.clone());
        if let Err(ref err) = result {
            println!("{}", err);
            assert!(false);
        }
        ::test::black_box(result)
    })
}
