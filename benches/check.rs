#![feature(test)]

extern crate test;

extern crate gluon_base as base;
extern crate gluon_parser as parser;
extern crate gluon_check as check;
extern crate gluon;

use std::fs::File;
use std::io::Read;

use gluon::{Compiler, new_vm};
use gluon::compiler_pipeline::*;

#[bench]
fn typecheck_prelude(b: &mut ::test::Bencher) {
    let vm = new_vm();
    let mut compiler = Compiler::new();
    let MacroValue { expr } = {
        let mut text = String::new();
        File::open("std/prelude.glu").unwrap().read_to_string(&mut text).unwrap();
        text.expand_macro(&mut compiler, &vm, "std.prelude").unwrap_or_else(|err| panic!("{}", err))
    };
    b.iter(|| {
        let result = MacroValue { expr: expr.clone() }.typecheck(&mut compiler, &vm, "<top>", "");
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
    let mut compiler = Compiler::new();
    let TypecheckValue { expr, .. } = {
        let mut text = String::new();
        File::open("std/prelude.glu").unwrap().read_to_string(&mut text).unwrap();
        text.typecheck(&mut compiler, &vm, "std.prelude", &text)
            .unwrap_or_else(|err| panic!("{}", err))
    };
    b.iter(|| ::test::black_box(expr.clone()))
}
