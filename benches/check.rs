#[macro_use]
extern crate bencher;

extern crate gluon;
extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_parser as parser;

use std::fs::File;
use std::io::Read;

use bencher::{black_box, Bencher};

use gluon::{new_vm, Compiler};
use gluon::compiler_pipeline::*;

fn typecheck_prelude(b: &mut Bencher) {
    let vm = new_vm();
    let mut compiler = Compiler::new();
    let MacroValue { expr } = {
        let mut text = String::new();
        File::open("std/prelude.glu")
            .unwrap()
            .read_to_string(&mut text)
            .unwrap();
        text.expand_macro(&mut compiler, &vm, "std.prelude", &text)
            .unwrap_or_else(|(_, err)| panic!("{}", err))
    };
    b.iter(|| {
        let result = MacroValue { expr: expr.clone() }.typecheck(&mut compiler, &vm, "<top>", "");
        if let Err(ref err) = result {
            println!("{}", err);
            assert!(false);
        }
        black_box(result)
    })
}

fn clone_prelude(b: &mut Bencher) {
    let vm = new_vm();
    let mut compiler = Compiler::new();
    let TypecheckValue { expr, .. } = {
        let mut text = String::new();
        File::open("std/prelude.glu")
            .unwrap()
            .read_to_string(&mut text)
            .unwrap();
        text.typecheck(&mut compiler, &vm, "std.prelude", &text)
            .unwrap_or_else(|err| panic!("{}", err))
    };
    b.iter(|| black_box(expr.clone()))
}

benchmark_group!(check, typecheck_prelude, clone_prelude);
benchmark_main!(check);
