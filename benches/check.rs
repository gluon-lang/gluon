#[macro_use]
extern crate criterion;
extern crate env_logger;

extern crate gluon;
extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_parser as parser;

use std::fs;

use criterion::{Bencher, Criterion};

use gluon::{compiler_pipeline::*, new_vm, Compiler};

fn typecheck_prelude(b: &mut Bencher) {
    let vm = new_vm();
    let compiler = Compiler::new();
    let MacroValue { expr } = {
        let text = fs::read_to_string("std/prelude.glu").unwrap();
        text.expand_macro(&mut compiler.module_compiler(), &vm, "std.prelude", &text)
            .unwrap_or_else(|(_, err)| panic!("{}", err))
    };
    b.iter(|| {
        let result = MacroValue { expr: expr.clone() }.typecheck(
            &mut compiler.module_compiler(),
            &vm,
            "<top>",
            "",
        );
        if let Err(ref err) = result {
            println!("{}", err);
            assert!(false);
        }
        result
    })
}

fn clone_prelude(b: &mut Bencher) {
    let vm = new_vm();
    let compiler = Compiler::new();
    let TypecheckValue { expr, .. } = {
        let text = fs::read_to_string("std/prelude.glu").unwrap();
        text.typecheck(&mut compiler.module_compiler(), &vm, "std.prelude", &text)
            .unwrap_or_else(|err| panic!("{}", err))
    };
    b.iter(|| expr.clone())
}

fn typecheck_24(b: &mut Bencher) {
    let vm = new_vm();
    let compiler = Compiler::new();
    let MacroValue { expr } = {
        let text = fs::read_to_string("examples/24.glu").unwrap();
        text.expand_macro(&mut compiler.module_compiler(), &vm, "examples.24", &text)
            .unwrap_or_else(|(_, err)| panic!("{}", err))
    };
    b.iter(|| {
        let result = MacroValue { expr: expr.clone() }.typecheck(
            &mut compiler.module_compiler(),
            &vm,
            "<top>",
            "",
        );
        if let Err(ref err) = result {
            println!("{}", err);
            assert!(false);
        }
        result
    })
}

fn typecheck_file(b: &mut Bencher, file: &str) {
    let vm = new_vm();
    let compiler = Compiler::new();
    let reparsed = {
        let text = fs::read_to_string(file).unwrap();
        text.reparse_infix(
            &mut compiler.module_compiler(),
            &vm,
            &base::filename_to_module(file),
            &text,
        )
        .unwrap_or_else(|(_, err)| panic!("{}", err))
    };
    let InfixReparsed {
        metadata,
        metadata_map,
        expr,
    } = &reparsed;
    b.iter_with_setup(
        || InfixReparsed {
            metadata: metadata.clone(),
            metadata_map: metadata_map.clone(),
            expr: expr.clone(),
        },
        |input| {
            let result = input.typecheck(&mut compiler.module_compiler(), &vm, "<top>", "");
            if let Err(ref err) = result {
                println!("{}", err);
                assert!(false);
            }
            result
        },
    )
}

fn clone_benchmark(c: &mut Criterion) {
    let _ = env_logger::try_init();

    c.bench_function("clone prelude", clone_prelude);
}

fn typecheck_benchmark(c: &mut Criterion) {
    let _ = env_logger::try_init();

    c.bench_function("std/prelude", typecheck_prelude);
    c.bench_function("examples/24", typecheck_24);

    c.bench_function("typecheck_only_24", move |b| {
        typecheck_file(b, "examples/24.glu")
    });

    c.bench_function("compile_lisp", move |b| {
        b.iter(|| {
            let vm = new_vm();
            let mut compiler = Compiler::new();
            compiler
                .load_file(&vm, "examples/lisp/lisp.glu")
                .unwrap_or_else(|err| panic!("{}", err))
        })
    });
}

criterion_group!(
    name = check;
    config = Criterion::default().sample_size(20).configure_from_args();
    targets = typecheck_benchmark, clone_benchmark
);
criterion_main!(check);
