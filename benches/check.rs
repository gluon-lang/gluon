use std::{cell::RefCell, fs};

use criterion::{criterion_group, criterion_main, Bencher, Criterion};

use gluon::{base, compiler_pipeline::*, new_vm, ThreadExt};

fn typecheck_prelude(b: &mut Bencher) {
    let vm = new_vm();
    let text = fs::read_to_string("std/prelude.glu").unwrap();
    b.iter_with_setup(
        || {
            let MacroValue { expr } = futures::executor::block_on(text.expand_macro(
                &mut vm.module_compiler(&mut vm.get_database()),
                &vm,
                "std.prelude",
                &text,
            ))
            .unwrap_or_else(|err| panic!("{}", err));
            expr
        },
        |expr| {
            let result = futures::executor::block_on(MacroValue { expr }.typecheck(
                &mut vm.module_compiler(&mut vm.get_database()),
                &vm,
                "std.prelude",
                &text,
            ));
            if let Err(err) = &result {
                println!("{}", err);
                assert!(false);
            }
            result
        },
    )
}

fn typecheck_24(b: &mut Bencher) {
    let vm = new_vm();
    let text = fs::read_to_string("examples/24.glu").unwrap();
    let mut db = vm.get_database();
    let compiler = RefCell::new(vm.module_compiler(&mut db));
    b.iter_with_setup(
        || {
            futures::executor::block_on(text.expand_macro(
                &mut compiler.borrow_mut(),
                &vm,
                "examples.24",
                &text,
            ))
            .unwrap_or_else(|err| panic!("{}", err))
        },
        |input| {
            let result = futures::executor::block_on(input.typecheck(
                &mut compiler.borrow_mut(),
                &vm,
                "examples.24",
                &text,
            ));
            if let Err(err) = &result {
                println!("{}", err);
                assert!(false);
            }
            result
        },
    )
}

fn typecheck_file(b: &mut Bencher, file: &str) {
    let vm = new_vm();
    let text = fs::read_to_string(file).unwrap();
    let module_name = base::filename_to_module(file);
    let mut db = vm.get_database();
    let compiler = RefCell::new(vm.module_compiler(&mut db));
    b.iter_with_setup(
        || {
            futures::executor::block_on(text.reparse_infix(
                &mut compiler.borrow_mut(),
                &vm,
                &module_name,
                &text,
            ))
            .unwrap_or_else(|err| panic!("{}", err))
        },
        |input| {
            let result = futures::executor::block_on(input.typecheck(
                &mut compiler.borrow_mut(),
                &vm,
                &module_name,
                &text,
            ));
            if let Err(err) = &result {
                println!("{}", err);
                assert!(false);
            }
            result
        },
    )
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
            vm.load_file("examples/lisp/lisp.glu")
                .unwrap_or_else(|err| panic!("{}", err))
        })
    });
}

criterion_group!(
    name = check;
    config = Criterion::default().sample_size(20).configure_from_args();
    targets = typecheck_benchmark
);
criterion_main!(check);
