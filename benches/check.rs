use std::fs;

use criterion::{criterion_group, criterion_main, Bencher, Criterion};

use gluon::{base, compiler_pipeline::*, new_vm, ThreadExt};

fn typecheck_prelude(b: &mut Bencher) {
    let vm = new_vm();
    let text = fs::read_to_string("std/prelude.glu").unwrap();
    let MacroValue { expr } = text
        .expand_macro(
            &mut vm.module_compiler(&vm.get_database()),
            &vm,
            "std.prelude",
            &text,
        )
        .unwrap_or_else(|(_, err)| panic!("{}", err));
    b.iter(|| {
        let result = MacroValue { expr: expr.clone() }.typecheck(
            &mut vm.module_compiler(&vm.get_database()),
            &vm,
            "std.prelude",
            &text,
        );
        if let Err((_, err)) = &result {
            println!("{}", err);
            assert!(false);
        }
        result
    })
}

fn clone_prelude(b: &mut Bencher) {
    let vm = new_vm();
    let TypecheckValue { expr, .. } = {
        let text = fs::read_to_string("std/prelude.glu").unwrap();
        text.typecheck(
            &mut vm.module_compiler(&vm.get_database()),
            &vm,
            "std.prelude",
            &text,
        )
        .unwrap_or_else(|(_, err)| panic!("{}", err))
    };
    b.iter(|| expr.clone())
}

fn typecheck_24(b: &mut Bencher) {
    let vm = new_vm();
    let text = fs::read_to_string("examples/24.glu").unwrap();
    let db = vm.get_database();
    let mut compiler = vm.module_compiler(&db);
    let MacroValue { expr } = text
        .expand_macro(&mut compiler, &vm, "examples.24", &text)
        .unwrap_or_else(|(_, err)| panic!("{}", err));
    b.iter_with_setup(
        || MacroValue { expr: expr.clone() },
        |input| {
            let result = input.typecheck(&mut compiler, &vm, "examples.24", &text);
            if let Err((_, err)) = &result {
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
    let db = vm.get_database();
    let mut compiler = vm.module_compiler(&db);
    let reparsed = text
        .reparse_infix(&mut compiler, &vm, &module_name, &text)
        .unwrap_or_else(|(_, err)| panic!("{}", err));
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
            let result = input.typecheck(&mut compiler, &vm, &module_name, &text);
            if let Err((_, err)) = &result {
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
            vm.load_file("examples/lisp/lisp.glu")
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
