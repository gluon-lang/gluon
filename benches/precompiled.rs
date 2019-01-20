#[macro_use]
extern crate criterion;

extern crate gluon;

extern crate bincode;
extern crate futures;
extern crate serde_json;
extern crate serde_state;

use std::fs::File;
use std::io::Read;

use criterion::{Bencher, Criterion};

use futures::Future;
use gluon::compiler_pipeline::compile_to;
use gluon::{new_vm, Compiler};

fn precompiled_prelude(b: &mut Bencher) {
    let thread = new_vm();
    let prelude = {
        let mut out = String::new();
        File::open("std/prelude.glu")
            .unwrap()
            .read_to_string(&mut out)
            .unwrap();
        out
    };
    let mut serialized_prelude = Vec::new();
    {
        let mut serializer = serde_json::Serializer::new(&mut serialized_prelude);
        compile_to(
            &prelude[..],
            &mut Compiler::new(),
            &thread,
            "std.prelude",
            &prelude,
            None,
            &mut serializer,
        )
        .unwrap()
    }
    b.iter(|| {
        use gluon::compiler_pipeline::{Executable, Precompiled};

        let mut deserializer = serde_json::Deserializer::from_slice(&serialized_prelude);
        Precompiled(&mut deserializer)
            .run_expr(&mut Compiler::new(), &*thread, "std.prelude", "", ())
            .wait()
            .unwrap()
    })
}

fn source_prelude(b: &mut Bencher) {
    let mut prelude_source = String::new();
    File::open("std/prelude.glu")
        .and_then(|mut f| f.read_to_string(&mut prelude_source))
        .unwrap();
    let thread = new_vm();

    b.iter(|| {
        use gluon::compiler_pipeline::Executable;

        prelude_source
            .run_expr(
                &mut Compiler::new(),
                &*thread,
                "std.prelude",
                &prelude_source,
                None,
            )
            .wait()
            .unwrap()
    })
}

fn precompiled_benchmark(c: &mut Criterion) {
    c.bench_function("source std/prelude", source_prelude);
    c.bench_function("precompiled std/prelude", precompiled_prelude);
}

criterion_group!(precompiled, precompiled_benchmark);
criterion_main!(precompiled);
