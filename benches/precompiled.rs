#[macro_use]
extern crate bencher;

extern crate gluon;

extern crate bincode;
extern crate serde_state;

use std::fs::File;
use std::io::Read;

use bencher::{black_box, Bencher};

use serde_state::ser::SerializeState;

use gluon::{new_vm, Compiler, Future};
use gluon::vm::thread::ThreadInternal;
use gluon::vm::serialization::SeSeed;

fn precompiled_prelude(b: &mut Bencher) {
    let thread = new_vm();
    Compiler::new()
        .implicit_prelude(false)
        .load_file(&thread, "std/prelude.glu")
        .unwrap();
    let mut serialized_prelude = Vec::new();
    {
        let env = thread.global_env().get_env();
        let prelude = env.globals.get("std.prelude").unwrap();
        prelude
            .serialize_state(
                &mut bincode::Serializer::new(&mut serialized_prelude),
                &SeSeed::new(),
            )
            .unwrap();
    }
    b.iter(|| {
        use gluon::compiler_pipeline::{Executable, Precompiled};

        let mut deserializer = bincode::Deserializer::new(
            bincode::read_types::SliceReader::new(&serialized_prelude),
            bincode::Infinite,
        );
        let result = Precompiled(&mut deserializer)
            .run_expr(&mut Compiler::new(), &*thread, "std.prelude", "", ())
            .wait()
            .unwrap();
        black_box(result)
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

        let result = prelude_source
            .run_expr(
                &mut Compiler::new(),
                &*thread,
                "std.prelude",
                &prelude_source,
                None,
            )
            .wait()
            .unwrap();
        black_box(result)
    })
}

benchmark_group!(precompiled, precompiled_prelude, source_prelude);
benchmark_main!(precompiled);
