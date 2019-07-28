#![cfg(feature = "serialization")]
extern crate env_logger;
extern crate futures;
extern crate serde_json;
extern crate serde_state as serde;
extern crate walkdir;

extern crate gluon;

use std::{fs::File, io::Read};

use futures::Future;

use crate::serde::ser::SerializeState;

use gluon::{
    new_vm,
    vm::{
        api::{Hole, OpaqueValue, IO},
        serialization::{DeSeed, SeSeed},
        thread::{RootedThread, RootedValue, Thread},
        Variants,
    },
    Compiler,
};

fn serialize_value(value: Variants) {
    let mut buffer = Vec::new();
    {
        let mut ser = serde_json::Serializer::pretty(&mut buffer);
        let ser_state = SeSeed::new();
        value.serialize_state(&mut ser, &ser_state).unwrap();
    }
    String::from_utf8(buffer).unwrap();
}

fn roundtrip(
    thread: &RootedThread,
    value: &OpaqueValue<&Thread, Hole>,
) -> RootedValue<RootedThread> {
    use std::str::from_utf8;

    let value = value.get_variant();

    let mut buffer = Vec::new();
    {
        let mut ser = serde_json::Serializer::pretty(&mut buffer);
        let ser_state = SeSeed::new();
        value.serialize_state(&mut ser, &ser_state).unwrap();
    }
    let buffer = from_utf8(&buffer).unwrap();

    let mut de = serde_json::Deserializer::from_str(buffer);

    let deserialize_value = DeSeed::new(thread, &mut thread.current_context())
        .deserialize(&mut de)
        .unwrap_or_else(|err| panic!("{}\n{}", err, buffer));

    // We can't compare functions for equality so serialize again and check that for equality with
    // the first serialization
    let mut buffer2 = Vec::new();
    {
        let mut ser = serde_json::Serializer::pretty(&mut buffer2);
        let ser_state = SeSeed::new();
        value.serialize_state(&mut ser, &ser_state).unwrap();
    }
    eprintln!("{}", buffer);
    assert_eq!(buffer, from_utf8(&buffer2).unwrap());

    deserialize_value
}

#[test]
fn roundtrip_module() {
    let thread = new_vm();
    let (value, _) = Compiler::new()
        .run_expr::<OpaqueValue<&Thread, Hole>>(&thread, "test", r#" { x = 1, y = "test" } "#)
        .unwrap();
    let deserialize_value = roundtrip(&thread, &value);
    assert_eq!(deserialize_value, value.into_inner());
}

#[test]
fn roundtrip_recursive_closure() {
    let thread = new_vm();
    let expr = r#"
        rec
        let f x = g x
        let g x = f x
        { f, g }
        "#;
    let (value, _) = Compiler::new()
        .run_expr::<OpaqueValue<&Thread, Hole>>(&thread, "test", expr)
        .unwrap();
    roundtrip(&thread, &value);
}

#[test]
fn roundtrip_std_prelude() {
    let thread = new_vm();
    let expr = r#" import! std.prelude "#;
    let (value, _) = Compiler::new()
        .run_expr::<OpaqueValue<&Thread, Hole>>(&thread, "test", expr)
        .unwrap();
    roundtrip(&thread, &value);
}

#[test]
fn roundtrip_std_libs() {
    use std::fmt::Write;

    let _ = env_logger::try_init();

    let thread = new_vm();
    let mut expr = "{\n".to_string();
    for entry in walkdir::WalkDir::new("std") {
        let entry = entry.unwrap();
        let path = entry.path();
        // Can't check the extension since vim swap files ".glu.swp" will report ".glu" as the
        // extension
        let path_str = path.to_str().unwrap();
        if path.to_str().unwrap().ends_with(".glu") && 
            path_str.starts_with("std/regex") &&
            path_str.starts_with("std/repl") &&
            path_str.starts_with("std/stream") &&
            // floats cannot be roundtripped with serde json
            // https://github.com/serde-rs/json/issues/128
            path_str.starts_with("std/float")
        {
            let module = gluon_base::filename_to_module(path_str);
            write!(
                expr,
                "    {} = import! {:?},\n",
                module.replace(".", "_"),
                module
            )
            .unwrap();
        }
    }
    expr.push_str("}\n");
    let (value, _) = Compiler::new()
        .run_expr::<OpaqueValue<&Thread, Hole>>(&thread, "test", &expr)
        .unwrap_or_else(|err| panic!("{}", err));
    roundtrip(&thread, &value);
}

#[test]
fn precompile() {
    use gluon::compiler_pipeline::*;

    let thread = new_vm();
    let mut text = String::new();
    File::open("std/map.glu")
        .expect("Unable to open map.glu")
        .read_to_string(&mut text)
        .unwrap();

    let mut buffer = Vec::new();
    {
        let mut serializer = serde_json::Serializer::new(&mut buffer);
        Compiler::new()
            .compile_to_bytecode(&thread, "test", &text, &mut serializer)
            .unwrap()
    }
    let precompiled_result = {
        let mut deserializer = serde_json::Deserializer::from_slice(&buffer);
        Precompiled(&mut deserializer)
            .run_expr(&mut Compiler::new(), &*thread, "test", "", ())
            .wait()
            .unwrap()
    };
    let thread2 = new_vm();
    assert_eq!(
        serialize_value(
            text.run_expr(&mut Compiler::new(), &*thread2, "test", &text, None)
                .wait()
                .unwrap()
                .value
                .get_variant()
        ),
        serialize_value(precompiled_result.value.get_variant())
    );
}

#[test]
fn roundtrip_reference() {
    let thread = new_vm();
    let expr = r#" import! std.reference "#;
    let (value, _) = Compiler::new()
        .run_expr::<OpaqueValue<&Thread, Hole>>(&thread, "test", &expr)
        .unwrap_or_else(|err| panic!("{}", err));
    roundtrip(&thread, &value);
}

#[test]
fn roundtrip_lazy() {
    let thread = new_vm();
    let expr = r#" import! std.lazy "#;
    let (value, _) = Compiler::new()
        .run_expr::<OpaqueValue<&Thread, Hole>>(&thread, "test", &expr)
        .unwrap_or_else(|err| panic!("{}", err));
    roundtrip(&thread, &value);
}

#[test]
fn roundtrip_std_thread() {
    let thread = new_vm();
    let expr = r#" import! std.thread "#;
    let (value, _) = Compiler::new()
        .run_expr::<OpaqueValue<&Thread, Hole>>(&thread, "test", &expr)
        .unwrap_or_else(|err| panic!("{}", err));
    roundtrip(&thread, &value);
}

#[test]
#[ignore] // Unimplemented so far
fn roundtrip_thread() {
    let thread = new_vm();
    let expr = r#" let t = import! std.thread in t.new_thread ()"#;
    let (value, _) = Compiler::new()
        .run_io(true)
        .run_expr::<IO<OpaqueValue<&Thread, Hole>>>(&thread, "test", &expr)
        .unwrap_or_else(|err| panic!("{}", err));
    roundtrip(&thread, &Into::<Result<_, _>>::into(value).unwrap());
}
