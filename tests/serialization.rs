#![cfg(feature = "serialization")]
extern crate futures;

extern crate env_logger;

extern crate serde_json;
extern crate serde_state as serde;

extern crate gluon;

use std::fs::File;
use std::io::Read;

use futures::Future;

use serde::ser::SerializeState;

use gluon::{new_vm, Compiler};
use gluon::vm::api::{Hole, OpaqueValue};
use gluon::vm::thread::{RootedThread, RootedValue, Thread, ThreadInternal};
use gluon::vm::serialization::{DeSeed, SeSeed};
use gluon::vm::internal::Value;

fn serialize_value(value: &Value) {
    let mut buffer = Vec::new();
    {
        let mut ser = serde_json::Serializer::pretty(&mut buffer);
        let ser_state = SeSeed::new();
        value.serialize_state(&mut ser, &ser_state).unwrap();
    }
    String::from_utf8(buffer).unwrap();
}

fn roundtrip<'t>(
    thread: &'t RootedThread,
    value: &OpaqueValue<&Thread, Hole>,
) -> RootedValue<&'t Thread> {
    use std::str::from_utf8;

    let value = unsafe { value.get_value() };

    let mut buffer = Vec::new();
    {
        let mut ser = serde_json::Serializer::pretty(&mut buffer);
        let ser_state = SeSeed::new();
        value.serialize_state(&mut ser, &ser_state).unwrap();
    }
    let buffer = from_utf8(&buffer).unwrap();

    let mut de = serde_json::Deserializer::from_str(buffer);

    let deserialize_value = DeSeed::new(thread)
        .deserialize(&mut de)
        .unwrap_or_else(|err| panic!("{}\n{}", err, buffer));
    let deserialize_value = thread.root_value(deserialize_value);

    // We can't compare functions for equality so serialize again and check that for equality with
    // the first serialization
    let mut buffer2 = Vec::new();
    {
        let mut ser = serde_json::Serializer::pretty(&mut buffer2);
        let ser_state = SeSeed::new();
        value.serialize_state(&mut ser, &ser_state).unwrap();
    }
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
        let f x = g x
        and g x = f x
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
    let _ = env_logger::try_init();

    let thread = new_vm();
    let mut expr = "{\n".to_string();
    for entry in std::fs::read_dir("std").unwrap() {
        let path = entry.unwrap().path();
        // Can't check the extension since vim swap files ".glu.swp" will report ".glu" as the
        // extension
        let file_stem = path.file_stem().unwrap().to_str();
        if path.to_str().unwrap().ends_with(".glu") && file_stem != Some("repl")
            // floats cannot be roundtripped with serde json
            // https://github.com/serde-rs/json/issues/128
            && file_stem != Some("float")
        {
            expr.push_str(&format!(
                "    {} = import! {:?},\n",
                path.file_stem().unwrap().to_str().unwrap(),
                path.display()
            ));
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
            &text.run_expr(&mut Compiler::new(), &*thread2, "test", &text, None)
                .wait()
                .unwrap()
                .value
        ),
        serialize_value(&precompiled_result.value)
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
fn roundtrip_thread() {
    let thread = new_vm();
    let expr = r#" import! std.thread "#;
    let (value, _) = Compiler::new()
        .run_expr::<OpaqueValue<&Thread, Hole>>(&thread, "test", &expr)
        .unwrap_or_else(|err| panic!("{}", err));
    roundtrip(&thread, &value);
}
