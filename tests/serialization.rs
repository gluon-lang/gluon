extern crate serde_json;
extern crate serde;

extern crate gluon;

use gluon::{Compiler, new_vm};
use gluon::vm::api::{Hole, OpaqueValue};
use gluon::vm::thread::{RootedThread, RootedValue, Thread, ThreadInternal};
use gluon::vm::serialization::{DeSeed, SeSeed};

fn roundtrip<'t>(thread: &'t RootedThread,
                 value: &OpaqueValue<&Thread, Hole>)
                 -> RootedValue<&'t Thread> {
    use std::str::from_utf8;

    use serde::ser::SerializeSeed;
    let value = unsafe { value.get_value() };

    let mut buffer = Vec::new();
    {
        let mut ser = serde_json::Serializer::pretty(&mut buffer);
        let ser_seed = SeSeed::new();
        value.serialize_seed(&mut ser, &ser_seed).unwrap();
    }

    let mut de = serde_json::Deserializer::from_slice(&buffer);

    let deserialize_value = DeSeed::new(thread.clone()).deserialize(&mut de).unwrap();
    let deserialize_value = thread.root_value_ref(deserialize_value);

    // We can't compare functions for equality so serialize again and check that for equality with
    // the first serialization
    let mut buffer2 = Vec::new();
    {
        let mut ser = serde_json::Serializer::pretty(&mut buffer2);
        let ser_seed = SeSeed::new();
        value.serialize_seed(&mut ser, &ser_seed).unwrap();
    }
    assert_eq!(from_utf8(&buffer).unwrap(), from_utf8(&buffer2).unwrap());

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
