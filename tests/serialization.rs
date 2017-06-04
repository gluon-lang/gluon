extern crate serde_json;
extern crate serde;

extern crate gluon;

use gluon::{Compiler, new_vm};
use gluon::vm::api::{Hole, OpaqueValue};
use gluon::vm::internal::Value;
use gluon::vm::thread::{RootedThread, Thread};
use gluon::vm::serialization::{DeSeed, SeSeed};

fn roundtrip(thread: &RootedThread, value: OpaqueValue<&Thread, Hole>) {
    use serde::ser::SerializeSeed;
    let value = unsafe { value.get_value() };

    let mut buffer = Vec::new();
    {
        let mut ser = serde_json::Serializer::pretty(&mut buffer);
        let ser_seed = SeSeed::new();
        value.serialize_seed(&mut ser, &ser_seed).unwrap();
    }
    println!("{}", ::std::str::from_utf8(&buffer).unwrap());
    let mut de = serde_json::Deserializer::from_slice(&buffer);

    let deserialize_value: Value = DeSeed::new(thread.clone()).deserialize(&mut de).unwrap();
    assert_eq!(deserialize_value, value);
}

#[test]
fn roundtrip_module() {
    let thread = new_vm();
    let (value, _) = Compiler::new()
        .run_expr::<OpaqueValue<&Thread, Hole>>(&thread, "test", r#" { x = 1, y = "test" } "#)
        .unwrap();
    roundtrip(&thread, value);
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
    roundtrip(&thread, value);
}
