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
    let buffer = from_utf8(&buffer).unwrap();

    let mut de = serde_json::Deserializer::from_str(buffer);

    let deserialize_value = DeSeed::new(thread.clone())
        .deserialize(&mut de)
        .unwrap_or_else(|err| panic!("{}\n{}", err, buffer));
    let deserialize_value = thread.root_value_ref(deserialize_value);

    // We can't compare functions for equality so serialize again and check that for equality with
    // the first serialization
    let mut buffer2 = Vec::new();
    {
        let mut ser = serde_json::Serializer::pretty(&mut buffer2);
        let ser_seed = SeSeed::new();
        value.serialize_seed(&mut ser, &ser_seed).unwrap();
    }
    assert_eq!(buffer, from_utf8(&buffer2).unwrap());
    let mut f = ::std::fs::File::create("../test2").unwrap();
    ::std::io::Write::write_all(&mut f, &buffer2).unwrap();

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
    let expr = r#" import! "std/prelude.glu" "#;
    let (value, _) = Compiler::new()
        .run_expr::<OpaqueValue<&Thread, Hole>>(&thread, "test", expr)
        .unwrap();
    roundtrip(&thread, &value);
}

#[test]
fn roundtrip_std_libs() {
    let thread = new_vm();
    let mut expr = "{\n".to_string();
    for entry in std::fs::read_dir("std").unwrap() {
        let path = entry.unwrap().path();
        // Can't check the extension since vim swap files ".glu.swp" will report ".glu" as the
        // extension
        if path.to_str().unwrap().ends_with(".glu") &&
           path.file_stem().unwrap().to_str() != Some("repl") {
            expr.push_str(&format!("    {} = import! {:?},\n",
                                   path.file_stem().unwrap().to_str().unwrap(),
                                   path.display()));
        }
    }
    expr.push_str("}\n");
    let (value, _) = Compiler::new()
        .run_expr::<OpaqueValue<&Thread, Hole>>(&thread, "test", &expr)
        .unwrap_or_else(|err| panic!("{}", err));
    roundtrip(&thread, &value);
}
