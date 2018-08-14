#[macro_use]
extern crate gluon_codegen;
extern crate gluon;

mod init;

use gluon::vm::api::VmType;
use init::new_vm;

#[derive(VmType)]
#[allow(unused)]
struct Struct {
    string: String,
    number: u32,
    vec: Vec<f64>,
}

#[test]
fn struct_() {
    let vm = new_vm();

    assert_eq!(
        Struct::make_type(&vm).to_string(),
        "{ string : String, number : Int, vec : Array Float }"
    );
}

#[derive(VmType)]
#[allow(unused)]
struct Newtype(Struct);

#[test]
fn newtype() {
    let vm = new_vm();

    assert_eq!(
        Newtype::make_type(&vm).to_string(),
        Struct::make_type(&vm).to_string(),
    );
}
