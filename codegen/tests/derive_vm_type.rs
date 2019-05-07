#[macro_use]
extern crate gluon_codegen;
extern crate gluon;

mod init;

use gluon::{base::types::Type, vm::api::VmType};
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
enum Enum {
    One,
    Two(u32),
    Three { id: String },
}

#[test]
fn enum_() {
    let vm = new_vm();

    assert_eq!(
        Enum::make_type(&vm).to_string(),
        "| One\n| Two Int\n| Three String"
    );
}

#[derive(VmType)]
#[allow(unused)]
struct NewtypeInner(Struct);

#[test]
fn newtype_inner() {
    let vm = new_vm();

    assert_eq!(
        NewtypeInner::make_type(&vm).to_string(),
        Struct::make_type(&vm).to_string(),
    );
}

#[derive(VmType)]
#[gluon(newtype)]
#[allow(unused)]
struct Newtype(Struct);

#[test]
fn newtype() {
    let vm = new_vm();

    match &*Newtype::make_type(&vm) {
        Type::Alias(alias) => {
            assert_eq!(alias.name.declared_name(), "Newtype");
            assert_eq!(
                alias.unresolved_type().to_string(),
                Struct::make_type(&vm).to_string()
            );
        }
        _ => panic!(),
    }
}
