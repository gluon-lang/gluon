extern crate gluon;
extern crate gluon_codegen;

use gluon::import::add_extern_module;
use gluon::new_vm;
use gluon::vm::api::{primitive_f, Userdata, VmType};
use gluon::vm::gc::{Gc, Traverseable};
use gluon::vm::thread::{Status, Thread};
use gluon::vm::ExternModule;

#[derive(Debug, gluon_codegen::Traverseable)]
struct Test;

impl Userdata for Test {}

impl VmType for Test {
    type Type = Test;
}

extern "C" fn dummy(_: &Thread) -> Status {
    unimplemented!()
}
fn f(_: &'static Test) {}

#[cfg_attr(rustfmt, rustfmt_skip)]
fn main() {
    let vm = new_vm();
    add_extern_module(&vm, "test", |vm| {
        ExternModule::new(vm, unsafe { primitive_f("f", dummy, f as fn (_)) })
        //~^ cannot infer an appropriate lifetime for lifetime parameter `'vm` due to conflicting requirements
    });
}
