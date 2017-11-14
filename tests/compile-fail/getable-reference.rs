extern crate gluon;
use gluon::new_vm;
use gluon::import::add_extern_module;
use gluon::vm::ExternModule;
use gluon::vm::thread::{Status, Thread};
use gluon::vm::gc::{Gc, Traverseable};
use gluon::vm::api::{primitive_f, Userdata, VmType};

#[derive(Debug)]
struct Test;

impl Userdata for Test {}

impl VmType for Test {
    type Type = Test;
}

impl Traverseable for Test {
    fn traverse(&self, _: &mut Gc) {}
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
