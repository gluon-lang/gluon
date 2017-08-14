extern crate gluon_vm;
extern crate gluon;
use gluon::new_vm;
use gluon::vm::thread::{Thread, Status};
use gluon::vm::gc::{Gc, Traverseable};
use gluon::vm::api::{VmType, Userdata, primitive_f};

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
    vm.define_global("test", unsafe { primitive_f("f", dummy, f as fn (_)) });
    //~^ Error `vm` does not live long enough
}
