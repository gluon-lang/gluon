extern crate gluon;
use gluon::new_vm;
use gluon::vm::thread::{Thread, Status};
use gluon::vm::api::primitive_f;

extern "C" fn dummy(_: &Thread) -> Status {
    unimplemented!()
}
fn f(_: &'static str) {}

#[cfg_attr(rustfmt, rustfmt_skip)]
fn main() {
    let vm = new_vm();
    vm.define_global("test", unsafe { primitive_f("f", dummy, f as fn (_)) });
    //~^ Error `vm` does not live long enough
}
