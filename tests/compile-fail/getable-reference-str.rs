extern crate gluon;
use gluon::new_vm;
use gluon::import::add_extern_module;
use gluon::vm::ExternModule;
use gluon::vm::thread::{Status, Thread};
use gluon::vm::api::primitive_f;

extern "C" fn dummy(_: &Thread) -> Status {
    unimplemented!()
}
fn f(_: &'static str) {}

#[cfg_attr(rustfmt, rustfmt_skip)]
fn main() {
    let vm = new_vm();
    add_extern_module(&vm, "test", |vm| {
        ExternModule::new(vm, unsafe { primitive_f("f", dummy, f as fn (_)) })
        //~^ cannot infer an appropriate lifetime for lifetime parameter `'vm` due to conflicting requirements
    });
}
