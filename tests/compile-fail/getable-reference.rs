#[macro_use]
extern crate gluon_vm;
extern crate gluon;
extern crate gluon_codegen;

use gluon::{
    import::add_extern_module,
    new_vm,
    vm::{
        api::{primitive_f, Userdata, VmType},
        gc::{Gc, Trace},
        thread::{Status, Thread},
        ExternModule,
    },
};

#[derive(Debug, gluon_codegen::Trace)]
struct Test;

impl Userdata for Test {}

impl VmType for Test {
    type Type = Test;
}

fn f(_: &'static Test) {}

#[cfg_attr(rustfmt, rustfmt_skip)]
fn main() {
    let vm = new_vm();
    add_extern_module(&vm, "test", |vm| {
        ExternModule::new(vm, primitive!(1, f))
        //~^ `thread` has lifetime `'thread` but it needs to satisfy a `'static` lifetime requirement
    });
}
