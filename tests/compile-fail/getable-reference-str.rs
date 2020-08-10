#[macro_use]
extern crate gluon_vm;
extern crate gluon;
use gluon::{
    import::add_extern_module,
    new_vm,
    vm::{
        api::primitive_f,
        thread::{Status, Thread},
        ExternModule,
    },
};

fn f(_: &'static str) {}

#[cfg_attr(rustfmt, rustfmt_skip)]
fn main() {
    let vm = new_vm();
    add_extern_module(&vm, "test", |vm| {
        ExternModule::new(vm, primitive!(1, f))
        //~^ `thread` has lifetime `'thread` but it needs to satisfy a `'static` lifetime requirement
    });
}
