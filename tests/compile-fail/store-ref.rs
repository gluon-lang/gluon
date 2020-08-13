#[macro_use]
extern crate gluon_vm;
extern crate gluon;
extern crate gluon_codegen;

use std::{fmt, sync::Mutex};

use gluon::{
    import::add_extern_module,
    new_vm,
    vm::{
        api::{primitive_f, Userdata, VmType},
        gc::Trace,
        thread::{Status, Thread},
        ExternModule,
    },
};

#[derive(gluon_codegen::Trace)]
#[gluon_trace(skip)]
struct Test<'vm>(Mutex<&'vm str>);

impl Userdata for Test<'static> {}

impl<'vm> fmt::Debug for Test<'vm> {
    fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
        Ok(())
    }
}

impl<'vm> VmType for Test<'vm> {
    type Type = Test<'static>;
}

fn f<'vm>(test: &'vm Test<'vm>, s: &'vm str) {
    *test.0.lock().unwrap() = s;
}

#[cfg_attr(rustfmt, rustfmt_skip)]
fn main() {
    let vm = new_vm();
    add_extern_module(&vm, "test", |vm| {
        ExternModule::new(vm, primitive!(2, f))
        //~^ `thread` has lifetime `'thread` but it needs to satisfy a `'static` lifetime requirement
    });
}
