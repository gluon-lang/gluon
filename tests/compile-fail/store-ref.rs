extern crate gluon;
use std::fmt;
use std::sync::Mutex;

use gluon::new_vm;
use gluon::import::add_extern_module;
use gluon::vm::ExternModule;
use gluon::vm::thread::{Status, Thread};
use gluon::vm::api::{primitive_f, Userdata, VmType};
use gluon::vm::gc::Traverseable;

struct Test<'vm>(Mutex<&'vm str>);

impl Userdata for Test<'static> {}

impl<'vm> fmt::Debug for Test<'vm> {
    fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
        Ok(())
    }
}

impl<'vm> Traverseable for Test<'vm> {}
impl<'vm> VmType for Test<'vm> {
    type Type = Test<'static>;
}

extern "C" fn dummy(_: &Thread) -> Status {
    unimplemented!()
}

fn f<'vm>(test: &'vm Test<'vm>, s: &'vm str) {
    *test.0.lock().unwrap() = s;
}

#[cfg_attr(rustfmt, rustfmt_skip)]
fn main() {
    let vm = new_vm();
    add_extern_module(&vm, "test", |vm| {
        ExternModule::new(vm, unsafe { primitive_f("f", dummy, f as fn (_, _)) })
        //~^ cannot infer an appropriate lifetime for lifetime parameter `'vm` due to conflicting requirements
    });
}
