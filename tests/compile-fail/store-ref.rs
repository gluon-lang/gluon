extern crate gluon;
use std::fmt;
use std::sync::Mutex;

use gluon::new_vm;
use gluon::vm::api::{Userdata, VmType};
use gluon::vm::gc::Traverseable;

struct Test<'vm>(Mutex<&'vm str>);

impl Userdata for Test<'static> { }

impl<'vm> fmt::Debug for Test<'vm> {
    fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
        Ok(())
    }
}

impl<'vm> Traverseable for Test<'vm> { }
impl<'vm> VmType for Test<'vm> {
    type Type = Test<'static>;
}

fn f<'vm>(test: &'vm Test<'vm>, s: &'vm str) {
    *test.0.lock().unwrap() = s;
}

fn main() {
    let vm = new_vm();
    let _ = vm.define_global("f", f as fn (_, _));
    //~^ `vm` does not live long enough
}
