extern crate gluon;
use gluon::new_vm;
use gluon::vm::vm::Value;
use gluon::vm::api::{VMType, Getable};
use gluon::vm::gc::Traverseable;

use std::cell::Cell;

struct Test<'vm>(Cell<&'vm str>);

impl<'vm> Traverseable for Test<'vm> { }
impl<'vm> VMType for Test<'vm> {
    type Type = Test<'static>;
}

fn f<'vm>(test: &'vm Test<'vm>, s: &'vm str) {
    test.0.set(s);
}

fn main() {
    let vm = new_vm();
    vm.define_global("f", f as fn (_, _));
    //~^ Error `vm` does not live long enough
}
