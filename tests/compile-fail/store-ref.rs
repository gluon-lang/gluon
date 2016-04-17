extern crate embed_lang;
use embed_lang::new_vm;
use embed_lang::vm::vm::Value;
use embed_lang::vm::api::{VMType, Getable};
use embed_lang::vm::gc::Traverseable;

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
