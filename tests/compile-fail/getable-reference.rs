extern crate embed_lang;
use embed_lang::new_vm;
use embed_lang::vm::gc::{Gc, Traverseable};
use embed_lang::vm::api::{Pushable, VMType};

struct Test;

impl VMType for Test {
    type Type = Test;
}

impl Traverseable for Test {
    fn traverse(&self, _: &mut Gc) { }
}

fn f(_: &'static Test) { }

fn main() {
    let vm = new_vm();
    let f: fn (_) = f;
    vm.define_global("test", f);
    //~^ Error `vm` does not live long enough
}
