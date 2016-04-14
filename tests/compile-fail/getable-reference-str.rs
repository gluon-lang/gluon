extern crate embed_lang;
use embed_lang::new_vm;
use embed_lang::vm::api::Pushable;

fn f(_: &'static str) { }

fn main() {
    let vm = new_vm();
    let f: fn (_) = f;
    vm.define_global("test", f);
    //~^ Error `vm` does not live long enough
}
