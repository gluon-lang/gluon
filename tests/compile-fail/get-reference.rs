extern crate embed_lang;
use embed_lang::new_vm;
use embed_lang::vm::vm::Value;
use embed_lang::vm::api::Getable;

fn f(_: &'static str) { }

fn main() {
    let vm = new_vm();
    let s: Option<&'static str> = <&'static str>::from_value(&vm, Value::Int(0));
    //~^ Error `vm` does not live long enough
}
