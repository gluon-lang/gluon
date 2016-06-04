extern crate gluon;
use gluon::new_vm;
use gluon::vm::vm::Value;
use gluon::vm::api::Getable;

fn f(_: &'static str) { }

fn main() {
    let vm = new_vm();
    let s: Option<&'static str> = <&'static str>::from_value(&vm, Value::Int(0));
    //~^ Error `vm` does not live long enough
}
