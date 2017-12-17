extern crate gluon;
use gluon::new_vm;
use gluon::vm::Variants;
use gluon::vm::internal::Value;
use gluon::vm::api::Getable;

#[cfg_attr(rustfmt, rustfmt_skip)]
fn main() {
    unsafe {
        let vm = new_vm();
        let v = Value::Int(0);
        let v = Variants::new(&v);
        let _: &'static str = <&'static str>::from_value(&vm, v);
        //~^ Error `vm` does not live long enough
    }
}
