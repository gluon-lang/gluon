extern crate gluon;
use gluon::new_vm;
use gluon::vm::api::Getable;
use gluon::vm::internal::Value;
use gluon::vm::Variants;

#[cfg_attr(rustfmt, rustfmt_skip)]
fn main() {
    unsafe {
        let vm = new_vm();
        let value = Value::int(0);
        let value = Variants::new(&value);
        //~^ Error `value` does not live long enough
        let _: &'static str = <&'static str>::from_value(&vm, value);
    }
}
