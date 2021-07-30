extern crate gluon;

use gluon::{new_vm, ThreadExt};

fn main() {
    let vm = new_vm();

    let _ = vm.run_expr::<&str>("", r#" "test" "#);
    //~^ the trait bound `for<'value> &str: Getable<'_, 'value>` is not satisfied [E0277]
}
