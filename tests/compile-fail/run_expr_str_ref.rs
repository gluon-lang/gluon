extern crate gluon;

use gluon::{new_vm, Compiler};

fn main() {
    let vm = new_vm();

    let _ = Compiler::new().run_expr::<&str>(&vm, "", r#" "test" "#);
    //~^ the trait bound `for<'value> &str: gluon::gluon_vm::api::Getable<'_, 'value>` is not satisfied [E0277]
}
