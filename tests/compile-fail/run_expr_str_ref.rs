extern crate gluon;

use gluon::{new_vm, Compiler};

fn main() {
    let vm = new_vm();

    let _ = Compiler::new().run_expr::<&str>(&vm, "", r#" "test" "#);
    //~^ mismatched types [E0308]
}
