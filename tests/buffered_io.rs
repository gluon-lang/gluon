extern crate env_logger;
extern crate gluon;

use gluon::vm::api::IO;
use gluon::{new_vm, Compiler};

#[test]
fn buffered_io() {
    env_logger::init();
    let thread = new_vm();

    let _ = Compiler::new()
        .run_io(true)
        .run_expr::<IO<()>>(&thread, "<buffered_io>", include_str!("buffered_io.glu"))
        .unwrap_or_else(|err| panic!("{}", err));
}
