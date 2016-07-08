extern crate gluon;
extern crate env_logger;

use gluon::{Compiler, new_vm};

#[test]
fn read_file() {
    let _ = ::env_logger::init();

    let thread = new_vm();
    let text = r#"
        let prelude = import "std/prelude.glu"
        let { assert } = import "std/test.glu"

        let file = io.open_file "Cargo.toml"
        let bytes = io.read_file file 9
        assert (array.length bytes == 9)
        assert (array.index bytes 0 #Byte== 91b) // [
        assert (array.index bytes 1 #Byte== 112b) // p
        (array.index bytes 8)
        "#;
    let result = Compiler::new()
        .run_expr::<u8>(&thread, "<top>", text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
    assert_eq!(result.unwrap(), b']');
}
