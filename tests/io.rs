extern crate gluon;
extern crate env_logger;

use gluon::{Compiler, new_vm};
use gluon::vm::api::IO;

#[test]
fn read_file() {
    let _ = ::env_logger::init();

    let thread = new_vm();
    let text = r#"
        let prelude  = import! "std/prelude.glu"
        let { assert }  = import! "std/test.glu"
        let { pure } = prelude.applicative_IO
        let { (>>=) } = prelude.make_Monad prelude.monad_IO

        io.open_file "Cargo.toml" >>= \file ->
            io.read_file file 9 >>= \bytes ->
            assert (array.length bytes == 9)
            assert (array.index bytes 0 #Byte== 91b) // [
            assert (array.index bytes 1 #Byte== 112b) // p
            pure (array.index bytes 8)
        "#;
    let result = Compiler::new()
        .run_io_expr_async::<IO<u8>>(&thread, "<top>", text)
        .sync_or_error();

    match result {
        Ok((IO::Value(value), _)) => assert_eq!(value, b']'),
        Ok((IO::Exception(err), _)) => assert!(false, "{}", err),
        Err(err) => assert!(false, "{}", err),
    }
}
