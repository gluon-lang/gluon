extern crate gluon;

use std::thread::spawn;

use gluon::vm::channel::{ChannelRecord, Sender, Receiver};
use gluon::vm::api::OpaqueValue;
use gluon::vm::api::FunctionRef;
use gluon::RootedThread;
use gluon::{new_vm, Compiler, Error};

#[test]
fn parallel() {
    if let Err(err) = parallel_() {
        assert!(false, "{}", err);
    }
}

fn parallel_() -> Result<(), Error> {
    let vm = new_vm();
    let mut compiler = Compiler::new();
    let (value, _) = try!(compiler.run_expr(&vm, "<top>", " channel 0 "));
    let value: ChannelRecord<OpaqueValue<RootedThread, Sender<i32>>, OpaqueValue<RootedThread, Receiver<i32>>> = value;
    let (sender, receiver) = value.split();

    let child = vm.new_thread();
    let handle1 = spawn(move || -> Result<(), Error> {
        let expr = r#"
        let f sender =
            send sender 1
            send sender 2
            ()
        f
        "#;
        let mut compiler = Compiler::new();
        let mut f: FunctionRef<fn (OpaqueValue<RootedThread, Sender<i32>>)> = try!(compiler.run_expr(&child, "<top>", expr)).0;
        Ok(try!(f.call(sender)))
    });

    let child2 = vm.new_thread();
    let handle2 = spawn(move || -> Result<(), Error> {
        let expr = r#"
        let { assert } = import "std/test.glu"
        let f receiver =
            match recv receiver with
            | Ok x -> assert (x == 1)
            | Err _ -> assert False
            match recv receiver with
            | Ok x -> assert (x == 2)
            | Err _ -> assert False
        f
        "#;
        let mut compiler = Compiler::new();
        let mut f: FunctionRef<fn (OpaqueValue<RootedThread, Receiver<i32>>)> = try!(compiler.run_expr(&child2, "<top>", expr)).0;
        Ok(try!(f.call(receiver)))
    });

    // Ensure that both threads stop without any panics (just dropping ignores panics)
    try!(handle1.join().unwrap());
    handle2.join().unwrap()
}
