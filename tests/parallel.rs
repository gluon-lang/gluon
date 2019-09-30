#[macro_use]
extern crate gluon_vm;

use std::thread::spawn;

use gluon::{
    new_vm,
    vm::{
        api::{FunctionRef, OpaqueValue},
        channel::{ChannelRecord, Receiver, Sender},
    },
    Error, RootedThread, ThreadExt,
};

#[test]
fn parallel() {
    let _ = env_logger::try_init();

    if let Err(err) = parallel_() {
        assert!(false, "{}", err);
    }
}

fn parallel_() -> Result<(), Error> {
    let vm = new_vm();

    vm.run_expr::<()>("<top>", " let _ = import! std.channel in () ")?;

    let (value, _) = vm.run_expr(
        "<top>",
        " let { channel } = import! std.channel in channel 0 ",
    )?;
    let record_p! { sender, receiver }: ChannelRecord<
        OpaqueValue<RootedThread, Sender<i32>>,
        OpaqueValue<RootedThread, Receiver<i32>>,
    > = value;

    let child = vm.new_thread()?;
    let handle1 = spawn(move || -> Result<(), Error> {
        let expr = r#"
        let { send } = import! std.channel
        let f sender =
            send sender 1
            send sender 2
            ()
        f
        "#;
        let mut f: FunctionRef<fn(OpaqueValue<RootedThread, Sender<i32>>)> =
            child.run_expr("<top>", expr)?.0;
        Ok(f.call(sender)?)
    });

    let child2 = vm.new_thread()?;
    let handle2 = spawn(move || -> Result<(), Error> {
        let expr = r#"
        let { assert }  = import! std.test
        let { Bool } = import! std.bool
        let { Result }  = import! std.result
        let { recv } = import! std.channel

        let f receiver =
            match recv receiver with
            | Ok x -> assert (x == 1)
            | Err _ -> assert False
            match recv receiver with
            | Ok x -> assert (x == 2)
            | Err _ -> assert False

        f
        "#;
        let mut f: FunctionRef<fn(OpaqueValue<RootedThread, Receiver<i32>>)> =
            child2.run_expr("<top>", expr)?.0;
        Ok(f.call(receiver)?)
    });

    // Ensure that both threads stop without any panics (just dropping ignores panics)
    handle1.join().unwrap()?;
    handle2.join().unwrap()
}
