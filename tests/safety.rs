extern crate env_logger;

extern crate gluon;

mod support;

use gluon::vm::api::{FunctionRef, OpaqueValue};
use gluon::vm::reference::Reference;
use gluon::{Compiler, RootedThread, Thread};

use support::*;

fn verify_value_cloned(from: &Thread, to: &Thread) {
    let expr = r#" ref 0 "#;

    let (value, _) = Compiler::new()
        .run_expr::<OpaqueValue<RootedThread, Reference<i32>>>(&from, "example", expr)
        .unwrap_or_else(|err| panic!("{}", err));

    // Load the prelude
    type Fn<'t> = FunctionRef<'t, fn(OpaqueValue<RootedThread, Reference<i32>>)>;
    let (mut store_1, _) = Compiler::new()
        .run_expr::<Fn>(&to, "store_1", r#"\r -> r <- 1"#)
        .unwrap();
    assert_eq!(store_1.call(value.clone()), Ok(()));

    let mut load: FunctionRef<fn(OpaqueValue<RootedThread, Reference<i32>>) -> i32> =
        from.get_global("load").unwrap();
    assert_eq!(load.call(value), Ok(0));
}

#[test]
fn cant_transfer_opaque_value_between_sibling_threads() {
    let _ = ::env_logger::init();
    //     vm
    //  /     \
    // vm1    vm2
    // Passing a value directly from vm1 to vm2 requires the value to be cloned in its entirety
    let vm = make_vm();
    let vm1 = vm.new_thread().unwrap();
    let vm2 = vm.new_thread().unwrap();
    verify_value_cloned(&vm1, &vm2);
}

#[test]
fn cant_transfer_opaque_value_between_disjoint_threads() {
    let _ = ::env_logger::init();
    // vm1    vm2
    // Passing a value directly from vm1 to vm2 requires the value to be cloned in its entirety
    // since the vms do not share the same global vm
    let vm1 = make_vm();
    let vm2 = make_vm();
    verify_value_cloned(&vm1, &vm2);
}
