mod support;

use gluon::{
    vm::{
        api::{FunctionRef, OpaqueValue, IO},
        reference::Reference,
    },
    RootedThread, Thread, ThreadExt,
};

use crate::support::*;

fn verify_value_cloned(from: &Thread, to: &Thread) {
    from.get_database_mut().run_io(true);
    to.get_database_mut().run_io(true);

    from.run_expr::<()>("load", r#"let _ = import! std.reference in () "#)
        .unwrap_or_else(|err| panic!("{}", err));
    to.run_expr::<()>("load", r#"let _ = import! std.reference in () "#)
        .unwrap_or_else(|err| panic!("{}", err));

    let expr = r#"
        let { ref } = import! std.reference
        ref 0
        "#;

    let value: OpaqueValue<_, _> = from
        .run_expr::<IO<OpaqueValue<RootedThread, Reference<i32>>>>("example", expr)
        .and_then(|(io, _)| Result::from(io).map_err(From::from))
        .unwrap_or_else(|err| panic!("{}", err));

    // Load the prelude
    type Fn<'t> = FunctionRef<'t, fn(OpaqueValue<RootedThread, Reference<i32>>) -> IO<()>>;
    let store_expr = r#"
        let { (<-) } = import! std.reference
        \r -> r <- 1
        "#;
    let (mut store_1, _) = to
        .run_expr::<Fn>("store_1", store_expr)
        .unwrap_or_else(|err| panic!("{}", err));
    assert_eq!(store_1.call(value.clone()), Ok(IO::Value(())));

    let mut load: FunctionRef<fn(OpaqueValue<RootedThread, Reference<i32>>) -> IO<i32>> =
        from.get_global("std.reference.load").unwrap();
    assert_eq!(load.call(value), Ok(IO::Value(0)));
}

#[test]
fn cant_transfer_opaque_value_between_sibling_threads() {
    let _ = ::env_logger::try_init();
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
    let _ = ::env_logger::try_init();
    // vm1    vm2
    // Passing a value directly from vm1 to vm2 requires the value to be cloned in its entirety
    // since the vms do not share the same global vm
    let vm1 = make_vm();
    let vm2 = make_vm();
    verify_value_cloned(&vm1, &vm2);
}
