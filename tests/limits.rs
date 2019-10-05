mod support;

use gluon::{
    vm::{
        api::{Hole, OpaqueValue},
        thread::ThreadInternal,
        Error as VMError,
    },
    Error, Thread, ThreadExt,
};

use crate::support::make_vm;

#[test]
fn out_of_memory() {
    let _ = ::env_logger::try_init();

    let vm = make_vm();
    vm.set_memory_limit(10);
    vm.get_database_mut().implicit_prelude(false);

    let expr = " [1, 2, 3, 4] ";
    let result = vm.run_expr::<OpaqueValue<&Thread, Hole>>("example", expr);

    match result {
        // FIXME This should just need to match on the explicit out of memory error
        Err(Error::VM(VMError::OutOfMemory { limit: 10, .. })) => (),
        Err(err) => panic!("Unexpected error `{:?}`", err),
        Ok(_) => panic!("Expected an error"),
    }
}

#[test]
fn stack_overflow() {
    let _ = ::env_logger::try_init();

    let vm = make_vm();
    vm.context().set_max_stack_size(3);
    vm.get_database_mut().implicit_prelude(false);

    let expr = " [1, 2, 3, 4] ";
    let result = vm.run_expr::<OpaqueValue<&Thread, Hole>>("example", expr);

    match result {
        Err(Error::VM(VMError::StackOverflow(3))) => (),
        Err(err) => panic!("Unexpected error `{:?}`", err),
        Ok(_) => panic!("Expected an error"),
    }
}
