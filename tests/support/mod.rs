#[allow(unused_extern_crates)]
extern crate env_logger;
pub extern crate futures;
#[allow(unused_extern_crates)]
extern crate gluon;
extern crate tokio_core;

use gluon::vm::api::{Getable, VmType};
use gluon::vm::thread::{RootedThread, Thread};
use gluon::import::Import;
use gluon::Compiler;

#[allow(dead_code)]
pub fn load_script(vm: &Thread, filename: &str, input: &str) -> ::gluon::Result<()> {
    Compiler::new()
        .implicit_prelude(false)
        .load_script_async(vm, filename, input)
        .sync_or_error()
}

#[allow(dead_code)]
pub fn run_expr_<'vm, T>(vm: &'vm Thread, s: &str, implicit_prelude: bool) -> T
where
    T: Getable<'vm> + VmType + Send + 'vm,
{
    Compiler::new()
        .implicit_prelude(implicit_prelude)
        .run_expr_async(vm, "<top>", s)
        .sync_or_error()
        .unwrap_or_else(|err| panic!("{}", err))
        .0
}

#[allow(dead_code)]
pub fn run_expr<'vm, T>(vm: &'vm Thread, s: &str) -> T
where
    T: Getable<'vm> + VmType + Send + 'vm,
{
    run_expr_(vm, s, false)
}

/// Creates a VM for testing which has the correct paths to import the std library properly
pub fn make_vm() -> RootedThread {
    make_async_vm(None)
}

pub fn make_async_vm(remote: Option<self::tokio_core::reactor::Remote>) -> RootedThread {
    let vm = ::gluon::VmBuilder::new().event_loop(remote).build();
    let import = vm.get_macros().get("import");
    import
        .as_ref()
        .and_then(|import| import.downcast_ref::<Import>())
        .expect("Import macro")
        .add_path("..");
    vm
}

#[allow(unused_macros)]
macro_rules! test_expr {
    (prelude $name: ident, $expr: expr, $value: expr) => {
        #[test]
        fn $name() {
            let _ = ::env_logger::try_init();
            let mut vm = $crate::support::make_vm();
            let value = $crate::support::run_expr_(&mut vm, $expr, true);
            assert_eq!(value, $value);

            // Help out the type inference by forcing that left and right are the same types
            fn equiv<T>(_: &T, _: &T) { }
            equiv(&value, &$value);
        }
    };
    (io $name: ident, $expr: expr, $value: expr) => {
        #[test]
        fn $name() {
            use gluon::vm::api::IO;

            let _ = ::env_logger::try_init();
            let mut vm = $crate::support::make_vm();
            let (value, _) = ::gluon::Compiler::new()
                .implicit_prelude(false)
                .run_io(true)
                .run_expr(&mut vm, "<top>", $expr)
                .unwrap_or_else(|err| panic!("{}", err));
            match value {
                IO::Value(value) => {
                    assert_eq!(value, $value);

                    // Help out the type inference by forcing that left and right are the same types
                    fn equiv<T>(_: &T, _: &T) { }
                    equiv(&value, &$value);
                }
                IO::Exception(err) => panic!("{}", err),
            }
        }
    };
    (any $name: ident, $expr: expr, $value: expr) => {
        #[test]
        fn $name() {
            let _ = ::env_logger::try_init();
            let mut vm = $crate::support::make_vm();
            let value = $crate::support::run_expr::<OpaqueValue<&Thread, Hole>>(&mut vm, $expr);
            assert_eq!(value.get_ref(), $value);
        }
    };
    ($name: ident, $expr: expr, $value: expr) => {
        #[test]
        fn $name() {
            let _ = ::env_logger::try_init();
            let mut vm = $crate::support::make_vm();
            let value = $crate::support::run_expr(&mut vm, $expr);
            assert_eq!(value, $value);

            // Help out the type inference by forcing that left and right are the same types
            fn equiv<T>(_: &T, _: &T) { }
            equiv(&value, &$value);
        }
    };
    ($name: ident, $expr: expr) => {
        #[test]
        fn $name() {
            let _ = ::env_logger::try_init();
            let mut vm = $crate::support::make_vm();
            $crate::support::run_expr::<OpaqueValue<&Thread, Hole>>(&mut vm, $expr);
        }
    }
}
