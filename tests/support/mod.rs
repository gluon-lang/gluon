#![allow(dead_code)]

pub extern crate futures;

use gluon::{
    import::Import,
    vm::{
        api::{Getable, VmType},
        thread::{RootedThread, Thread},
    },
    ThreadExt,
};

#[allow(dead_code)]
pub fn load_script(vm: &Thread, filename: &str, input: &str) -> ::gluon::Result<()> {
    vm.get_database_mut().set_implicit_prelude(false);
    vm.load_script(filename, input)
}

#[allow(dead_code)]
pub fn run_expr_<'vm, T>(vm: &'vm Thread, s: &str, implicit_prelude: bool) -> T
where
    T: for<'value> Getable<'vm, 'value> + VmType + Send + 'vm,
{
    vm.get_database_mut()
        .implicit_prelude(implicit_prelude)
        .run_io(true);
    vm.run_expr("<top>", s)
        .unwrap_or_else(|err| panic!("{}", err))
        .0
}

#[allow(dead_code)]
pub fn run_expr<'vm, T>(vm: &'vm Thread, s: &str) -> T
where
    T: for<'value> Getable<'vm, 'value> + VmType + Send + 'vm,
{
    run_expr_(vm, s, false)
}

/// Creates a VM for testing which has the correct paths to import the std library properly
pub fn make_vm() -> RootedThread {
    let vm = ::gluon::VmBuilder::new().build();
    let import = vm.get_macros().get("import");
    import
        .as_ref()
        .and_then(|import| import.downcast_ref::<Import>())
        .expect("Import macro")
        .add_path("..");
    vm
}

pub async fn make_vm_async() -> RootedThread {
    let vm = ::gluon::VmBuilder::new().build_async().await;
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
    (prelude $name:ident, $expr:expr, $value:expr) => {
        #[test]
        fn $name() {
            let _ = ::env_logger::try_init();
            let mut vm = $crate::support::make_vm();
            let value = $crate::support::run_expr_(&mut vm, $expr, true);
            assert_eq!(value, $value);

            // Help out the type inference by forcing that left and right are the same types
            fn equiv<T>(_: &T, _: &T) {}
            equiv(&value, &$value);
        }
    };
    (io $name:ident, $expr:expr, $value:expr) => {
        #[test]
        fn $name() {
            use gluon::{vm::api::IO, ThreadExt};

            let _ = ::env_logger::try_init();
            let vm = $crate::support::make_vm();
            vm.get_database_mut().implicit_prelude(false).run_io(true);
            let (value, _) = vm
                .run_expr("<top>", $expr)
                .unwrap_or_else(|err| panic!("{}", err));
            match value {
                IO::Value(value) => {
                    assert_eq!(value, $value);

                    // Help out the type inference by forcing that left and right are the same types
                    fn equiv<T>(_: &T, _: &T) {}
                    equiv(&value, &$value);
                }
                IO::Exception(err) => panic!("{}", err),
            }
        }
    };
    (any $name:ident, $expr:expr, $value:expr) => {
        #[test]
        fn $name() {
            let _ = ::env_logger::try_init();
            let mut vm = $crate::support::make_vm();
            let value = $crate::support::run_expr::<OpaqueValue<&Thread, Hole>>(&mut vm, $expr);
            assert_eq!(value.get_ref(), $value);
        }
    };
    ($name:ident, $expr:expr, $value:expr) => {
        #[test]
        fn $name() {
            let _ = ::env_logger::try_init();
            let mut vm = $crate::support::make_vm();
            let value = $crate::support::run_expr(&mut vm, $expr);
            assert_eq!(value, $value);

            // Help out the type inference by forcing that left and right are the same types
            fn equiv<T>(_: &T, _: &T) {}
            equiv(&value, &$value);
        }
    };
    ($name:ident, $expr:expr) => {
        #[test]
        fn $name() {
            let _ = ::env_logger::try_init();
            let mut vm = $crate::support::make_vm();
            $crate::support::run_expr::<OpaqueValue<&Thread, Hole>>(&mut vm, $expr);
        }
    };
}
