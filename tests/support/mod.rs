extern crate env_logger;
extern crate gluon;

use gluon::vm::api::{Getable, VmType};
use gluon::vm::thread::{RootedThread, Thread};
use gluon::import::Import;
use gluon::Compiler;

#[allow(dead_code)]
pub fn load_script(vm: &Thread, filename: &str, input: &str) -> ::gluon::Result<()> {
    Compiler::new()
        .implicit_prelude(false)
        .load_script(vm, filename, input)
}

pub fn run_expr_<'vm, T>(vm: &'vm Thread, s: &str, implicit_prelude: bool) -> T
    where T: Getable<'vm> + VmType
{
    Compiler::new()
        .implicit_prelude(implicit_prelude)
        .run_expr(vm, "<top>", s)
        .unwrap_or_else(|err| panic!("{}", err)).0
}

pub fn run_expr<'vm, T>(vm: &'vm Thread, s: &str) -> T
    where T: Getable<'vm> + VmType
{
    run_expr_(vm, s, false)
}

/// Creates a VM for testing which has the correct paths to import the std library properly
pub fn make_vm() -> RootedThread {
    let vm = ::gluon::new_vm();
    let import = vm.get_macros().get("import");
    import.as_ref()
          .and_then(|import| import.downcast_ref::<Import>())
          .expect("Import macro")
          .add_path("..");
    vm
}

macro_rules! test_expr {
    (prelude $name: ident, $expr: expr, $value: expr) => {
        #[test]
        fn $name() {
            let _ = ::env_logger::init();
            let mut vm = make_vm();
            let value = run_expr_(&mut vm, $expr, true);
            assert_eq!(value, $value);

            // Help out the type inference by forcing that left and right are the same types
            fn equiv<T>(_: &T, _: &T) { }
            equiv(&value, &$value);
        }
    };
    (io $name: ident, $expr: expr, $value: expr) => {
        #[test]
        fn $name() {
            let _ = ::env_logger::init();
            let mut vm = make_vm();
            let (value, _) = Compiler::new()
                .implicit_prelude(false)
                .run_io_expr(&mut vm, "<top>", $expr)
                .unwrap_or_else(|err| panic!("{}", err));
            assert_eq!(value, $value);

            // Help out the type inference by forcing that left and right are the same types
            fn equiv<T>(_: &T, _: &T) { }
            equiv(&value, &$value);
        }
    };
    ($name: ident, $expr: expr, $value: expr) => {
        #[test]
        fn $name() {
            let _ = ::env_logger::init();
            let mut vm = make_vm();
            let value = run_expr(&mut vm, $expr);
            assert_eq!(value, $value);

            // Help out the type inference by forcing that left and right are the same types
            fn equiv<T>(_: &T, _: &T) { }
            equiv(&value, &$value);
        }
    };
    ($name: ident, $expr: expr) => {
        #[test]
        fn $name() {
            let _ = ::env_logger::init();
            let mut vm = make_vm();
            run_expr::<Generic<A>>(&mut vm, $expr);
        }
    }
}
