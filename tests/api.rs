extern crate env_logger;
extern crate futures;

#[macro_use]
extern crate gluon_vm;
extern crate gluon;

use futures::{BoxFuture, Future, IntoFuture};
use futures::future::lazy;

use gluon::base::types::Type;
use gluon::vm::Error;
use gluon::vm::api::{FutureResult, VmType, FunctionRef, Userdata};
use gluon::vm::thread::{RootedThread, Thread, Traverseable, Root, RootStr};
use gluon::vm::types::VmInt;
use gluon::Compiler;
use gluon::import::Import;

fn load_script(vm: &Thread, filename: &str, input: &str) -> ::gluon::Result<()> {
    Compiler::new().load_script(vm, filename, input).sync_or_error()
}

fn make_vm() -> RootedThread {
    let vm = ::gluon::new_vm();
    let import = vm.get_macros().get("import");
    import.as_ref()
        .and_then(|import| import.downcast_ref::<Import>())
        .expect("Import macro")
        .add_path("..");
    vm
}

#[test]
fn call_function() {
    let _ = ::env_logger::init();
    let add10 = r"
let add10 : Int -> Int = \x -> x #Int+ 10 in add10
";
    let mul = r"
let mul : Float -> Float -> Float = \x y -> x #Float* y in mul
";
    let mut vm = make_vm();
    load_script(&mut vm, "add10", &add10).unwrap_or_else(|err| panic!("{}", err));
    load_script(&mut vm, "mul", &mul).unwrap_or_else(|err| panic!("{}", err));
    {
        let mut f: FunctionRef<fn(VmInt) -> VmInt> = vm.get_global("add10")
            .unwrap();
        let result = f.call(2).unwrap();
        assert_eq!(result, 12);
    }
    let mut f: FunctionRef<fn(f64, f64) -> f64> = vm.get_global("mul").unwrap();
    let result = f.call(4., 5.).unwrap();
    assert_eq!(result, 20.);
}

#[test]
fn root_data() {
    let _ = ::env_logger::init();

    #[derive(Debug)]
    struct Test(VmInt);
    impl Userdata for Test {}
    impl Traverseable for Test {}
    impl VmType for Test {
        type Type = Test;
    }

    let expr = r#"
\x -> test x 1
"#;
    let vm = make_vm();
    fn test(r: Root<Test>, i: VmInt) -> VmInt {
        r.0 + i
    }
    vm.register_type::<Test>("Test", &[])
        .unwrap_or_else(|_| panic!("Could not add type"));
    vm.define_global("test", primitive!(2 test)).unwrap();
    load_script(&vm, "script_fn", expr).unwrap_or_else(|err| panic!("{}", err));
    let mut script_fn: FunctionRef<fn(Test) -> VmInt> = vm.get_global("script_fn").unwrap();
    let result = script_fn.call(Test(123))
        .unwrap();
    assert_eq!(result, 124);
}

#[test]
fn root_string() {
    let _ = ::env_logger::init();

    let expr = r#"
test "hello"
"#;
    fn test(s: RootStr) -> String {
        let mut result = String::from(&s[..]);
        result.push_str(" world");
        result
    }

    let vm = make_vm();
    vm.define_global("test", primitive!(1 test)).unwrap();

    let result = Compiler::new()
        .run_expr::<String>(&vm, "<top>", expr)
        .wait()
        .unwrap();
    let expected = ("hello world".to_string(), Type::string());

    assert_eq!(result, expected);
}

#[test]
fn array() {
    let _ = ::env_logger::init();

    let expr = r#"
sum_bytes [100b, 42b, 3b, 15b]
"#;
    fn sum_bytes(s: &[u8]) -> u8 {
        s.iter().fold(0, |acc, b| acc + b)
    }

    let vm = make_vm();
    vm.define_global("sum_bytes", primitive!(1 sum_bytes)).unwrap();

    let result = Compiler::new()
        .run_expr::<u8>(&vm, "<top>", expr)
        .wait()
        .unwrap_or_else(|err| panic!("{}", err));
    let expected = (160, Type::byte());

    assert_eq!(result, expected);
}

#[test]
fn return_finished_future() {
    let _ = ::env_logger::init();

    fn add(x: i32, y: i32) -> FutureResult<BoxFuture<i32, Error>> {
        FutureResult(Ok(x + y).into_future().boxed())
    }

    let expr = r#"
    add 1 2
"#;

    let vm = make_vm();
    vm.define_global("add", primitive!(2 add)).unwrap();

    let result = Compiler::new()
        .run_expr::<i32>(&vm, "<top>", expr)
        .wait()
        .unwrap_or_else(|err| panic!("{}", err));
    let expected = (3, Type::int());

    assert_eq!(result, expected);
}

#[test]
fn return_delayed_future() {
    let _ = ::env_logger::init();

    fn poll_n(i: i32) -> FutureResult<BoxFuture<i32, Error>> {
        use std::thread::spawn;
        use futures::sync::oneshot::channel;

        let (ping_c, ping_p) = channel();
        let (pong_c, pong_p) = channel();
        spawn(move || {
            ping_p.wait().unwrap();
            pong_c.complete(i);
        });
        FutureResult(lazy(move || {
                ping_c.complete(());
                Ok(())
            })
            .and_then(|_| pong_p.map_err(|err| Error::Message(format!("{}", err))))
            .boxed())
    }

    let expr = r#"
    poll_n 3
"#;

    let vm = make_vm();
    vm.define_global("poll_n", primitive!(1 poll_n)).unwrap();

    let result = Compiler::new()
        .run_expr::<i32>(&vm, "<top>", expr)
        .wait()
        .unwrap_or_else(|err| panic!("{}", err));
    let expected = (3, Type::int());

    assert_eq!(result, expected);
}

#[test]
fn io_future() {
    use gluon_vm::api::IO;

    let _ = ::env_logger::init();

    fn test(_: ()) -> FutureResult<BoxFuture<IO<i32>, Error>> {
        FutureResult(Ok(IO::Value(123)).into_future().boxed())
    }

    let expr = r#"
    let { applicative_IO, monad_IO } = import "std/prelude.glu"
    monad_IO.flat_map (\x -> applicative_IO.pure (x + 1)) (test ())
"#;

    let vm = make_vm();
    vm.define_global("test", primitive!(1 test)).unwrap();

    let result = Compiler::new()
        .run_io_expr::<IO<i32>>(&vm, "<top>", expr)
        .wait()
        .unwrap_or_else(|err| panic!("{}", err));

    assert_eq!(result.0, IO::Value(124));
}
