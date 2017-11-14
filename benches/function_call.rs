#[macro_use]
extern crate bencher;

extern crate gluon;

use bencher::{black_box, Bencher};

use gluon::{new_vm, Compiler};
use gluon::vm::thread::{Status, Thread};
use gluon::vm::api::{primitive, FunctionRef, Primitive};

// Benchmarks function calls
fn factorial(b: &mut Bencher) {
    let vm = new_vm();
    let text = r#"
    let factorial n =
        if n < 2
        then 1
        else n * factorial (n - 1)
    factorial
    "#;
    Compiler::new().load_script(&vm, "factorial", text).unwrap();
    let mut factorial: FunctionRef<fn(i32) -> i32> = vm.get_global("factorial").unwrap();
    b.iter(|| {
        let result = factorial.call(100).unwrap();
        black_box(result)
    })
}

fn factorial_tail_call(b: &mut Bencher) {
    let vm = new_vm();
    let text = r#"
    let factorial a n =
        if n < 2
        then a
        else factorial (a * n) (n - 1)
    factorial 1
    "#;
    Compiler::new().load_script(&vm, "factorial", text).unwrap();
    let mut factorial: FunctionRef<fn(i32) -> i32> = vm.get_global("factorial").unwrap();
    b.iter(|| {
        let result = factorial.call(100).unwrap();
        black_box(result)
    })
}

fn gluon_rust_boundary_overhead(b: &mut Bencher) {
    let vm = new_vm();

    extern "C" fn test_fn(_: &Thread) -> Status {
        Status::Ok
    }

    let text = r#"
    let for n f =
        if n #Int== 0 then
            ()
        else
            f n
            f n
            f n
            f n
            f n
            f n
            f n
            f n
            f n
            f n
            for (n #Int- 10) f
    for
    "#;
    Compiler::new().load_script(&vm, "test", text).unwrap();

    let mut test: FunctionRef<fn(i32, Primitive<fn(i32)>) -> ()> = vm.get_global("test").unwrap();
    b.iter(|| {
        let result = test.call(1000, primitive::<fn(i32)>("test_fn", test_fn))
            .unwrap();
        black_box(result)
    })
}

benchmark_group!(
    function_call,
    factorial,
    factorial_tail_call,
    gluon_rust_boundary_overhead
);
benchmark_main!(function_call);
