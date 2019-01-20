#[macro_use]
extern crate criterion;

extern crate gluon;

use criterion::{black_box, Bencher, Criterion};

use gluon::vm::api::{primitive, FunctionRef, Primitive};
use gluon::vm::thread::{Status, Thread};
use gluon::{new_vm, Compiler};

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
        let result = factorial.call(20).unwrap();
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
        let result = factorial.call(20).unwrap();
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
        let result = test
            .call(1000, primitive::<fn(i32)>("test_fn", test_fn))
            .unwrap();
        black_box(result)
    })
}

fn function_call_benchmark(c: &mut Criterion) {
    c.bench_function("factorial", factorial);
    c.bench_function("factorial tail call", factorial_tail_call);
    c.bench_function("gluon rust boundary overhead", gluon_rust_boundary_overhead);
}

criterion_group!(function_call, function_call_benchmark);
criterion_main!(function_call);
