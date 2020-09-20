use criterion::{black_box, criterion_group, criterion_main, Bencher, Criterion};

use gluon::{
    new_vm,
    vm::{
        api::{primitive, FunctionRef, Primitive},
        thread::{Status, Thread},
    },
    ThreadExt,
};

// Benchmarks function calls

fn identity(b: &mut Bencher) {
    let vm = new_vm();
    let text = r#"
    let id x = x
    id
    "#;
    vm.load_script("id", text).unwrap();
    let mut id: FunctionRef<fn(i32) -> i32> = vm.get_global("id").unwrap();
    b.iter(|| {
        let result = id.call(20).unwrap();
        black_box(result)
    })
}

fn factorial(b: &mut Bencher) {
    let vm = new_vm();
    let text = r#"
    let factorial n =
        if n < 2
        then 1
        else n * factorial (n - 1)
    factorial
    "#;
    vm.load_script("factorial", text).unwrap();
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
    vm.load_script("factorial", text).unwrap();
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
            let _ = f n
            let _ = f n
            let _ = f n
            let _ = f n
            let _ = f n
            let _ = f n
            let _ = f n
            let _ = f n
            let _ = f n
            let _ = f n
            for (n #Int- 10) f
    for
    "#;
    vm.load_script("test", text).unwrap();

    let mut test: FunctionRef<fn(i32, Primitive<fn(i32)>) -> ()> = vm.get_global("test").unwrap();
    b.iter(|| {
        let result = test
            .call(1000, primitive::<fn(i32)>("test_fn", test_fn))
            .unwrap();
        black_box(result)
    })
}

fn function_call_benchmark(c: &mut Criterion) {
    c.bench_function("identity", identity);
    c.bench_function("factorial", factorial);
    c.bench_function("factorial tail call", factorial_tail_call);
    c.bench_function("gluon rust boundary overhead", gluon_rust_boundary_overhead);
}

criterion_group!(function_call, function_call_benchmark);
criterion_main!(function_call);
