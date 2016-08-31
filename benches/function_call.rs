#![feature(test)]

extern crate test;

extern crate gluon;

use gluon::{Compiler, new_vm};
use gluon::vm::thread::{Status, Thread};
use gluon::vm::api::{FunctionRef, primitive};

// Benchmarks function calls
#[bench]
fn factorial(b: &mut ::test::Bencher) {
    let vm = new_vm();
    let text = r#"
    let factorial n =
        if n < 2
        then 1
        else n * factorial (n - 1)
    factorial
    "#;
    Compiler::new()
        .load_script(&vm, "factorial", text)
        .unwrap();
    let mut factorial: FunctionRef<fn (i32) -> i32> = vm.get_global("factorial").unwrap();
    b.iter(|| {
        let result = factorial.call(100).unwrap();
        ::test::black_box(result)
    })
}

#[bench]
fn factorial_tail_call(b: &mut ::test::Bencher) {
    let vm = new_vm();
    let text = r#"
    let factorial a n =
        if n < 2
        then a
        else factorial (a * n) (n - 1)
    factorial 1
    "#;
    Compiler::new()
        .load_script(&vm, "factorial", text)
        .unwrap();
    let mut factorial: FunctionRef<fn (i32) -> i32> = vm.get_global("factorial").unwrap();
    b.iter(|| {
        let result = factorial.call(100).unwrap();
        ::test::black_box(result)
    })
}

#[bench]
fn gluon_rust_boundary_overhead(b: &mut ::test::Bencher) {
    let vm = new_vm();

    fn test_fn(_: &Thread) -> Status { Status::Ok }
    vm.define_global("test_fn", primitive::<fn (i32)>("test_fn", test_fn)).unwrap();

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
    \n -> for n test_fn
    "#;
    Compiler::new()
        .load_script(&vm, "test", text)
        .unwrap();

    let mut test: FunctionRef<fn (i32) -> ()> = vm.get_global("test").unwrap();
    b.iter(|| {
        let result = test.call(1000).unwrap();
        ::test::black_box(result)
    })
}
