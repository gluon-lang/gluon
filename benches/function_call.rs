#![feature(test)]

extern crate test;

extern crate gluon;

use gluon::{Compiler, new_vm};
use gluon::vm::api::FunctionRef;

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
    let text = r#"
    let { trim } = import "std/string.glu"
    let for n f =
        if n #Int== 0 then
            ()
        else
            f n
            for (n #Int- 10) f
    \n -> for n \_ -> trim ""
    "#;
    Compiler::new()
        .load_script(&vm, "test", text)
        .unwrap();
    let mut factorial: FunctionRef<fn (i32) -> ()> = vm.get_global("test").unwrap();
    b.iter(|| {
        let result = factorial.call(1000).unwrap();
        ::test::black_box(result)
    })
}
