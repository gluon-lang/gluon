#![feature(test)]

extern crate test;

extern crate base;
extern crate parser;

use base::gc::Gc;
use base::interner::Interner;

#[bench]
fn prelude(b: &mut ::test::Bencher) {
    use std::fs::File;
    use std::io::Read;
    let mut text = String::new();
    File::open("std/prelude.hs")
        .unwrap()
        .read_to_string(&mut text)
        .unwrap();
    b.iter(|| {
        let mut interner = Interner::new();
        let mut gc = Gc::new();
        let expr = ::parser::parse_tc(&mut gc, &mut interner, &text)
                       .unwrap_or_else(|err| panic!("{:?}", err));
        ::test::black_box(expr)
    })
}
