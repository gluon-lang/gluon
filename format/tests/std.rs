extern crate gluon_base as base;
extern crate gluon_format as format;

use std::{
    env,
    fs::File,
    io::{Read, Write},
    path::Path,
};

use difference::assert_diff;

use gluon::{RootedThread, ThreadExt, VmBuilder};

fn new_vm() -> RootedThread {
    VmBuilder::new()
        .import_paths(Some(vec![".".into(), "..".into()]))
        .build()
}

fn test_format(name: &str) {
    let _ = env_logger::try_init();

    let mut contents = String::new();
    File::open(Path::new("../").join(name))
        .or_else(|_| File::open(name))
        .unwrap()
        .read_to_string(&mut contents)
        .unwrap();

    let thread = new_vm();
    let out_str = thread
        .format_expr(&mut format::Formatter::default(), name, &contents)
        .unwrap_or_else(|err| panic!("{}", err));

    if contents != out_str {
        let args: Vec<_> = env::args().collect();
        let out_path = Path::new(&args[0][..])
            .parent()
            .and_then(|p| p.parent())
            .expect("folder")
            .join(Path::new(name).file_name().unwrap());
        File::create(out_path)
            .unwrap()
            .write_all(out_str.as_bytes())
            .unwrap();

        assert_diff!(&contents, &out_str, "\n", 0);
    }
}

#[test]
fn bool() {
    test_format("std/bool.glu");
}

#[test]
fn char() {
    test_format("std/char.glu");
}

#[test]
fn function() {
    test_format("std/function.glu");
}

#[test]
fn map() {
    test_format("std/map.glu");
}

#[test]
fn option() {
    test_format("std/option.glu");
}

#[test]
fn prelude() {
    test_format("std/prelude.glu");
}

#[test]
fn result() {
    test_format("std/result.glu");
}

#[test]
fn state() {
    test_format("std/state.glu");
}

#[test]
fn stream() {
    test_format("std/stream.glu");
}

#[test]
fn string() {
    test_format("std/string.glu");
}

#[test]
fn test() {
    test_format("std/test.glu");
}

#[test]
fn types() {
    test_format("std/types.glu");
}

#[test]
fn unit() {
    test_format("std/unit.glu");
}

#[test]
fn writer() {
    test_format("std/writer.glu");
}

#[test]
fn parser() {
    test_format("std/parser.glu");
}

#[test]
fn random() {
    test_format("std/random.glu");
}

#[test]
fn repl() {
    test_format("repl/src/repl.glu");
}

#[test]
fn json_de() {
    test_format("std/json/de.glu");
}
