#[macro_use]
extern crate pretty_assertions;

use std::fs::File;
use std::io::Read;
use std::process::Command;

#[test]
fn fmt_repl() {
    let source = "src/repl.glu";

    let mut before = String::new();
    File::open(source).unwrap().read_to_string(&mut before).unwrap();

    let status = Command::new("gluon")
        .args(&["fmt", source])
        .spawn()
        .unwrap()
        .wait()
        .unwrap();
    assert!(status.success());

    let mut after = String::new();
    File::open(source).unwrap().read_to_string(&mut after).unwrap();

    assert_eq!(before, after);
}
