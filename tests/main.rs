
extern crate env_logger;

extern crate embed_lang;
extern crate vm;

use vm::vm::{VM, run_expr, load_file};

use std::io::Read;
use std::fs::{File, read_dir};
use std::error::Error;

#[test]
fn main() {
    if let Err(err) = main_() {
        assert!(false, "{}", err);
    }
}
fn main_() -> Result<(), Box<Error>> {
    let vm = VM::new();
    try!(load_file(&vm, "std/prelude.hs"));
    let mut text = String::new();
    let dir = try!(read_dir("tests"));
    let iter = dir
        .filter_map(|f| {
            f.ok()
                .and_then(|f| {
                    let path = f.path();
                    if path.extension().and_then(|e| e.to_str()) == Some("hs") {
                        Some(path)
                    }
                    else {
                        None
                    }
                })
        });
    let _ = ::env_logger::init();
    for filename in iter {
        let mut file = try!(File::open(filename));
        try!(file.read_to_string(&mut text));
        try!(run_expr(&vm, &text));
    }
    Ok(())
}
