
extern crate env_logger;

extern crate embed_lang;
extern crate vm;

use embed_lang::vm::api::generic::A;
use embed_lang::vm::api::Generic;
use embed_lang::{new_vm, Compiler};

use std::io::Read;
use std::fmt;
use std::fs::{File, read_dir};
use std::path::PathBuf;
use std::error::Error;

#[derive(Debug)]
pub struct StringError(String);

impl fmt::Display for StringError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Error for StringError {
    fn description(&self) -> &str {
        &self.0
    }
}

#[test]
fn main() {
    if let Err(err) = main_() {
        assert!(false, "{}", err);
    }
}

fn test_files(path: &str) -> Result<Box<Iterator<Item = PathBuf>>, Box<Error>> {
    let dir = try!(read_dir(path));
    Ok(Box::new(dir.filter_map(|f| {
        f.ok()
         .and_then(|f| {
             let path = f.path();
             if path.extension().and_then(|e| e.to_str()) == Some("hs") {
                 Some(path)
             } else {
                 None
             }
         })
    })))
}

fn main_() -> Result<(), Box<Error>> {
    let vm = new_vm();
    let mut compiler = Compiler::new();
    try!(compiler.load_file(&vm, "std/prelude.hs"));
    let mut text = String::new();
    let _ = ::env_logger::init();
    for filename in try!(test_files("tests/pass")) {
        let mut file = try!(File::open(&filename));
        text.clear();
        try!(file.read_to_string(&mut text));
        let name = filename.to_str().unwrap_or("<unknown>");
        println!("test {}", name);
        try!(compiler.run_expr::<Generic<A>>(&vm, name, &text));
    }
    for filename in try!(test_files("tests/fail")) {
        let mut file = try!(File::open(&filename));
        text.clear();
        try!(file.read_to_string(&mut text));
        let name = filename.to_str().unwrap_or("<unknown>");
        println!("test {}", name);
        match compiler.run_expr::<Generic<A>>(&vm, name, &text) {
            Ok(x) => {
                return Err(StringError(format!("Expected test '{}' to fail got {:?}",
                                               filename.to_str().unwrap(),
                                               x))
                               .into())
            }
            Err(_) => (),
        }
    }
    Ok(())
}
