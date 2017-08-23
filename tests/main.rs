extern crate env_logger;

extern crate gluon;

use gluon::vm::api::{Hole, OpaqueValue};
use gluon::{new_vm, Compiler, Thread};

use std::io::Read;
use std::fmt;
use std::fs::{read_dir, File};
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

fn test_files(path: &str) -> Result<Vec<PathBuf>, Box<Error>> {
    let dir = read_dir(path)?;
    let paths: Vec<_> = dir.filter_map(|f| {
        f.ok().and_then(|f| {
            let path = f.path();
            if path.extension().and_then(|e| e.to_str()) == Some("glu") {
                Some(path)
            } else {
                None
            }
        })
    }).collect();
    assert!(!paths.is_empty(), "Expected test files");
    Ok(paths)
}

fn main_() -> Result<(), Box<Error>> {
    let args: Vec<_> = ::std::env::args().collect();
    let filter = if args.len() > 1 && args.last().unwrap() != "main" {
        args.last()
    } else {
        None
    };

    let vm = new_vm();
    let mut compiler = Compiler::new();
    compiler
        .load_file_async(&vm, "std/prelude.glu")
        .sync_or_error()?;
    let mut text = String::new();
    let _ = ::env_logger::init();

    let iter = test_files("tests/pass")?.into_iter().filter(|filename| {
        filter.map_or(true, |filter| filename.to_string_lossy().contains(filter))
    });
    for filename in iter {
        let mut file = File::open(&filename)?;
        text.clear();
        file.read_to_string(&mut text)?;
        let name = filename.to_str().unwrap_or("<unknown>");
        println!("test {}", name);
        compiler
            .run_expr_async::<OpaqueValue<&Thread, Hole>>(&vm, name, &text)
            .sync_or_error()?;
    }

    let iter = test_files("tests/fail")?.into_iter().filter(|filename| {
        filter.map_or(true, |filter| filename.to_string_lossy().contains(filter))
    });
    for filename in iter {
        let mut file = File::open(&filename)?;
        text.clear();
        file.read_to_string(&mut text)?;
        let name = filename.to_str().unwrap_or("<unknown>");
        println!("test {}", name);
        match compiler
            .run_expr_async::<OpaqueValue<&Thread, Hole>>(&vm, name, &text)
            .sync_or_error()
        {
            Ok(x) => {
                return Err(
                    StringError(format!(
                        "Expected test '{}' to fail got {:?}",
                        filename.to_str().unwrap(),
                        x
                    )).into(),
                )
            }
            Err(er) => println!("{}", er),
        }
    }
    Ok(())
}
