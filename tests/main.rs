extern crate env_logger;

extern crate gluon;
extern crate tensile;

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
    let _ = ::env_logger::init();
    let args: Vec<_> = ::std::env::args().collect();
    let filter = if args.len() > 1 && args.last().unwrap() != "main" {
        args.last()
    } else {
        None
    };

    let vm = new_vm();
    Compiler::new()
        .load_file_async(&vm, "std/prelude.glu")
        .sync_or_error()?;

    let iter = test_files("tests/pass")?.into_iter().filter(|filename| {
        filter.map_or(true, |filter| filename.to_string_lossy().contains(filter))
    });

    let mut pass_tests = Vec::new();

    for filename in iter {
        let name = filename.to_str().unwrap_or("<unknown>").to_owned();

        let vm = vm.new_thread().unwrap();

        pass_tests.push(tensile::test(name.clone(), move || -> Result<(), String> {
            let mut compiler = Compiler::new();

            let mut file = File::open(&filename).map_err(|err| err.to_string())?;
            let mut text = String::new();
            file.read_to_string(&mut text)
                .map_err(|err| err.to_string())?;
            compiler
                .run_expr_async::<OpaqueValue<&Thread, Hole>>(&vm, &name, &text)
                .sync_or_error()
                .map_err(|err| err.to_string())?;
            Ok(())
        }));
    }

    let iter = test_files("tests/fail")?.into_iter().filter(|filename| {
        filter.map_or(true, |filter| filename.to_string_lossy().contains(filter))
    });

    let mut compiler = Compiler::new();
    let mut text = String::new();

    for filename in iter {
        let mut file = File::open(&filename)?;
        text.clear();
        file.read_to_string(&mut text)?;
        let name = filename.to_str().unwrap_or("<unknown>");
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
            Err(_) => (),
        }
    }

    tensile::console_runner(
        tensile::group("main", vec![tensile::group("pass", pass_tests)]),
        &tensile::Options::default().jobs(Some(3)),
    ).unwrap();
    Ok(())
}
