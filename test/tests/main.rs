extern crate env_logger;

extern crate gluon;
extern crate tensile;

use gluon::base::types::ArcType;
use gluon::vm::api::{Hole, OpaqueValue};
use gluon::{new_vm, Compiler, Thread};

use std::io::Read;
use std::fmt;
use std::fs::{read_dir, File};
use std::path::{Path, PathBuf};
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

fn run_file<'t>(
    vm: &'t Thread,
    name: &str,
    filename: &Path,
) -> Result<(OpaqueValue<&'t Thread, Hole>, ArcType), String> {
    let mut compiler = Compiler::new();

    let mut file = File::open(&filename).map_err(|err| err.to_string())?;
    let mut text = String::new();
    file.read_to_string(&mut text)
        .map_err(|err| err.to_string())?;
    compiler
        .run_expr_async::<OpaqueValue<&Thread, Hole>>(&vm, &name, &text)
        .sync_or_error()
        .map_err(|err| err.to_string())
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
    let import = vm.get_macros().get("import");
    let import = import
        .as_ref()
        .and_then(|import| import.downcast_ref::<gluon::import::Import>())
        .unwrap();
    import.add_path("..");

    Compiler::new()
        .load_file_async(&vm, "std/prelude.glu")
        .sync_or_error()?;

    let iter = test_files("tests/pass")?.into_iter();

    let pass_tests = iter.map(|filename| {
        let name = filename.to_str().unwrap_or("<unknown>").to_owned();

        let vm = vm.new_thread().unwrap();

        tensile::test(name.clone(), move || -> Result<(), String> {
            run_file(&vm, &name, &filename).map(|_| ())
        })
    }).collect();

    let iter = test_files("tests/fail")?.into_iter();

    let fail_tests = iter.map(|filename| {
        let name = filename.to_str().unwrap_or("<unknown>").to_owned();

        let vm = vm.new_thread().unwrap();

        tensile::test(name.clone(), move || -> Result<(), String> {
            match run_file(&vm, &name, &filename) {
                Ok(x) => Err(format!(
                    "Expected test '{}' to fail got {:?}",
                    filename.to_str().unwrap(),
                    x
                )),
                Err(_) => Ok(()),
            }
        })
    }).collect();

    tensile::console_runner(
        tensile::group(
            "main",
            vec![
                tensile::group("pass", pass_tests),
                tensile::group("fail", fail_tests),
            ],
        ),
        &tensile::Options::default().filter(filter.map_or("", |s| &s[..])),
    ).unwrap();
    Ok(())
}
