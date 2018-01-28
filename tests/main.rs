extern crate env_logger;

#[macro_use]
extern crate serde_derive;

#[macro_use]
extern crate collect_mac;

extern crate futures;
extern crate gluon;
extern crate tensile;

use gluon::base::types::{ArcType, Type};
use gluon::vm::api::{Getable, Hole, OpaqueValue, OwnedFunction, VmType, IO};
use gluon::vm::api::de::De;
use gluon::vm::thread::ThreadInternal;
use gluon::{new_vm, Compiler, RootedThread, Thread};

use futures::{future, Future};

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

macro_rules! define_test_type {
    ($name: ident) => {
        impl VmType for $name {
            type Type = $name;
            fn make_type(vm: &Thread) -> ArcType {
                let typ = concat!("std.test.", stringify!($name));
                Type::app(
                    (*vm.global_env().get_env().find_type_info(typ).unwrap())
                        .clone()
                        .into_type(),
                    collect![Type::unit()],
                )
            }
        }
    }
}

#[derive(Deserialize)]
enum TestCase {
    Test {
        name: String,
        test: OpaqueValue<RootedThread, Test>,
    },
    Group {
        name: String,
        tests: Vec<TestCase>,
    },
}

define_test_type! { TestCase }

struct Test;

define_test_type! { Test }

impl TestCase {
    fn into_tensile_test(self) -> tensile::Test<String> {
        match self {
            TestCase::Test { name, test } => {
                let test = ::std::panic::AssertUnwindSafe(test);
                tensile::test(name, move || {
                    let mut action: OwnedFunction<
                        fn(OpaqueValue<RootedThread, Test>) -> (),
                    > = test.vm()
                        .get_global("std.test.run")
                        .map_err(|err| err.to_string())?;
                    action.call(test.0).map_err(|err| err.to_string())
                })
            }
            TestCase::Group { name, tests } => tensile::Test::Group {
                name,
                tests: tests.into_iter().map(TestCase::into_tensile_test).collect(),
            },
        }
    }
}

fn make_test<'t>(vm: &'t Thread, name: &str, filename: &Path) -> Result<TestCase, String> {
    let mut compiler = Compiler::new();

    let mut file = File::open(&filename).map_err(|err| err.to_string())?;
    let mut text = String::new();
    file.read_to_string(&mut text)
        .map_err(|err| err.to_string())?;
    match compiler.run_expr_async(&vm, &name, &text).sync_or_error() {
        Ok((De(test), _)) => Ok(test),
        Err(err) => Err(err.to_string()),
    }
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
    let _ = ::env_logger::try_init();
    let args: Vec<_> = ::std::env::args().collect();
    let filter = if args.len() > 1 && args.last().unwrap() != "main" {
        args.last()
    } else {
        None
    };

    let vm = new_vm();
    Compiler::new()
        .load_file_async(&vm, "std/test.glu")
        .sync_or_error()?;

    let iter = test_files("tests/pass")?.into_iter();

    let pass_tests = iter.map(|filename| {
        let name = filename.to_str().unwrap_or("<unknown>").to_owned();

        let vm = vm.new_thread().unwrap();

        match make_test(&vm, &name, &filename) {
            Ok(test) => test.into_tensile_test(),
            Err(err) => tensile::test(name, || Err(err)),
        }
    }).collect();

    let iter = test_files("tests/fail")?.into_iter();

    let fail_tests = iter.map(|filename| {
        let name = filename.to_str().unwrap_or("<unknown>").to_owned();

        let vm = vm.new_thread().unwrap();

        tensile::test(name.clone(), move || -> Result<(), String> {
            match run_file(&vm, &name, &filename) {
                Ok(x) => Err(format!(
                    "Expected test '{}' to fail",
                    filename.to_str().unwrap(),
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
