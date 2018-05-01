#[macro_use]
extern crate collect_mac;
extern crate env_logger;
extern crate failure;
extern crate futures;
extern crate futures_cpupool;
extern crate gluon;
#[macro_use]
extern crate serde_derive;
extern crate tensile;
extern crate tokio;

use gluon::base::types::{ArcType, Type};
use gluon::vm::api::{Getable, Hole, OpaqueValue, OwnedFunction, VmType};
use gluon::vm::future::FutureValue;
use gluon::vm::api::de::De;
use gluon::vm::thread::ThreadInternal;
use gluon::{new_vm, Compiler, RootedThread, Thread};

use std::io::Read;
use std::fmt;
use std::fs::{read_dir, File};
use std::path::{Path, PathBuf};
use std::error::Error;

use futures::{future, stream, Future, Stream};

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
    tokio::run(main_().map_err(|err| {
        panic!("{}", err);
    }));
}

fn test_files(path: &str) -> Result<Vec<PathBuf>, failure::Error> {
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

type TestFn = OwnedFunction<fn(()) -> OpaqueValue<RootedThread, Test>>;

#[derive(Deserialize)]
enum TestCase {
    Test { name: String, test: TestFn },
    Group { name: String, tests: Vec<TestCase> },
}

define_test_type! { TestCase }

struct Test;

define_test_type! { Test }

struct GluonTestable<F>(F);

impl<F> tensile::Testable for GluonTestable<F>
where
    F: Future<Item = (), Error = String> + Send + Sync + 'static,
{
    type Error = String;

    fn test(self) -> tensile::TestFuture<Self::Error> {
        Box::new(self.0)
    }
}

impl TestCase {
    fn into_tensile_test(self) -> tensile::Test<String> {
        match self {
            TestCase::Test { name, test } => {
                let child_thread = test.vm().new_thread().unwrap();
                let test = TestFn::from_value(&child_thread, test.get_variant());
                let mut test = ::std::panic::AssertUnwindSafe(test);
                tensile::test(name, move || {
                    let future = test.call_async(())
                        .and_then(|test| {
                            FutureValue::Future(
                                future::result(test.vm().get_global("std.test.run")).and_then(
                                    |action| {
                                        let mut action: OwnedFunction<
                                    fn(OpaqueValue<RootedThread, Test>) -> (),
                                > = action;
                                        action.call_async(test)
                                    },
                                ),
                            )
                        })
                        .map_err(|err| err.to_string());
                    GluonTestable(::std::panic::AssertUnwindSafe(future))
                })
            }
            TestCase::Group { name, tests } => tensile::Test::Group {
                name,
                tests: tests.into_iter().map(TestCase::into_tensile_test).collect(),
            },
        }
    }
}

fn make_test<'t>(vm: &'t Thread, name: &str, filename: &Path) -> Result<TestCase, failure::Error> {
    let mut compiler = Compiler::new();

    let mut file = File::open(&filename)?;
    let mut text = String::new();
    file.read_to_string(&mut text)?;
    let (De(test), _) = compiler.run_expr(&vm, &name, &text)?;
    Ok(test)
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
        .run_expr::<OpaqueValue<&Thread, Hole>>(&vm, &name, &text)
        .map_err(|err| err.to_string())
}

fn main_() -> Box<Future<Item = (), Error = failure::Error> + Send + 'static> {
    let _ = ::env_logger::try_init();
    let args: Vec<_> = ::std::env::args().collect();
    let filter = if args.len() > 1 && args.last().unwrap() != "main" {
        args.last().cloned()
    } else {
        None
    };

    let vm = new_vm();

    let pass_tests_future = {
        let vm = vm.clone();
        Compiler::new()
            .load_file_async(&vm, "std/test.glu")
            .from_err::<failure::Error>()
            .join(future::result(test_files("tests/pass")).from_err())
            .and_then(move |(_, iterable)| {
                let pool = futures_cpupool::CpuPool::new(1);
                stream::futures_ordered(iterable.into_iter().map(|filename| {
                    let name = filename.to_str().unwrap_or("<unknown>").to_owned();

                    let vm = vm.new_thread().unwrap();

                    let name2 = name.clone();
                    pool.spawn_fn(move || make_test(&vm, &name, &filename))
                        .then(|result| -> Result<_, failure::Error> {
                            Ok(match result {
                                Ok(test) => test.into_tensile_test(),
                                Err(err) => {
                                    let err_msg = err.to_string();
                                    tensile::test(name2, move || Err(err_msg))
                                }
                            })
                        })
                })).collect()
            })
    };
    Box::new(
        pass_tests_future.and_then(move |pass_tests| -> Result<_, failure::Error> {
            let iter = test_files("tests/fail")?.into_iter();

            let fail_tests = iter.map(|filename| {
                let name = filename.to_str().unwrap_or("<unknown>").to_owned();

                let vm = vm.new_thread().unwrap();

                tensile::test(name.clone(), move || -> Result<(), String> {
                    match run_file(&vm, &name, &filename) {
                        Ok(err) => Err(format!(
                            "Expected test '{}' to fail\n{:?}",
                            filename.to_str().unwrap(),
                            err.0,
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
                &tensile::Options::default().filter(filter.as_ref().map_or("", |s| &s[..])),
            ).unwrap();
            Ok(())
        }),
    )
}
