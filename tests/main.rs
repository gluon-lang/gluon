extern crate env_logger;
#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate collect_mac;
extern crate futures;
extern crate futures_cpupool;
extern crate gluon;
extern crate pulldown_cmark;
extern crate tensile;
extern crate tokio;
extern crate walkdir;

use gluon::base::ast::{Expr, Pattern, SpannedExpr};
use gluon::base::filename_to_module;
use gluon::base::symbol::Symbol;
use gluon::base::types::{ArcType, Type};

use gluon::vm::api::de::De;
use gluon::vm::api::{Getable, Hole, OpaqueValue, OwnedFunction, VmType};

use gluon::{new_vm, Compiler, RootedThread, Thread};

use std::error::Error;
use std::fmt;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};

use futures::{future, stream, Future, Stream};
use tokio::runtime::current_thread::Runtime;

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
    let paths: Vec<_> = walkdir::WalkDir::new(path)
        .into_iter()
        .filter_map(|f| {
            f.ok().and_then(|f| {
                let path = f.path();
                if path.extension().and_then(|e| e.to_str()) == Some("glu") {
                    Some(path.to_owned())
                } else {
                    None
                }
            })
        }).collect();
    assert!(!paths.is_empty(), "Expected test files");
    Ok(paths)
}

macro_rules! define_test_type {
    ($name:ident) => {
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
    };
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
                    let future = test
                        .call_async(())
                        .and_then(|test| {
                            future::result(test.vm().get_global("std.test.run")).and_then(
                                |action| {
                                    let mut action: OwnedFunction<
                                    fn(OpaqueValue<RootedThread, Test>) -> (),
                                > = action;
                                    action.call_async(test)
                                },
                            )
                        }).map_err(|err| err.to_string());
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

fn make_test<'t>(vm: &'t Thread, name: &str, filename: &Path) -> Result<TestCase, String> {
    let mut compiler = Compiler::new();

    let mut file = File::open(&filename).map_err(|err| err.to_string())?;
    let mut text = String::new();
    file.read_to_string(&mut text)
        .map_err(|err| err.to_string())?;
    let (De(test), _) = compiler
        .run_expr(&vm, &name, &text)
        .map_err(|err| err.to_string())?;
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

fn gather_doc_tests(expr: &SpannedExpr<Symbol>) -> Vec<(String, String)> {
    use gluon::base::ast::{walk_expr, Visitor};

    fn make_test(comment: &str) -> String {
        let mut parser = pulldown_cmark::Parser::new(comment);

        let mut source = String::new();
        loop {
            let content = match parser.next() {
                Some(pulldown_cmark::Event::Start(pulldown_cmark::Tag::CodeBlock(code))) => code,
                None => break,
                _ => continue,
            };
            source.push_str(&content);
            loop {
                match parser.next() {
                    Some(pulldown_cmark::Event::End(pulldown_cmark::Tag::CodeBlock(content))) => {
                        source.push_str(&content);
                        break;
                    }
                    Some(pulldown_cmark::Event::Text(content)) => {
                        source.push_str(&content);
                    }
                    None => break,
                    _ => continue,
                }
            }
        }
        source
    }

    struct DocVisitor(Vec<(String, String)>);
    impl<'a> Visitor<'a> for DocVisitor {
        type Ident = Symbol;

        fn visit_expr(&mut self, expr: &SpannedExpr<Symbol>) {
            match expr.value {
                Expr::LetBindings(ref binds, _) => {
                    for bind in binds {
                        if let Some(ref comment) = bind.metadata.comment {
                            let mut source = make_test(&comment.content);
                            if !source.is_empty() {
                                let name = match bind.name.value {
                                    Pattern::Ident(ref id) => id.name.declared_name(),
                                    _ => "Unknown",
                                };
                                self.0.push((format!("{}", name), String::from(source)));
                            }
                        }
                    }
                }
                Expr::TypeBindings(ref binds, _) => {
                    for bind in binds {
                        if let Some(ref comment) = bind.metadata.comment {
                            let mut source = make_test(&comment.content);
                            if !source.is_empty() {
                                self.0.push((
                                    format!("{}", bind.name.value.declared_name()),
                                    String::from(source),
                                ));
                            }
                        }
                    }
                }
                _ => (),
            }
            walk_expr(self, expr);
        }
    }
    let mut visitor = DocVisitor(Vec::new());

    visitor.visit_expr(expr);

    visitor.0
}

fn run_doc_tests<'t>(
    vm: &'t Thread,
    name: &str,
    filename: &Path,
) -> Result<Vec<tensile::Test<String>>, String> {
    let mut compiler = Compiler::new();

    let mut file = File::open(&filename).map_err(|err| err.to_string())?;
    let mut text = String::new();
    file.read_to_string(&mut text)
        .map_err(|err| err.to_string())?;

    let (expr, _, _) = compiler
        .extract_metadata(&vm, &name, &text)
        .map_err(|err| err.to_string())?;

    let tests = gather_doc_tests(&expr);
    Ok(tests
        .into_iter()
        .map(move |(test_name, test_source)| {
            let vm = vm.new_thread().unwrap();
            tensile::test(test_name.clone(), move || {
                Compiler::new()
                    .run_expr::<OpaqueValue<&Thread, Hole>>(&vm, &test_name, &test_source)
                    .map_err(|err| err.to_string())?;
                Ok(())
            })
        }).collect())
}

fn main_() -> Result<(), Box<Error>> {
    let _ = ::env_logger::try_init();
    let args: Vec<_> = ::std::env::args().collect();
    let filter = if args.len() > 1 && args.last().unwrap() != "main" {
        args.last()
    } else {
        None
    };

    let file_filter = filter.as_ref().map_or(false, |f| f.starts_with("@"));
    let filter = filter.as_ref().map(|f| f.trim_left_matches('@'));

    let vm = new_vm();
    Compiler::new().load_file(&vm, "std/test.glu")?;

    let iter = test_files("tests/pass")?.into_iter();

    let pool = futures_cpupool::CpuPool::new(1);
    let mut runtime = tokio::runtime::Runtime::new()?;
    let pass_tests_future = stream::futures_ordered(
        iter.filter_map(|filename| {
            let name = filename_to_module(filename.to_str().unwrap_or("<unknown>"));

            match filter {
                Some(ref filter) if file_filter && !name.contains(&filter[..]) => None,
                _ => Some((filename, name)),
            }
        }).map(|(filename, name)| {
            let vm = vm.new_thread().unwrap();

            let name2 = name.clone();
            pool.spawn_fn(move || make_test(&vm, &name, &filename))
                .then(|result| -> Result<_, String> {
                    Ok(match result {
                        Ok(test) => test.into_tensile_test(),
                        Err(err) => tensile::test(name2, || Err(err)),
                    })
                })
        }),
    ).collect();
    let pass_tests = runtime.block_on(pass_tests_future)?;

    let iter = test_files("tests/fail")?
        .into_iter()
        .filter(|filename| !filename.to_string_lossy().contains("deps"));

    let fail_tests = iter
        .filter_map(|filename| {
            let name = filename_to_module(filename.to_str().unwrap_or("<unknown>"));

            match filter {
                Some(ref filter) if file_filter && !name.contains(&filter[..]) => None,
                _ => Some((filename, name)),
            }
        }).map(|(filename, name)| {
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

    let doc_tests = test_files("std")?
        .into_iter()
        .filter_map(|filename| {
            let name = filename_to_module(filename.to_str().unwrap_or("<unknown>"));

            match filter {
                Some(ref filter) if file_filter && !name.contains(&filter[..]) => None,
                _ => Some((filename, name)),
            }
        }).map(|(filename, name)| {
            let vm = vm.new_thread().unwrap();
            match run_doc_tests(&vm, &name, &filename) {
                Ok(tests) => tensile::group(name.clone(), tests),
                Err(err) => tensile::test(name.clone(), || Err(err)),
            }
        }).collect();

    let mut runtime = Runtime::new()?;
    runtime.block_on(tensile::console_runner(
        tensile::group(
            "main",
            vec![
                tensile::group("pass", pass_tests),
                tensile::group("fail", fail_tests),
                tensile::group("doc", doc_tests),
            ],
        ),
        &tensile::Options::default().filter(filter.map_or("", |s| &s[..])),
    ))?;
    Ok(())
}
