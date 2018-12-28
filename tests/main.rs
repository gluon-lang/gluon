#![feature(futures_api, arbitrary_self_types, async_await, await_macro)]

extern crate env_logger;
#[macro_use]
extern crate log;
#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate collect_mac;
extern crate failure;
#[macro_use]
extern crate failure_derive;
extern crate futures;
extern crate gluon;
extern crate pulldown_cmark;
extern crate tensile;
extern crate tokio;
extern crate walkdir;

use gluon::base::ast::{Expr, Pattern, SpannedExpr};
use gluon::base::filename_to_module;
use gluon::base::symbol::Symbol;
use gluon::base::types::{ArcType, Type};

use gluon::vm::api::{de::De, generic::A, Getable, Hole, OpaqueValue, OwnedFunction, VmType, IO};

use gluon::{new_vm, Compiler, RootedThread, Thread};

use std::{
    fs::File,
    io::{self, Read},
    path::{Path, PathBuf},
};

use futures::{
    compat::{Future01CompatExt, TokioDefaultSpawner},
    prelude::*,
    stream,
    task::SpawnExt,
};
use tokio::runtime::Runtime;

#[derive(Debug, Fail)]
enum Error {
    #[fail(display = "{}", _0)]
    Error(failure::Error),
    #[fail(display = "{}", _0)]
    Io(io::Error),
    #[fail(display = "{}", _0)]
    Gluon(gluon::Error),
    #[fail(display = "{}", _0)]
    Message(String),
}

impl From<String> for Error {
    fn from(d: String) -> Error {
        Error::Message(d)
    }
}

impl<'a> From<&'a str> for Error {
    fn from(d: &'a str) -> Error {
        Error::Message(d.to_string())
    }
}

impl From<failure::Error> for Error {
    fn from(d: failure::Error) -> Error {
        Error::Error(d)
    }
}

impl From<io::Error> for Error {
    fn from(d: io::Error) -> Error {
        Error::Io(d)
    }
}

impl From<gluon::Error> for Error {
    fn from(d: gluon::Error) -> Error {
        Error::Gluon(d)
    }
}

fn main() {
    let mut runtime = Runtime::new().unwrap();
    if let Err(err) = runtime.block_on((async { await!(main_()) }).boxed().compat()) {
        assert!(false, "{}", err);
    }
}

fn test_files(path: &str) -> Result<Vec<PathBuf>, Error> {
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
        })
        .collect();
    assert!(!paths.is_empty(), "Expected test files");
    Ok(paths)
}

macro_rules! define_test_type {
    ($name:ident $($args: ident)*) => {
        impl VmType for $name {
            type Type = $name;
            fn make_type(vm: &Thread) -> ArcType {
                let typ = concat!("std.test.", stringify!($name));
                Type::app(
                    (*vm.global_env().get_env().find_type_info(typ).unwrap())
                        .clone()
                        .into_type(),
                    collect![$($args::make_type(vm),)* Type::unit()],
                )
            }
        }
    };
}

type TestEff = OpaqueValue<RootedThread, TestEffIO>;
type TestFn = OwnedFunction<fn(()) -> TestEff>;

#[derive(Deserialize)]
enum TestCase {
    Test { name: String, test: TestFn },
    Group { name: String, tests: Vec<TestCase> },
}

define_test_type! { TestCase Hole }

struct TestEffIO;

define_test_type! { TestEffIO A }

struct GluonTestable<F>(F);

impl<F> GluonTestable<F>
where
    F: Future<Output = Result<(), Error>> + Send + 'static,
{
    fn new(f: F) -> Self {
        GluonTestable(f)
    }
}

impl<F> tensile::Testable for GluonTestable<F>
where
    F: Future<Output = Result<(), Error>> + Send + 'static,
{
    type Error = Error;

    fn test(self) -> tensile::TestFuture<Self::Error> {
        Box::new(self.0.boxed().compat())
    }
}

fn make_tensile_test(name: String, test: TestFn) -> tensile::Test<Error> {
    let mut test = ::std::panic::AssertUnwindSafe(test);
    tensile::test(name, move || {
        let future = test
            .call_async(())
            .and_then(|test| {
                future::result(test.vm().get_global("std.test.run_io")).and_then(|action| {
                    let mut action: OwnedFunction<
                        fn(OpaqueValue<RootedThread, TestEffIO>) -> IO<()>,
                    > = action;
                    action.call_async(test).map(|_| ())
                })
            })
            .map_err(gluon::Error::from)
            .map_err(Error::from);
        GluonTestable(::std::panic::AssertUnwindSafe(future))
    })
}

impl TestCase {
    fn into_tensile_test(self) -> tensile::Test<Error> {
        match self {
            TestCase::Test { name, test } => {
                let child_thread = test.vm().new_thread().unwrap();
                let test = TestFn::from_value(&child_thread, test.get_variant());
                make_tensile_test(name, test)
            }
            TestCase::Group { name, tests } => tensile::Test::Group {
                name,
                tests: tests.into_iter().map(TestCase::into_tensile_test).collect(),
            },
        }
    }
}

fn new_compiler() -> Compiler {
    Compiler::new().task_spawner(Some(TokioDefaultSpawner))
}

fn dispatch<F>(f: F) -> impl Future<Output = F::Output> + Send + 'static
where
    F: Future + Send + 'static,
    F::Output: Send,
{
    TokioDefaultSpawner.spawn_with_handle(f).unwrap()
}

async fn make_test<'t>(
    vm: &'t Thread,
    name: &'t str,
    filename: &'t Path,
) -> Result<TestCase, Error> {
    trace!("TEST {}", name);
    let mut compiler = new_compiler();

    let mut file = File::open(&filename)?;
    let mut text = String::new();
    file.read_to_string(&mut text)?;
    let (De(test), _) = await!(compiler.run_expr_async(&vm, &name, &text))?;
    trace!("DON {}", name);
    Ok(test)
}

async fn run_file<'t>(
    vm: &'t Thread,
    name: &'t str,
    filename: &'t Path,
) -> Result<(OpaqueValue<RootedThread, Hole>, ArcType), Error> {
    trace!("TEST {}", name);
    let mut compiler = new_compiler();

    let mut file = File::open(&filename)?;
    let mut text = String::new();
    file.read_to_string(&mut text)?;
    let v = await!(compiler.run_expr_async::<OpaqueValue<RootedThread, Hole>>(&vm, &name, &text))?;
    trace!("DON {}", name);
    Ok(v)
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
                            let source = make_test(&comment.content);
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
                            let source = make_test(&comment.content);
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

async fn run_doc_tests<'t>(
    vm: &'t Thread,
    name: &'t str,
    filename: &'t Path,
) -> Result<Vec<tensile::Test<Error>>, Error> {
    trace!("START DOC {}", name);
    let mut compiler = new_compiler();

    let mut file = File::open(&filename)?;
    let mut text = String::new();
    file.read_to_string(&mut text)?;

    let (expr, _, _) = await!(compiler.extract_metadata_async(&vm, &name, &text))?;

    let (mut convert_test_fn, _) = compiler.run_expr::<OwnedFunction<fn(TestEff) -> TestFn>>(
        &vm,
        "convert_test_fn",
        r"\x -> \_ -> x",
    )?;

    let tests = gather_doc_tests(&expr);
    let x = tests
        .into_iter()
        .map(move |(test_name, test_source)| {
            let vm = vm.new_thread().unwrap();

            match Compiler::new()
                .run_expr::<TestEff>(&vm, &test_name, &test_source)
                .and_then(|(test, _)| Ok(convert_test_fn.call(test)?))
            {
                Ok(test) => make_tensile_test(test_name, test),
                Err(err) => {
                    let err = ::std::panic::AssertUnwindSafe(err);
                    tensile::test(test_name, || Err(err.0.into()))
                }
            }
        })
        .collect();
    trace!("END DOC {}", name);
    Ok(x)
}

fn doc_tests(
    vm: &Thread,
    file_filter: bool,
    filter: Option<String>,
) -> Result<impl Future<Output = Vec<tensile::Test<Error>>> + 'static, Error> {
    let vm = vm.root_thread();
    Ok(stream::futures_ordered(
        test_files("std")?
            .into_iter()
            .filter_map(move |filename| {
                let name = filename_to_module(filename.to_str().unwrap_or("<unknown>"));

                match filter {
                    Some(ref filter) if file_filter && !name.contains(&filter[..]) => None,
                    _ => Some((filename, name)),
                }
            })
            .map(move |(filename, name)| {
                let vm = vm.new_thread().unwrap();
                dispatch(
                    async move {
                        match await!(run_doc_tests(&vm, &name, &filename)) {
                            Ok(tests) => tensile::group(name.clone(), tests),
                            Err(err) => {
                                let err = ::std::panic::AssertUnwindSafe(err);
                                tensile::test(name.clone(), || Err(err.0))
                            }
                        }
                    },
                )
            }),
    )
    .collect())
}

async fn main_() -> Result<(), Error> {
    let _ = ::env_logger::try_init();
    let args: Vec<_> = ::std::env::args().collect();
    let filter = if args.len() > 1 && args.last().unwrap() != "main" {
        args.last().cloned()
    } else {
        None
    };

    let file_filter = filter.as_ref().map_or(false, |f| f.starts_with("@"));
    let filter = filter
        .as_ref()
        .map(|f| f.trim_start_matches('@').to_owned());

    let vm = new_vm();
    let mut compiler = new_compiler();
    await!(compiler.load_file_async(&vm, "std/test.glu"))?;

    let iter = test_files("tests/pass")?.into_iter();

    let pass_tests_future = stream::futures_ordered(
        iter.filter_map(|filename| {
            let name = filename_to_module(filename.to_str().unwrap_or("<unknown>"));

            match filter {
                Some(ref filter) if file_filter && !name.contains(&filter[..]) => None,
                _ => Some((filename, name)),
            }
        })
        .map(|(filename, name)| {
            let vm = vm.new_thread().unwrap();

            let name2 = name.clone();
            dispatch(
                async move {
                    await!(make_test(&vm, &name, &filename).then(
                        async move |result| -> Result<_, String> {
                            Ok(match result {
                                Ok(test) => test.into_tensile_test(),
                                Err(err) => {
                                    let err = ::std::panic::AssertUnwindSafe(err);
                                    tensile::test(name2, || Err(err.0))
                                }
                            })
                        }
                    ))
                },
            )
        }),
    )
    .try_collect();

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
        })
        .map(|(filename, name)| {
            let vm = vm.new_thread().unwrap();

            tensile::test(name.clone(), move || {
                let future = dispatch(
                    async move {
                        match await!(run_file(&vm, &name, &filename)) {
                            Ok(err) => Err(format!(
                                "Expected test '{}' to fail\n{:?}",
                                filename.to_str().unwrap(),
                                err.0,
                            )
                            .into()),
                            Err(_) => Ok(()),
                        }
                    },
                );
                GluonTestable::new(future)
            })
        })
        .collect();

    let doc_tests_future = doc_tests(&vm, file_filter, filter.clone())?;

    let (pass_tests, doc_tests) = await!(pass_tests_future.try_join(doc_tests_future.map(Ok)))?;

    await!(Future01CompatExt::compat(tensile::console_runner(
        tensile::group(
            "main",
            vec![
                tensile::group("pass", pass_tests),
                tensile::group("fail", fail_tests),
                tensile::group("doc", doc_tests),
            ],
        ),
        &tensile::Options::default().filter(filter.as_ref().map_or("", |s| &s[..])),
    )))?;
    Ok(())
}
