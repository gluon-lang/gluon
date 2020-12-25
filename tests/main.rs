use std::{
    io,
    path::{Path, PathBuf},
};

use {
    anyhow::anyhow,
    collect_mac::collect,
    futures::{join, prelude::*, stream, task::SpawnExt},
    serde_derive::Deserialize,
    structopt::StructOpt,
    thiserror::Error,
    tokio::fs,
};

use gluon::{
    base::{
        ast::{Expr, Pattern, SpannedExpr},
        filename_to_module,
        metadata::BaseMetadata,
        symbol::Symbol,
        types::{ArcType, Type},
    },
    new_vm_async,
    vm::api::{de::De, generic::A, Getable, Hole, OpaqueValue, OwnedFunction, VmType, IO},
    RootedThread, Thread, ThreadExt,
};

#[derive(Debug, Error)]
enum Error {
    #[error("{0}")]
    Error(anyhow::Error),

    #[error("{0}")]
    Io(io::Error),

    #[error("{0}")]
    Gluon(gluon::Error),

    #[error("{0}")]
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

impl From<anyhow::Error> for Error {
    fn from(d: anyhow::Error) -> Error {
        Error::Error(d)
    }
}

impl From<io::Error> for Error {
    fn from(d: io::Error) -> Error {
        Error::Io(d)
    }
}

impl From<gluon::vm::Error> for Error {
    fn from(d: gluon::vm::Error) -> Error {
        gluon::Error::from(d).into()
    }
}

impl From<gluon::Error> for Error {
    fn from(d: gluon::Error) -> Error {
        Error::Gluon(d)
    }
}

#[derive(StructOpt)]
#[structopt(about = "gluon tests")]
pub struct Opt {
    #[structopt(long = "jobs")]
    #[structopt(help = "How many threads to run in parallel")]
    pub jobs: Option<usize>,

    #[structopt(name = "FILTER", help = "Filters which tests to run")]
    pub filter: Vec<String>,
}

fn main() {
    let options = Opt::from_args();
    let mut runtime = {
        let mut builder = tokio::runtime::Builder::new();
        if let Some(jobs) = options.jobs {
            builder.core_threads(jobs);
        }
        builder.threaded_scheduler().build().unwrap()
    };
    runtime.block_on(async move {
        if let Err(err) = main_(&options).await {
            eprintln!("{}", err);
            std::process::exit(1);
        }
    })
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
                    vm.get_env().find_type_info(typ).unwrap().into_type(),
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
    Test(String, TestFn),
    Group(String, Vec<TestCase>),
}

define_test_type! { TestCase Hole }

struct TestEffIO;

define_test_type! { TestEffIO A }

fn make_tensile_test(name: String, test: TestFn) -> tensile::Test<Error> {
    let mut test = ::std::panic::AssertUnwindSafe(test);
    tensile::test(name, {
        tensile::Future(::std::panic::AssertUnwindSafe(async move {
            let test = test.call_async(()).await?;
            let action = test.vm().get_global("std.test.run_io")?;
            let mut action: OwnedFunction<fn(OpaqueValue<RootedThread, TestEffIO>) -> IO<()>> =
                action;
            action.call_async(test).await?;
            Ok(())
        }))
    })
}

impl TestCase {
    fn into_tensile_test(self) -> tensile::Test<Error> {
        match self {
            TestCase::Test(name, test) => {
                let child_thread = test.vm().new_thread().unwrap();
                let test = TestFn::from_value(&child_thread, test.get_variant());
                make_tensile_test(name, test)
            }
            TestCase::Group(name, tests) => tensile::Test::Group {
                name,
                tests: tests.into_iter().map(TestCase::into_tensile_test).collect(),
            },
        }
    }
}

async fn catch_unwind_test(
    name: String,
    f: impl Future<Output = tensile::Test<Error>>,
) -> tensile::Test<Error> {
    std::panic::AssertUnwindSafe(f)
        .catch_unwind()
        .await
        .unwrap_or_else(|err| {
            let err = Error::from(
                err.downcast::<String>()
                    .map(|s| *s)
                    .or_else(|e| e.downcast::<&str>().map(|s| String::from(&s[..])))
                    .unwrap_or_else(|_| "Unknown panic".to_string()),
            );
            tensile::test(name, Err(err))
        })
}

async fn make_test<'t>(vm: &'t Thread, name: &str, filename: &Path) -> Result<TestCase, Error> {
    let text = fs::read_to_string(filename).await?;
    let (De(test), _) = std::panic::AssertUnwindSafe(vm.run_expr_async(&name, &text)).await?;
    Ok(test)
}

async fn run_fail_test<'t>(vm: &'t Thread, name: &str, filename: &Path) -> Result<(), Error> {
    let source = fs::read_to_string(&filename).await?;
    let error_pattern = {
        let pat = "// ERROR";
        assert!(
            source.starts_with(pat),
            "Failure tests must have an error pattern to match against"
        );
        &source.lines().next().unwrap()[pat.len()..].trim()
    };
    match vm.load_script_async(&name, &source).await {
        Ok(err) => Err(anyhow!(
            "Expected test '{}' to fail\n{:?}",
            filename.to_str().unwrap(),
            err
        )
        .into()),
        Err(ref err) if !err.to_string().contains(error_pattern) => Err(anyhow!(
            "Error does not match the error pattern.\nExpected:\n\t`{}`\nActual:\n\t`{}`",
            error_pattern,
            err
        )
        .into()),
        Err(_) => Ok(()),
    }
}

fn gather_doc_tests(expr: &SpannedExpr<Symbol>) -> Vec<(String, String)> {
    use gluon::base::ast::{walk_expr, Visitor};

    fn make_test(comment: &str) -> String {
        let mut parser = pulldown_cmark::Parser::new(comment);

        let mut source = String::new();
        loop {
            match parser.next() {
                Some(pulldown_cmark::Event::Start(pulldown_cmark::Tag::CodeBlock(_))) => (),
                None => break,
                _ => continue,
            }
            loop {
                match parser.next() {
                    Some(pulldown_cmark::Event::End(pulldown_cmark::Tag::CodeBlock(_))) => {
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

    impl DocVisitor {
        fn make_test_from_metadata(&mut self, name: &str, metadata: &BaseMetadata<'_>) {
            if let Some(comment) = &metadata.comment() {
                let source = make_test(&comment.content);
                if !source.is_empty() {
                    self.0.push((format!("{}", name), String::from(source)));
                }
            }
        }
    }

    impl Visitor<'_, '_> for DocVisitor {
        type Ident = Symbol;

        fn visit_expr(&mut self, expr: &SpannedExpr<'_, Symbol>) {
            match &expr.value {
                Expr::LetBindings(binds, _) => {
                    for bind in &**binds {
                        if let Some(comment) = &bind.metadata.comment() {
                            let source = make_test(&comment.content);
                            if !source.is_empty() {
                                let name = match &bind.name.value {
                                    Pattern::Ident(id) => id.name.declared_name(),
                                    _ => "Unknown",
                                };
                                self.0.push((format!("{}", name), String::from(source)));
                            }
                        }
                    }
                }

                Expr::TypeBindings(binds, _) => {
                    for bind in &**binds {
                        self.make_test_from_metadata(
                            bind.name.value.declared_name(),
                            &bind.metadata,
                        );
                    }
                }

                Expr::Record { types, exprs, .. } => {
                    for field in &**types {
                        self.make_test_from_metadata(field.name.declared_name(), &field.metadata);
                    }
                    for field in &**exprs {
                        self.make_test_from_metadata(field.name.declared_name(), &field.metadata);
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
    name: &str,
    filename: &Path,
) -> Result<Vec<tensile::Test<Error>>, Error> {
    let text = fs::read_to_string(filename).await?;

    let (expr, _, _) = vm.extract_metadata(&name, &text).await?;

    let convert_test_fn =
        vm.get_global::<OwnedFunction<fn(TestEff) -> TestFn>>("convert_test_fn")?;

    let tests = gather_doc_tests(&expr.expr());
    Ok(tests
        .into_iter()
        .map(move |(test_name, test_source)| {
            let mut convert_test_fn = convert_test_fn.clone();
            catch_unwind_test(test_name.clone(), async move {
                let vm = vm.new_thread().unwrap();

                match vm
                    .run_expr_async::<TestEff>(&test_name, &test_source)
                    .and_then(|(test, _)| async { Ok(convert_test_fn.call_async(test).await?) })
                    .await
                {
                    Ok(test) => make_tensile_test(test_name, test),
                    Err(err) => {
                        let err = ::std::panic::AssertUnwindSafe(err);
                        tensile::test(test_name, || Err(err.0.into()))
                    }
                }
            })
        })
        .collect::<stream::FuturesOrdered<_>>()
        .collect()
        .await)
}

async fn main_(options: &Opt) -> Result<(), Error> {
    let _ = ::env_logger::try_init();

    let file_filters = options
        .filter
        .iter()
        .filter(|f| f.starts_with("@"))
        .map(|f| f.trim_start_matches('@'))
        .collect::<Vec<_>>();
    let filter = options.filter.iter().find(|f| !f.starts_with("@"));

    let filter_fn = |filename: PathBuf| {
        let name = filename_to_module(filename.to_str().unwrap_or("<unknown>"));

        if file_filters.is_empty() || file_filters.iter().any(|filter| name.contains(&filter[..])) {
            Some((filename, name))
        } else {
            None
        }
    };

    let vm = new_vm_async().await;
    vm.load_file_async("std/test.glu").await?;

    let iter = test_files("tests/pass")?.into_iter();

    struct TokioSpawn;
    impl futures::task::Spawn for TokioSpawn {
        fn spawn_obj(
            &self,
            future: futures::task::FutureObj<'static, ()>,
        ) -> Result<(), futures::task::SpawnError> {
            tokio::spawn(future);
            Ok(())
        }
    }

    let pool = TokioSpawn;
    let pass_tests_future = iter
        .filter_map(&filter_fn)
        .map(|(filename, name)| {
            let vm = vm.new_thread().unwrap();

            let name2 = name.clone();
            pool.spawn_with_handle(catch_unwind_test(name.clone(), async move {
                match make_test(&vm, &name, &filename).await {
                    Ok(test) => test.into_tensile_test(),
                    Err(err) => {
                        let err = ::std::panic::AssertUnwindSafe(err);
                        tensile::test(name2, || Err(err.0))
                    }
                }
            }))
            .expect("Could not spawn test future")
        })
        .collect::<stream::FuturesOrdered<_>>()
        .collect::<Vec<_>>();

    let fail_tests = test_files("tests/fail")?
        .into_iter()
        .filter(|filename| !filename.to_string_lossy().contains("deps"))
        .filter_map(&filter_fn)
        .map(|(filename, name)| {
            let vm = vm.new_thread().unwrap();

            tensile::test(
                name.clone(),
                tensile::Future(std::panic::AssertUnwindSafe(async move {
                    run_fail_test(&vm, &name, &filename).await
                })),
            )
        })
        .collect();

    vm.load_script_async("convert_test_fn", r"\x -> \_ -> x")
        .await?;

    let doc_tests_future = test_files("std")?
        .into_iter()
        .filter_map(&filter_fn)
        .map(|(filename, name)| {
            let vm = vm.new_thread().unwrap();
            pool.spawn_with_handle(catch_unwind_test(name.clone(), async move {
                match run_doc_tests(&vm, &name, &filename).await {
                    Ok(tests) => tensile::group(name.clone(), tests),
                    Err(err) => {
                        let err = ::std::panic::AssertUnwindSafe(err);
                        tensile::test(name.clone(), || Err(err.0))
                    }
                }
            }))
            .expect("Could not spawn test future")
        })
        .collect::<stream::FuturesOrdered<_>>()
        .collect::<Vec<_>>();

    let (pass_tests, doc_tests) = join!(pass_tests_future, doc_tests_future);

    let report = tensile::tokio_console_runner(
        tensile::group(
            "main",
            vec![
                tensile::group("pass", pass_tests),
                tensile::group("fail", fail_tests),
                tensile::group("doc", doc_tests),
            ],
        ),
        &tensile::Options::default().filter(filter.map_or("", |s| &s[..])),
    )
    .await?;
    if !report.passes() {
        return Err("Some tests failed".into());
    }
    Ok(())
}
