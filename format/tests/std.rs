extern crate gluon_base as base;
extern crate gluon_format as format;

use std::{
    env,
    fs::File,
    io::{Read, Write},
    path::{Path, PathBuf},
};

use difference::assert_diff;

use gluon::{RootedThread, ThreadExt, VmBuilder};

type Error = Box<dyn std::error::Error>;

fn new_vm() -> RootedThread {
    VmBuilder::new()
        .import_paths(Some(vec![".".into(), "..".into()]))
        .build()
}

fn test_format(name: &str) {
    let _ = env_logger::try_init();

    let mut contents = String::new();
    File::open(Path::new("../").join(name))
        .or_else(|_| File::open(name))
        .unwrap()
        .read_to_string(&mut contents)
        .unwrap();

    let thread = new_vm();
    let out_str = thread
        .format_expr(&mut format::Formatter::default(), name, &contents)
        .unwrap_or_else(|err| panic!("{}", err));

    if contents != out_str {
        let args: Vec<_> = env::args().collect();
        let out_path = Path::new(&args[0][..])
            .parent()
            .and_then(|p| p.parent())
            .expect("folder")
            .join(Path::new(name).file_name().unwrap());
        File::create(out_path)
            .unwrap()
            .write_all(out_str.as_bytes())
            .unwrap();

        assert_diff!(&contents, &out_str, "\n", 0);
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

#[tokio::main]
async fn main() {
    if let Err(err) = main_().await {
        eprintln!("{}", err);
        std::process::exit(1);
    }
}

async fn main_() -> Result<(), Error> {
    let files = test_files("../std")?;

    let report = tensile::tokio_console_runner(
        tensile::group(
            "fmt",
            files
                .into_iter()
                .chain(Some(PathBuf::from("../repl/src/repl.glu")))
                .map(|file| {
                    let name = file.display().to_string();
                    tensile::test(name.clone(), move || test_format(&name))
                })
                .collect(),
        ),
        &Default::default(),
    )
    .await?;
    if !report.passes() {
        return Err("Some tests failed".into());
    }
    Ok(())
}
