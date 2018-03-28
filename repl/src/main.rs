//! REPL for the gluon programming language
#![doc(html_root_url = "https://docs.rs/gluon_repl/0.4.1")] // # GLUON

extern crate app_dirs;
#[macro_use]
extern crate clap;
#[cfg(feature = "env_logger")]
extern crate env_logger;
extern crate futures;
#[macro_use]
extern crate log;
#[macro_use]
extern crate serde_derive;
extern crate tokio_core;
extern crate tokio_signal;
extern crate walkdir;

extern crate gluon;
extern crate gluon_doc;
extern crate gluon_format;
#[macro_use]
extern crate gluon_vm;

use std::io::{self, Write};
use std::ffi::OsStr;
use std::path::Path;

use walkdir::WalkDir;

use gluon::base;
use gluon::parser;
use gluon::vm;

use base::error::InFile;

use gluon::{new_vm, Compiler, Error, Result, Thread};
use gluon::vm::thread::ThreadInternal;
use gluon::vm::Error as VMError;

mod repl;

const APP_INFO: app_dirs::AppInfo = app_dirs::AppInfo {
    name: "gluon-repl",
    author: "gluon-lang",
};

fn run_files<'s, I>(vm: &Thread, files: I) -> Result<()>
where
    I: Iterator<Item = &'s str>,
{
    let mut compiler = Compiler::new().run_io(true);
    for file in files {
        compiler.load_file(&vm, file)?;
    }
    Ok(())
}

#[cfg(feature = "env_logger")]
fn init_env_logger() {
    let _ = ::env_logger::try_init();
}

#[cfg(not(feature = "env_logger"))]
fn init_env_logger() {}

fn format(writer: &mut Write, buffer: &str) -> Result<usize> {
    use gluon_format::format_expr;

    let output = format_expr(buffer).map_err(|err| InFile::new("", buffer, err))?;
    writer.write_all(output.as_bytes())?;
    Ok(output.len())
}

fn fmt_file(name: &Path) -> Result<()> {
    use std::io::{Read, Seek, SeekFrom};
    use std::fs::{File, OpenOptions};

    let mut input_file = OpenOptions::new().read(true).write(true).open(name)?;

    let mut buffer = String::new();
    input_file.read_to_string(&mut buffer)?;

    {
        let mut backup = File::create(name.with_extension("glu.bk"))?;
        backup.write_all(buffer.as_bytes())?;
    }

    input_file.seek(SeekFrom::Start(0))?;
    let written = format(&mut input_file, &buffer)?;
    // Truncate the file to remove any data that were there before
    input_file.set_len(written as u64)?;
    Ok(())
}

fn fmt_stdio() -> Result<()> {
    use std::io::{stdin, stdout, Read};

    let mut buffer = String::new();
    stdin().read_to_string(&mut buffer)?;

    format(&mut stdout(), &buffer)?;
    Ok(())
}

fn run() -> std::result::Result<(), Box<std::error::Error + Send + Sync>> {
    let matches = clap_app!(gluon =>
        (version: crate_version!())
        (long_version:
            concat!(
                crate_version!(), "\n",
                "commit: ", env!("GIT_HASH")
            )
        )
        (about: "executes gluon programs")
        (@arg REPL: -i --interactive "Starts the repl")
        (@subcommand fmt =>
            (about: "Formats gluon source code")
            (@arg INPUT: ... "Formats each file")
        )
        (@subcommand doc =>
            (about: "Documents gluon source code")
            (@arg INPUT: +required "Documents the file or directory")
            (@arg OUTPUT: +required "Outputs the documentation to this directory")
        )
        (@arg INPUT: ... "Executes each file as a gluon program")
    ).get_matches();
    if let Some(fmt_matches) = matches.subcommand_matches("fmt") {
        if let Some(args) = fmt_matches.values_of("INPUT") {
            let mut gluon_files = args.into_iter()
                .flat_map(|arg| {
                    WalkDir::new(arg).into_iter().filter_map(|entry| {
                        entry.ok().and_then(|entry| {
                            if entry.file_type().is_file()
                                && entry.path().extension() == Some(OsStr::new("glu"))
                            {
                                Some(entry.path().to_owned())
                            } else {
                                None
                            }
                        })
                    })
                })
                .collect::<Vec<_>>();
            gluon_files.sort();
            gluon_files.dedup();

            for file in gluon_files {
                fmt_file(&file)?;
            }
        } else {
            fmt_stdio()?;
        }
    } else if let Some(fmt_matches) = matches.subcommand_matches("doc") {
        let input = fmt_matches.value_of("INPUT").expect("INPUT");
        let output = fmt_matches.value_of("OUTPUT").expect("OUTPUT");
        gluon_doc::generate_for_path(&new_vm(), input, output)
            .map_err(|err| format!("{}\n{}", err, err.backtrace()))?;
    } else if matches.is_present("REPL") {
        repl::run()?;
    } else if let Some(args) = matches.values_of("INPUT") {
        let vm = new_vm();
        match run_files(&vm, args) {
            Ok(()) => (),
            Err(err @ Error::VM(VMError::Message(_))) => {
                return Err(format!("{}\n{}", err, vm.context().stack.stacktrace(0)).into())
            }
            Err(err) => return Err(err.into()),
        }
    } else {
        write!(io::stderr(), "{}", matches.usage()).expect("Error writing help to stderr");
    }
    Ok(())
}

fn main() {
    init_env_logger();

    if let Err(err) = run() {
        eprintln!("error: {}", err);

        ::std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    // If nothing else this suppresses the unused imports warnings when compiling in test mode
    #[test]
    fn execute_repl_help() {
        super::main();
    }
}
