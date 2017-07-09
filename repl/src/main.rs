//! REPL for the gluon programming language
#![doc(html_root_url="https://docs.rs/gluon_repl/0.4.1")] // # GLUON

#[macro_use]
extern crate log;
#[cfg(feature = "env_logger")]
extern crate env_logger;
#[macro_use]
extern crate clap;
extern crate futures;

#[macro_use]
extern crate gluon_vm;
extern crate gluon;

use std::io::{self, Write};

use gluon::base;
use gluon::parser;
use gluon::check;
use gluon::vm;

use base::error::InFile;

use gluon::{new_vm, Compiler, Thread, Error, Result};
use gluon::vm::thread::ThreadInternal;
use gluon::vm::Error as VMError;

mod repl;

fn run_files<'s, I>(vm: &Thread, files: I) -> Result<()>
where
    I: Iterator<Item = &'s str>,
{
    let mut compiler = Compiler::new();
    for file in files {
        compiler.load_file(&vm, file)?;
    }
    Ok(())
}

#[cfg(feature = "env_logger")]
fn init_env_logger() {
    let _ = ::env_logger::init();
}

#[cfg(not(feature = "env_logger"))]
fn init_env_logger() {}

fn format(writer: &mut Write, buffer: &str) -> Result<usize> {
    use gluon::parser::format_expr;

    let output = format_expr(buffer).map_err(
        |err| InFile::new("", buffer, err),
    )?;
    writer.write_all(output.as_bytes())?;
    Ok(output.len())
}

fn fmt_file(name: &str) -> Result<()> {
    use std::io::{Read, Seek, SeekFrom};
    use std::fs::{File, OpenOptions};

    let mut input_file = OpenOptions::new().read(true).write(true).open(name)?;

    let mut buffer = String::new();
    input_file.read_to_string(&mut buffer)?;

    {
        let mut backup = File::create(&format!("{}.bk", name))?;
        backup.write_all(buffer.as_bytes())?;
    }

    input_file.seek(SeekFrom::Start(0))?;
    let written = format(&mut input_file, &buffer)?;
    // Truncate the file to remove any data that were there before
    input_file.set_len(written as u64)?;
    Ok(())
}

fn fmt_stdio() -> Result<()> {
    use std::io::{Read, stdin, stdout};

    let mut buffer = String::new();
    stdin().read_to_string(&mut buffer)?;

    format(&mut stdout(), &buffer)?;
    Ok(())
}

fn run() -> std::result::Result<(), Box<std::error::Error + Send + Sync>> {
    const GLUON_VERSION: &'static str = env!("CARGO_PKG_VERSION");

    let matches = clap_app!(gluon =>
        (version: GLUON_VERSION)
        (about: "executes gluon programs")
        (@arg REPL: -i --interactive "Starts the repl")
        (@subcommand fmt =>
            (about: "Formats gluon source code")
            (@arg INPUT: ... "Formats each file")
        )
        (@arg INPUT: ... "Executes each file as a gluon program")
    ).get_matches();
    if let Some(fmt_matches) = matches.subcommand_matches("fmt") {
        if let Some(args) = fmt_matches.values_of("INPUT") {
            for arg in args {
                fmt_file(arg)?;
            }
        } else {
            fmt_stdio()?;
        }
    } else if matches.is_present("REPL") {
        repl::run()?;
    } else if let Some(args) = matches.values_of("INPUT") {
        let vm = new_vm();
        match run_files(&vm, args) {
            Ok(()) => (),
            Err(err @ Error::VM(VMError::Message(_))) => {
                return Err(
                    format!("{}\n{}", err, vm.context().stack.stacktrace(0)).into(),
                )
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

    // Need the extra stack size when compiling the program using the msvc compiler
    ::std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| if let Err(err) = run() {
            let stderr = &mut io::stderr();
            let errmsg = "Error writing to stderr";

            write!(stderr, "error: {}", err).expect(errmsg);

            ::std::process::exit(1);
        })
        .unwrap()
        .join()
        .unwrap();
}


#[cfg(test)]
mod tests {
    // If nothing else this suppresses the unused imports warnings when compiling in test mode
    #[test]
    fn execute_repl_help() {
        super::main();
    }
}
