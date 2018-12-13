//! REPL for the gluon programming language
#![doc(html_root_url = "https://docs.rs/gluon_repl/0.4.1")] // # GLUON

extern crate app_dirs;
#[macro_use]
extern crate clap;
extern crate codespan;
extern crate codespan_reporting;
#[cfg(feature = "env_logger")]
extern crate env_logger;
extern crate futures;
#[macro_use]
extern crate log;
#[macro_use]
extern crate serde_derive;
extern crate structopt;
#[allow(unused_imports)]
#[macro_use]
extern crate structopt_derive;
extern crate tokio;
extern crate tokio_signal;
extern crate walkdir;

extern crate gluon;
extern crate gluon_doc;
extern crate gluon_format;
#[macro_use]
extern crate gluon_vm;
#[macro_use]
extern crate gluon_codegen;

use std::ffi::OsStr;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use codespan_reporting::termcolor;
use structopt::StructOpt;
use walkdir::WalkDir;

use futures::future;
use tokio::runtime::Runtime;

use gluon::base;
use gluon::parser;
use gluon::vm;

use base::filename_to_module;

use gluon::vm::thread::ThreadInternal;
use gluon::vm::Error as VMError;
use gluon::{new_vm, Compiler, Error, Result, Thread};

mod repl;

const APP_INFO: app_dirs::AppInfo = app_dirs::AppInfo {
    name: "gluon-repl",
    author: "gluon-lang",
};

#[derive(Copy, Clone, Debug, PartialEq, Serialize, Deserialize, VmType, Getable, Pushable)]
pub enum Color {
    Auto,
    Always,
    AlwaysAnsi,
    Never,
}

impl Into<termcolor::ColorChoice> for Color {
    fn into(self) -> termcolor::ColorChoice {
        use termcolor::ColorChoice::*;
        match self {
            Color::Auto => Auto,
            Color::Always => Always,
            Color::AlwaysAnsi => AlwaysAnsi,
            Color::Never => Never,
        }
    }
}

impl Default for Color {
    fn default() -> Color {
        Color::Auto
    }
}

impl ::std::str::FromStr for Color {
    type Err = &'static str;
    fn from_str(s: &str) -> ::std::result::Result<Self, Self::Err> {
        use Color::*;
        Ok(match s {
            "auto" => Auto,
            "always" => Always,
            "always-ansi" => AlwaysAnsi,
            "never" => Never,
            _ => return Err("Expected on of auto, always, always-ansi, never"),
        })
    }
}

#[derive(StructOpt)]
#[structopt(about = "Formats gluon source code")]
pub struct FmtOpt {
    #[structopt(name = "FILE", parse(from_os_str), help = "Formats each file")]
    input: Vec<PathBuf>,
}

#[derive(StructOpt)]
pub enum SubOpt {
    #[structopt(name = "fmt", about = "Formats gluon source code")]
    Fmt(FmtOpt),
    #[structopt(name = "doc", about = "Documents gluon source code")]
    Doc(::gluon_doc::Opt),
}

const LONG_VERSION: &str = concat!(crate_version!(), "\n", "commit: ", env!("GIT_HASH"));

#[derive(StructOpt)]
#[structopt(about = "executes gluon programs", raw(long_version = "LONG_VERSION"))]
pub struct Opt {
    #[structopt(short = "i", long = "interactive", help = "Starts the repl")]
    interactive: bool,

    #[structopt(
        long = "color",
        default_value = "auto",
        help = "Coloring: auto, always, always-ansi, never"
    )]
    color: Color,

    #[structopt(
        long = "prompt",
        short = "p",
        default_value = "> ",
        help = "String printed as the prompt for the repl"
    )]
    prompt: String,

    #[structopt(
        long = "debug",
        default_value = "none",
        help = "Debug Level: none, low, high"
    )]
    debug_level: base::DebugLevel,

    #[structopt(name = "FILE", help = "Executes each file as a gluon program")]
    input: Vec<String>,

    #[structopt(subcommand)]
    subcommand_opt: Option<SubOpt>,
}

fn run_files<I>(compiler: &mut Compiler, vm: &Thread, files: I) -> Result<()>
where
    I: IntoIterator,
    I::Item: AsRef<str>,
{
    for file in files {
        compiler.load_file(&vm, file.as_ref())?;
    }
    Ok(())
}

#[cfg(feature = "env_logger")]
fn init_env_logger() {
    let _ = ::env_logger::try_init();
}

#[cfg(not(feature = "env_logger"))]
fn init_env_logger() {}

fn format(file: &str, file_map: Arc<codespan::FileMap>) -> Result<String> {
    let mut compiler = Compiler::new();
    let thread = new_vm();

    Ok(compiler.format_expr(
        &mut gluon_format::Formatter::default(),
        &thread,
        file,
        file_map.src(),
    )?)
}

fn fmt_file(name: &Path) -> Result<()> {
    use std::fs::File;
    use std::io::Read;

    let mut buffer = String::new();
    {
        let mut input_file = File::open(name)?;
        input_file.read_to_string(&mut buffer)?;
    }

    let module_name = filename_to_module(&name.display().to_string());
    let mut code_map = codespan::CodeMap::new();
    let file_map = code_map.add_filemap(module_name.clone().into(), buffer);
    let formatted = format(&module_name, file_map.clone())?;

    // Avoid touching the .glu file if it did not change
    if file_map.src() != formatted {
        let bk_name = name.with_extension("glu.bk");
        let tmp_name = name.with_extension("tmp");
        {
            let mut backup = File::create(&*bk_name)?;
            backup.write_all(formatted.as_bytes())?;
        }
        fs::rename(name, tmp_name)?;
        fs::rename(bk_name, name)?;
    }
    Ok(())
}

fn fmt_stdio() -> Result<()> {
    use std::io::{stdin, stdout, Read};

    let mut buffer = String::new();
    stdin().read_to_string(&mut buffer)?;

    let mut code_map = codespan::CodeMap::new();
    let file_map = code_map.add_filemap("STDIN".into(), buffer);

    let formatted = format("STDIN", file_map)?;
    stdout().write_all(formatted.as_bytes())?;
    Ok(())
}

fn run(
    opt: &Opt,
    compiler: &mut Compiler,
    color: Color,
    vm: &Thread,
) -> std::result::Result<(), gluon::Error> {
    vm.global_env().set_debug_level(opt.debug_level.clone());
    match opt.subcommand_opt {
        Some(SubOpt::Fmt(ref fmt_opt)) => {
            if !fmt_opt.input.is_empty() {
                let mut gluon_files = fmt_opt
                    .input
                    .iter()
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
        }
        Some(SubOpt::Doc(ref doc_opt)) => {
            let input = &doc_opt.input;
            let output = &doc_opt.output;
            gluon_doc::generate_for_path(&new_vm(), input, output)
                .map_err(|err| format!("{}\n{}", err, err.backtrace()))?;
        }
        None => {
            if opt.interactive {
                let mut runtime = Runtime::new()?;
                let prompt = opt.prompt.clone();
                let debug_level = opt.debug_level.clone();
                runtime.block_on(future::lazy(move || repl::run(color, &prompt, debug_level)))?;
            } else if !opt.input.is_empty() {
                run_files(compiler, &vm, &opt.input)?;
            } else {
                writeln!(io::stderr(), "{}", Opt::clap().get_matches().usage())
                    .expect("Error writing help to stderr");
            }
        }
    }
    Ok(())
}

fn main() {
    init_env_logger();

    let opt = Opt::from_args();

    let mut compiler = Compiler::new().run_io(true);
    let vm = new_vm();

    if let Err(err) = run(&opt, &mut compiler, opt.color, &vm) {
        match err {
            Error::VM(VMError::Message(_)) => eprintln!("{}\n{}", err, vm.context().stacktrace(0)),
            _ => {
                let mut stderr = termcolor::StandardStream::stderr(opt.color.into());
                if let Err(err) = err.emit(&mut stderr, compiler.code_map()) {
                    eprintln!("{}", err);
                } else {
                    eprintln!("");
                }
            }
        }
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
