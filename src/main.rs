#[macro_use]
extern crate log;
extern crate env_logger;
extern crate clap;

extern crate embed_lang;
extern crate check;


#[cfg(not(test))]
use std::error::Error as StdError;
#[cfg(not(test))]
use embed_lang::vm::{VM, Error, load_script};
#[cfg(not(test))]
use clap::{Arg, App};

mod repl;


#[cfg(not(test))]
fn run_files(files: &[&str]) -> Result<(), Box<StdError>> {
    use std::fs::File;
    use std::io::Read;
    use std::path::Path;
    let vm = VM::new();
    let mut text = String::new();
    for file in files {
        text.clear();
        let path = Path::new(file);
        try!(File::open(path).and_then(|mut f| f.read_to_string(&mut text)));
        match path.file_stem().and_then(|s| s.to_str()) {
            Some(name) => try!(load_script(&vm, name, &text)),
            None => return Err(Error::Message(format!("Could not create a package name from '{}'", file)).into())
        }
    }
    Ok(())
}

#[cfg(not(test))]
fn main() {
    let _ = ::env_logger::init();
    let matches = App::new("embed_lang")
        .about("Executes embed_lang programs")
        .arg(Arg::with_name("INPUT")
            .multiple(true)
        )
        .arg(Arg::with_name("REPL")
             .short("i")
             .long("interactive")
             .help("Starts the repl")
             .takes_value(false)
        )
        .get_matches();
    if matches.is_present("REPL") {
        repl::run();
    }
    else if let Some(args) = matches.values_of("INPUT") {
        match run_files(&args) {
            Ok(()) => (),
            Err(msg) => println!("{}", msg)
        }
    }
    else {
        println!("{}", matches.usage());
    }
}
