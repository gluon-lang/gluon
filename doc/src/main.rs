extern crate env_logger;
extern crate failure;
extern crate opener;
extern crate structopt;

extern crate gluon;
extern crate gluon_doc;

use std::path::Path;

use structopt::StructOpt;

use gluon_doc::Opt;

fn main() {
    if let Err(err) = main_() {
        eprintln!("{}", err);
    }
}

fn main_() -> Result<(), failure::Error> {
    env_logger::init();

    let opt = Opt::from_args();

    gluon_doc::generate_for_path(&gluon::new_vm(), &opt.input, &opt.output)?;

    if opt.open {
        let path = Path::new(&opt.output)
            .join(&opt.input)
            .with_extension("html");
        eprintln!("Opening {}", path.display());
        opener::open(path)?;
    }

    Ok(())
}
