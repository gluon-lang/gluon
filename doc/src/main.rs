extern crate env_logger;
extern crate failure;
extern crate structopt;

extern crate gluon;
extern crate gluon_doc;

use gluon_doc::Opt;

use structopt::StructOpt;

fn main() {
    if let Err(err) = main_() {
        eprintln!("{}", err);
    }
}

fn main_() -> Result<(), failure::Error> {
    env_logger::init();

    let opt = Opt::from_args();
    gluon_doc::generate_for_path(&gluon::new_vm(), &opt.input, &opt.output)?;
    Ok(())
}
