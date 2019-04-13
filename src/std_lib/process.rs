use crate::real_std::process::Command;
use crate::vm::{api::IO, thread::Thread, ExternModule, Result};

#[derive(Getable, VmType)]
#[gluon(crate_name = "::vm")]
struct CreateProcess<'a> {
    command: &'a str,
    args: Vec<&'a str>,
    env: Option<Vec<(&'a str, &'a str)>>,
    current_dir: Option<&'a str>,
}

fn execute(create: CreateProcess) -> IO<Option<i32>> {
    let mut command = Command::new(create.command);
    for arg in &create.args {
        command.arg(arg);
    }
    match create.env {
        Some(env) => {
            command.env_clear();
            for (key, value) in &env {
                command.env(key, value);
            }
        }
        None => (),
    }
    if let Some(current_dir) = create.current_dir {
        command.current_dir(current_dir);
    }
    IO::from(command.status().map(|status| status.code()))
}

mod std {
    pub mod process {
        pub use crate::std_lib::process as prim;
    }
}

pub fn load(vm: &Thread) -> Result<ExternModule> {
    ExternModule::new(
        vm,
        record! {
            execute => primitive!(1, std::process::prim::execute)
        },
    )
}
