use api::generic::A;
use api::Generic;
use thread::Thread;
use {ExternModule, Result};

fn trace(a: Generic<A>) {
    println!("{:?}", a);
}

fn show(a: Generic<A>) -> String {
    format!("{:?}", a)
}

mod std {
    pub use debug;
}

pub fn load(vm: &Thread) -> Result<ExternModule> {
    use self::std;

    ExternModule::new(
        vm,
        record! {
            trace => primitive!(1, std::debug::trace),
            show => primitive!(1, std::debug::show)
        },
    )
}
