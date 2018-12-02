use {
    api::{
        generic::{A, B},
        Generic, Getable, WithVM,
    },
    thread::Thread,
    ExternModule, Result,
};

fn trace(a: Generic<A>) {
    println!("{:?}", a);
}

fn show(a: Generic<A>) -> String {
    format!("{:?}", a)
}

fn transmute(WithVM { vm, value: a }: WithVM<Generic<A>>) -> Generic<B> {
    Getable::from_value(vm, a.get_variant())
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
            show => primitive!(1, std::debug::show),
            transmute => primitive!(1, std::debug::transmute)
        },
    )
}
