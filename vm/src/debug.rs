use {
    api::{
        generic::{A, B},
        Generic, Getable, OpaqueRef, WithVM,
    },
    thread::Thread,
    value::ValueRepr,
    ExternModule, Result,
};

fn trace(a: Generic<A>) {
    println!("{:?}", a);
}

fn show(a: Generic<A>) -> String {
    format!("{:?}", a)
}

fn tag(a: OpaqueRef<A>) -> Option<String> {
    unsafe {
        match a.get_value().get_repr() {
            ValueRepr::Data(data) => data.poly_tag().map(|s| s.to_string()),
            _ => None,
        }
    }
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
            tag => primitive!(1, std::debug::tag),
            transmute => primitive!(1, std::debug::transmute)
        },
    )
}
