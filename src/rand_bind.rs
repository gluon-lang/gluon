//! Module containing bindings to the `rand` library.

extern crate rand;

use self::rand::{Rng, SeedableRng};

use vm::{self, ExternModule};
use vm::api::{RuntimeResult, Userdata, VmType, IO};
use vm::gc::{Gc, Traverseable};
use vm::thread::Thread;
use vm::types::VmInt;

#[derive(Debug, Clone)]
struct XorShiftRng(self::rand::XorShiftRng);

impl Userdata for XorShiftRng {}

impl VmType for XorShiftRng {
    type Type = XorShiftRng;
}

impl Traverseable for XorShiftRng {
    fn traverse(&self, _: &mut Gc) {}
}

field_decl! { value, gen }

fn next_int(_: ()) -> IO<VmInt> {
    IO::Value(rand::thread_rng().gen())
}

fn next_float(_: ()) -> IO<f64> {
    IO::Value(rand::thread_rng().gen())
}

fn gen_int_range(low: VmInt, high: VmInt) -> IO<VmInt> {
    IO::Value(rand::thread_rng().gen_range(low, high))
}

type RngNext<G> = record_type!{
    value => VmInt,
    gen => G
};

fn xor_shift_new(seed: &[VmInt]) -> RuntimeResult<XorShiftRng, String> {
    if seed.len() == 4 {
        RuntimeResult::Return(XorShiftRng(self::rand::XorShiftRng::from_seed([
            seed[0] as u32,
            seed[1] as u32,
            seed[2] as u32,
            seed[3] as u32,
        ])))
    } else {
        RuntimeResult::Panic("Expected xorshift seed to have 4 elements".to_string())
    }
}

fn xor_shift_next(gen: &XorShiftRng) -> RngNext<XorShiftRng> {
    let mut gen = gen.clone();
    record_no_decl!{
        value => gen.0.gen(),
        gen => gen
    }
}

mod std {
    pub mod random {
        pub use rand_bind as prim;
    }
}

pub fn load(vm: &Thread) -> vm::Result<ExternModule> {
    use self::std;

    vm.register_type::<XorShiftRng>("XorShiftRng", &[])?;

    ExternModule::new(
        vm,
        record!{
            next_int => primitive!(1 std::random::prim::next_int),
            next_float => primitive!(1 std::random::prim::next_float),
            gen_int_range => primitive!(2 std::random::prim::gen_int_range),
            xor_shift_new => primitive!(1 std::random::prim::xor_shift_new),
            xor_shift_next => primitive!(1 std::random::prim::xor_shift_next)
        },
    )
}
