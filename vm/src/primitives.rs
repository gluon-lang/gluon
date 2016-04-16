use std::cmp::Ordering;
use std::io::Read;
use std::string::String as StdString;

use primitives as prim;
use api::{generic, Generic, Getable, Array, MaybeError, primitive};
use api::generic::A;
use gc::{Gc, Traverseable, DataDef, WriteOnly};
use vm::{VM, DataStruct, VMInt, Status, Value, RootStr, Result};


pub fn array_length(array: Array<generic::A>) -> VMInt {
    array.len() as VMInt
}

pub fn array_index<'vm>(array: Array<'vm, Generic<generic::A>>,
                        index: VMInt)
                        -> MaybeError<Generic<generic::A>, String> {
    match array.get(index) {
        Some(value) => MaybeError::Ok(value),
        None => MaybeError::Err(format!("{} is out of range", index)),
    }
}

pub fn array_append<'vm>(lhs: Array<'vm, Generic<generic::A>>,
                         rhs: Array<'vm, Generic<generic::A>>)
                         -> Array<'vm, Generic<generic::A>> {
    struct Append<'b> {
        lhs: &'b [Value],
        rhs: &'b [Value],
    }

    impl<'b> Traverseable for Append<'b> {
        fn traverse(&self, gc: &mut Gc) {
            self.lhs.traverse(gc);
            self.rhs.traverse(gc);
        }
    }

    unsafe impl<'b> DataDef for Append<'b> {
        type Value = DataStruct;
        fn size(&self) -> usize {
            use std::mem::size_of;
            let len = self.lhs.len() + self.rhs.len();
            size_of::<usize>() + ::array::Array::<Value>::size_of(len)
        }
        fn initialize<'w>(self, mut result: WriteOnly<'w, DataStruct>) -> &'w mut DataStruct {
            unsafe {
                let result = &mut *result.as_mut_ptr();
                result.tag = 0;
                result.fields.initialize(self.lhs.iter().chain(self.rhs.iter()).cloned());
                result
            }
        }
    }
    let vm = lhs.vm();
    let value = {
        let stack = vm.current_frame();
        vm.alloc(&stack.stack,
                 Append {
                     lhs: &lhs.fields,
                     rhs: &rhs.fields,
                 })
    };
    Getable::from_value(lhs.vm(), Value::Data(value)).expect("Array")
}

pub fn string_length(s: RootStr) -> VMInt {
    s.len() as VMInt
}

pub fn string_append(l: RootStr, r: RootStr) -> String {
    let mut s = String::with_capacity(l.len() + r.len());
    s.push_str(&l);
    s.push_str(&r);
    s
}
pub fn string_eq(l: RootStr, r: RootStr) -> bool {
    *l == *r
}

pub fn string_compare(l: RootStr, r: RootStr) -> Ordering {
    l.cmp(&r)
}
pub fn string_slice(s: RootStr, start: VMInt, end: VMInt) -> String {
    String::from(&s[start as usize..end as usize])
}
pub fn string_find(haystack: RootStr, needle: RootStr) -> Option<VMInt> {
    haystack.find(&needle[..]).map(|i| i as VMInt)
}
pub fn string_rfind(haystack: RootStr, needle: RootStr) -> Option<VMInt> {
    haystack.rfind(&needle[..]).map(|i| i as VMInt)
}
pub fn string_trim(s: RootStr) -> String {
    String::from(s.trim())
}

pub fn trace(a: Generic<A>) {
    println!("{:?}", a.0);
}

pub fn show_int(i: VMInt) -> String {
    format!("{}", i)
}

pub fn show_float(f: f64) -> String {
    format!("{}", f)
}

pub fn show_char(c: char) -> String {
    format!("{}", c)
}

pub fn error(_: &VM) -> Status {
    // We expect a string as an argument to this function but we only return Status::Error
    // and let the caller take care of printing the message
    Status::Error
}

fn f1<A, R>(f: fn(A) -> R) -> fn(A) -> R {
    f
}
fn f2<A, B, R>(f: fn(A, B) -> R) -> fn(A, B) -> R {
    f
}
fn f3<A, B, C, R>(f: fn(A, B, C) -> R) -> fn(A, B, C) -> R {
    f
}

pub fn load(vm: &VM) -> Result<()> {
    use std::f64;
    try!(vm.define_global("float",
                          record!(
        digits => f64::DIGITS,
        epsilon => f64::EPSILON,
        infinity => f64::INFINITY,
        mantissa_digits => f64::MANTISSA_DIGITS,
        max_ => f64::MAX,
        max_10_exp => f64::MAX_10_EXP,
        max_exp => f64::MAX_EXP,
        min_ => f64::MIN,
        min_10_exp => f64::MIN_10_EXP,
        min_exp => f64::MIN_EXP,
        min_positive => f64::MIN_POSITIVE,
        nan => f64::NAN,
        neg_infinity => f64::NEG_INFINITY,
        e => f64::consts::E,
        pi => f64::consts::PI,
        radix => f64::RADIX,
        is_nan => f1(f64::is_nan),
        is_infinite => f1(f64::is_infinite),
        is_finite => f1(f64::is_finite),
        is_normal => f1(f64::is_normal),
        floor => f1(f64::floor),
        ceil => f1(f64::ceil),
        round => f1(f64::round),
        trunc => f1(f64::trunc),
        fract => f1(f64::fract),
        abs => f1(f64::abs),
        signum => f1(f64::signum),
        is_sign_positive => f1(f64::is_sign_positive),
        is_sign_negative => f1(f64::is_sign_negative),
        mul_add => f3(f64::mul_add),
        recip => f1(f64::recip),
        powi => f2(f64::powi),
        powf => f2(f64::powf),
        sqrt => f1(f64::sqrt),
        exp => f1(f64::exp),
        exp2 => f1(f64::exp2),
        ln => f1(f64::ln),
        log2 => f1(f64::log2),
        log10 => f1(f64::log10),
        to_degrees => f1(f64::to_degrees),
        to_radians => f1(f64::to_radians),
        max => f2(f64::max),
        min => f2(f64::min),
        abs_sub => f2(f64::abs_sub),
        cbrt => f1(f64::cbrt),
        hypot => f2(f64::hypot),
        sin => f1(f64::sin),
        cos => f1(f64::cos),
        tan => f1(f64::tan),
        acos => f1(f64::acos),
        atan => f1(f64::atan),
        atan2 => f2(f64::atan2),
        // TODO Implement marshalling for tuples
        //sin_cos => f1(f64::sin_cos),
        exp_m1 => f1(f64::exp_m1),
        ln_1p => f1(f64::ln_1p),
        sinh => f1(f64::sinh),
        cosh => f1(f64::cosh),
        tanh => f1(f64::tanh),
        acosh => f1(f64::acosh),
        atanh => f1(f64::atanh)
    )));
    try!(vm.define_global("array",
                          record!(
        length => f1(prim::array_length),
        index => f2(prim::array_index),
        append => f2(prim::array_append)
    )));

    try!(vm.define_global("string_prim",
                          record!(
        length => f1(prim::string_length),
        find => f2(prim::string_find),
        rfind => f2(prim::string_rfind),
        trim => f1(prim::string_trim),
        compare => f2(prim::string_compare),
        append => f2(prim::string_append),
        eq => f2(prim::string_eq),
        slice => f3(prim::string_slice)
    )));
    try!(vm.define_global("prim",
                          record!(
        show_Int => f1(prim::show_int),
        show_Float => f1(prim::show_float),
        show_Char => f1(prim::show_char)
    )));

    try!(vm.define_global("#error",
                          primitive::<fn(StdString) -> A>("#error", prim::error)));
    try!(vm.define_global("error",
                          primitive::<fn(StdString) -> A>("error", prim::error)));
    try!(vm.define_global("trace", f1(prim::trace)));

    try!(::lazy::load(vm));
    try!(::reference::load(vm));
    Ok(())
}
