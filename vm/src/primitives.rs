use std::string::String as StdString;

use Variants;
use primitives as prim;
use api::{generic, Generic, Getable, Array, MaybeError, primitive, WithVM};
use api::generic::A;
use gc::{Gc, Traverseable, DataDef, WriteOnly};
use vm::{Thread, DataStruct, VMInt, Status, Value, Result};


fn array_length(array: Array<generic::A>) -> VMInt {
    array.len() as VMInt
}

fn array_index<'vm>(array: Array<'vm, Generic<generic::A>>,
                    index: VMInt)
                    -> MaybeError<Generic<generic::A>, String> {
    match array.get(index) {
        Some(value) => MaybeError::Ok(value),
        None => MaybeError::Err(format!("{} is out of range", index)),
    }
}

fn array_append<'vm>(lhs: Array<'vm, Generic<generic::A>>,
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
        let stack = vm.get_stack();
        vm.alloc(&stack,
                 Append {
                     lhs: &lhs.fields,
                     rhs: &rhs.fields,
                 })
    };
    Getable::from_value(lhs.vm(), Variants(&Value::Data(value))).expect("Array")
}

fn string_append(lhs: WithVM<&str>, rhs: &str) -> String {
    use array::Str;
    struct StrAppend<'b> {
        lhs: &'b str,
        rhs: &'b str,
    }

    impl<'b> Traverseable for StrAppend<'b> {}

    unsafe impl<'b> DataDef for StrAppend<'b> {
        type Value = Str;
        fn size(&self) -> usize {
            ::array::Str::size_of(self.lhs.len() + self.rhs.len())
        }
        fn initialize<'w>(self, mut result: WriteOnly<'w, Str>) -> &'w mut Str {
            unsafe {
                let result = &mut *result.as_mut_ptr();
                {
                    let array = Str::as_mut_array(result);
                    ::array::Array::set_len(array, self.lhs.len() + self.rhs.len());
                    let (l, r) = array.split_at_mut(self.lhs.len());
                    l.clone_from_slice(self.lhs.as_bytes());
                    r.clone_from_slice(self.rhs.as_bytes());
                }
                result
            }
        }
    }

    let vm = lhs.vm;
    let lhs = lhs.value;
    let value = {
        let stack = vm.get_stack();
        vm.alloc(&stack,
                 StrAppend {
                     lhs: lhs,
                     rhs: rhs,
                 })
    };
    Getable::from_value(vm, Variants(&Value::String(value))).expect("Array")
}

fn string_slice(s: &str, start: usize, end: usize) -> MaybeError<&str, String> {
    if s.is_char_boundary(start) && s.is_char_boundary(end) {
        MaybeError::Ok(&s[start..end])
    } else {
        // Limit the amount of characters to print in the error message
        let mut iter = s.chars();
        for _ in iter.by_ref().take(256) {
        }
        MaybeError::Err(format!("index {} and/or {} in `{}` does not lie on a character boundary",
                                start,
                                end,
                                &s[..(s.len() - iter.as_str().len())]))
    }
}

fn trace(a: Generic<A>) {
    println!("{:?}", a.0);
}

fn show_int(i: VMInt) -> String {
    format!("{}", i)
}

fn show_float(f: f64) -> String {
    format!("{}", f)
}

fn show_char(c: char) -> String {
    format!("{}", c)
}

fn error(_: &Thread) -> Status {
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

pub fn load(vm: &Thread) -> Result<()> {
    use std::f64;
    use std::char;
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
        cbrt => f1(f64::cbrt),
        hypot => f2(f64::hypot),
        sin => f1(f64::sin),
        cos => f1(f64::cos),
        tan => f1(f64::tan),
        acos => f1(f64::acos),
        atan => f1(f64::atan),
        atan2 => f2(f64::atan2),
        sin_cos => f1(f64::sin_cos),
        exp_m1 => f1(f64::exp_m1),
        ln_1p => f1(f64::ln_1p),
        sinh => f1(f64::sinh),
        cosh => f1(f64::cosh),
        tanh => f1(f64::tanh),
        acosh => f1(f64::acosh),
        atanh => f1(f64::atanh)
    )));
    try!(vm.define_global("int",
                          record!(
        min_value => VMInt::min_value(),
        max_value => VMInt::max_value(),
        count_ones => f1(VMInt::count_ones),
        rotate_left => f2(VMInt::rotate_left),
        rotate_right => f2(VMInt::rotate_right),
        swap_bytes => f1(VMInt::swap_bytes),
        from_be => f1(VMInt::from_be),
        from_le => f1(VMInt::from_le),
        to_be => f1(VMInt::to_be),
        to_le => f1(VMInt::to_le),
        pow => f2(VMInt::pow),
        abs => f1(VMInt::abs),
        signum => f1(VMInt::signum),
        is_positive => f1(VMInt::is_positive),
        is_negative => f1(VMInt::is_negative)
    )));
    try!(vm.define_global("array",
                          record!(
        length => f1(prim::array_length),
        index => f2(prim::array_index),
        append => f2(prim::array_append)
    )));

    try!(vm.define_global("string_prim",
                          record!(
        length => f1(str::len),
        is_empty => f1(str::is_empty),
        split_at => f2(str::split_at),
        find => f2(str::find::<&str>),
        rfind => f2(str::rfind::<&str>),
        trim => f1(str::trim),
        trim_left => f1(str::trim_left),
        trim_right => f1(str::trim_right),
        compare => f2(str::cmp),
        append => f2(prim::string_append),
        eq => f2(<str as PartialEq>::eq),
        slice => f3(prim::string_slice)
    )));
    try!(vm.define_global("char",
                          record!(
        is_digit => f2(char::is_digit),
        to_digit => f2(char::to_digit),
        len_utf8 => f1(char::len_utf8),
        len_utf16 => f1(char::len_utf16),
        is_alphabetic => f1(char::is_alphabetic),
        is_lowercase => f1(char::is_lowercase),
        is_uppercase => f1(char::is_uppercase),
        is_whitespace => f1(char::is_whitespace),
        is_alphanumeric => f1(char::is_alphanumeric),
        is_control => f1(char::is_control),
        is_numeric => f1(char::is_numeric)
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
