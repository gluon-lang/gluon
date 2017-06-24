//! Module containing functions for interacting with gluon's primitive types.
use std::string::String as StdString;
use std::result::Result as StdResult;

use {Variants, Error};
use primitives as prim;
use api::{generic, Generic, Getable, AsyncPushable, Array, RuntimeResult, primitive, WithVM};
use api::generic::A;
use gc::{Gc, Traverseable, DataDef, WriteOnly};
use Result;
use vm::{Thread, Status};
use value::{Def, GcStr, Repr, Value, ValueArray};
use stack::StackFrame;
use thread::ThreadInternal;
use types::VmInt;

fn array_length(array: Array<generic::A>) -> VmInt {
    array.len() as VmInt
}

fn array_index<'vm>(
    array: Array<'vm, Generic<generic::A>>,
    index: VmInt,
) -> RuntimeResult<Generic<generic::A>, String> {
    match array.get(index) {
        Some(value) => RuntimeResult::Return(value),
        None => RuntimeResult::Panic(format!("Index {} is out of range", index)),
    }
}

fn array_append<'vm>(
    lhs: Array<'vm, Generic<generic::A>>,
    rhs: Array<'vm, Generic<generic::A>>,
) -> RuntimeResult<Array<'vm, Generic<generic::A>>, Error> {
    struct Append<'b> {
        lhs: &'b ValueArray,
        rhs: &'b ValueArray,
    }

    impl<'b> Append<'b> {
        fn repr(&self) -> Repr {
            // Empty arrays don't have the correct representation set so choose the representation
            // of `rhs` if it is empty. (And if both are empty the representation does not matter).
            if self.lhs.len() == 0 {
                self.rhs.repr()
            } else {
                self.lhs.repr()
            }
        }
    }

    impl<'b> Traverseable for Append<'b> {
        fn traverse(&self, gc: &mut Gc) {
            self.lhs.traverse(gc);
            self.rhs.traverse(gc);
        }
    }

    unsafe impl<'b> DataDef for Append<'b> {
        type Value = ValueArray;
        fn size(&self) -> usize {
            let len = self.lhs.len() + self.rhs.len();
            ValueArray::size_of(self.repr(), len)
        }
        fn initialize<'w>(self, mut result: WriteOnly<'w, ValueArray>) -> &'w mut ValueArray {
            unsafe {
                let result = &mut *result.as_mut_ptr();
                result.set_repr(self.repr());
                result.initialize(self.lhs.iter().chain(self.rhs.iter()));
                result
            }
        }
    }
    let vm = lhs.vm();
    let value = {
        let mut context = vm.context();
        let result = context.alloc(Append {
            lhs: lhs.get_value_array(),
            rhs: rhs.get_value_array(),
        });
        match result {
            Ok(x) => x,
            Err(err) => return RuntimeResult::Panic(err),
        }
    };
    unsafe {
        RuntimeResult::Return(
            Getable::from_value(lhs.vm(), Variants::new(&Value::Array(value))).expect("Array"),
        )
    }
}

fn string_append(lhs: WithVM<&str>, rhs: &str) -> RuntimeResult<String, Error> {
    struct StrAppend<'b> {
        lhs: &'b str,
        rhs: &'b str,
    }

    impl<'b> Traverseable for StrAppend<'b> {}

    unsafe impl<'b> DataDef for StrAppend<'b> {
        type Value = ValueArray;
        fn size(&self) -> usize {
            use std::mem::size_of;
            size_of::<ValueArray>() + (self.lhs.len() + self.rhs.len()) * size_of::<u8>()
        }
        fn initialize<'w>(self, mut result: WriteOnly<'w, ValueArray>) -> &'w mut ValueArray {
            use value::Repr;
            unsafe {
                let result = &mut *result.as_mut_ptr();
                result.set_repr(Repr::Byte);
                result.unsafe_array_mut::<u8>().initialize(
                    self.lhs
                        .as_bytes()
                        .iter()
                        .chain(self.rhs.as_bytes())
                        .cloned(),
                );
                result
            }
        }
    }

    let vm = lhs.vm;
    let lhs = lhs.value;
    unsafe {
        let mut context = vm.context();
        let result = context.alloc(StrAppend { lhs: lhs, rhs: rhs });
        let value = match result {
            Ok(x) => GcStr::from_utf8_unchecked(x),
            Err(err) => return RuntimeResult::Panic(err),
        };
        RuntimeResult::Return(
            Getable::from_value(vm, Variants::new(&Value::String(value))).expect("Array"),
        )
    }
}

fn string_slice(s: &str, start: usize, end: usize) -> RuntimeResult<&str, String> {
    if s.is_char_boundary(start) && s.is_char_boundary(end) {
        RuntimeResult::Return(&s[start..end])
    } else {
        // Limit the amount of characters to print in the error message
        let mut iter = s.chars();
        for _ in iter.by_ref().take(256) {}
        RuntimeResult::Panic(format!(
            "index {} and/or {} in `{}` does not lie on a character \
                                      boundary",
            start,
            end,
            &s[..(s.len() - iter.as_str().len())]
        ))
    }
}

extern "C" fn from_utf8(thread: &Thread) -> Status {
    let mut context = thread.context();
    let value = StackFrame::current(&mut context.stack)[0];
    match value {
        Value::Array(array) => {
            match GcStr::from_utf8(array) {
                Ok(string) => {
                    let value = Value::String(string);
                    let result = context.alloc_with(
                        thread,
                        Def {
                            tag: 1,
                            elems: &[value],
                        },
                    );
                    match result {
                        Ok(data) => {
                            context.stack.push(Value::Data(data));
                            Status::Ok
                        }
                        Err(err) => {
                            let result: RuntimeResult<(), _> = RuntimeResult::Panic(err);
                            result.status_push(thread, &mut context)
                        }
                    }
                }
                Err(()) =>{
                    let err: StdResult<&str, ()> = Err(());
                    err.status_push(thread, &mut context)
                }
            }
        }
        _ => unreachable!(),
    }
}

fn char_at(s: &str, index: usize) -> RuntimeResult<char, String> {
    if s.is_char_boundary(index) {
        if let Some(c) = s[index..].chars().next() {
            return RuntimeResult::Return(c);
        }
    }
    let mut iter = s.chars();
    for _ in iter.by_ref().take(256) {}
    RuntimeResult::Panic(format!(
        "index {} in `{}` does not lie on a character boundary",
        index,
        &s[..(s.len() - iter.as_str().len())]
    ))
}

fn show_int(i: VmInt) -> String {
    format!("{}", i)
}

fn show_float(f: f64) -> String {
    format!("{}", f)
}

fn show_char(c: char) -> String {
    format!("{}", c)
}

extern "C" fn error(_: &Thread) -> Status {
    // We expect a string as an argument to this function but we only return Status::Error
    // and let the caller take care of printing the message
    Status::Error
}

pub fn load(vm: &Thread) -> Result<()> {
    use std::f64;
    use std::char;
    vm.define_global(
        "float",
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
        is_nan => primitive!(1 f64::is_nan),
        is_infinite => primitive!(1 f64::is_infinite),
        is_finite => primitive!(1 f64::is_finite),
        is_normal => primitive!(1 f64::is_normal),
        floor => primitive!(1 f64::floor),
        ceil => primitive!(1 f64::ceil),
        round => primitive!(1 f64::round),
        trunc => primitive!(1 f64::trunc),
        fract => primitive!(1 f64::fract),
        abs => primitive!(1 f64::abs),
        signum => primitive!(1 f64::signum),
        is_sign_positive => primitive!(1 f64::is_sign_positive),
        is_sign_negative => primitive!(1 f64::is_sign_negative),
        mul_add => primitive!(3 f64::mul_add),
        recip => primitive!(1 f64::recip),
        powi => primitive!(2 f64::powi),
        powf => primitive!(2 f64::powf),
        sqrt => primitive!(1 f64::sqrt),
        exp => primitive!(1 f64::exp),
        exp2 => primitive!(1 f64::exp2),
        ln => primitive!(1 f64::ln),
        log2 => primitive!(1 f64::log2),
        log10 => primitive!(1 f64::log10),
        to_degrees => primitive!(1 f64::to_degrees),
        to_radians => primitive!(1 f64::to_radians),
        max => primitive!(2 f64::max),
        min => primitive!(2 f64::min),
        cbrt => primitive!(1 f64::cbrt),
        hypot => primitive!(2 f64::hypot),
        sin => primitive!(1 f64::sin),
        cos => primitive!(1 f64::cos),
        tan => primitive!(1 f64::tan),
        acos => primitive!(1 f64::acos),
        atan => primitive!(1 f64::atan),
        atan2 => primitive!(2 f64::atan2),
        sin_cos => primitive!(1 f64::sin_cos),
        exp_m1 => primitive!(1 f64::exp_m1),
        ln_1p => primitive!(1 f64::ln_1p),
        sinh => primitive!(1 f64::sinh),
        cosh => primitive!(1 f64::cosh),
        tanh => primitive!(1 f64::tanh),
        acosh => primitive!(1 f64::acosh),
        atanh => primitive!(1 f64::atanh)
    ),
    )?;
    vm.define_global(
        "int",
        record!(
        min_value => VmInt::min_value(),
        max_value => VmInt::max_value(),
        count_ones => primitive!(1 VmInt::count_ones),
        rotate_left => primitive!(2 VmInt::rotate_left),
        rotate_right => primitive!(2 VmInt::rotate_right),
        swap_bytes => primitive!(1 VmInt::swap_bytes),
        from_be => primitive!(1 VmInt::from_be),
        from_le => primitive!(1 VmInt::from_le),
        to_be => primitive!(1 VmInt::to_be),
        to_le => primitive!(1 VmInt::to_le),
        pow => primitive!(2 VmInt::pow),
        abs => primitive!(1 VmInt::abs),
        signum => primitive!(1 VmInt::signum),
        is_positive => primitive!(1 VmInt::is_positive),
        is_negative => primitive!(1 VmInt::is_negative)
    ),
    )?;
    vm.define_global(
        "array",
        record!(
        length => primitive!(1 prim::array_length),
        index => primitive!(2 prim::array_index),
        append => primitive!(2 prim::array_append)
    ),
    )?;

    vm.define_global("string_prim",
                       record!(
        length => primitive!(1 str::len),
        is_empty => primitive!(1 str::is_empty),
        split_at => primitive!(2 str::split_at),
        find => primitive!(2 str::find::<&str>),
        rfind => primitive!(2 str::rfind::<&str>),
        starts_with => primitive!(2 str::starts_with::<&str>),
        ends_with => primitive!(2 str::ends_with::<&str>),
        trim => primitive!(1 str::trim),
        trim_left => primitive!(1 str::trim_left),
        trim_right => primitive!(1 str::trim_right),
        compare => primitive!(2 str::cmp),
        append => primitive!(2 prim::string_append),
        eq => primitive!(2 <str as PartialEq>::eq),
        slice => primitive!(3 prim::string_slice),
        from_utf8 => primitive::<fn(Vec<u8>) -> StdResult<String, ()>>("from_utf8", prim::from_utf8),
        char_at => primitive!(2 prim::char_at),
        as_bytes => primitive!(1 str::as_bytes)
    ))?;
    vm.define_global(
        "char",
        record!(
        is_digit => primitive!(2 char::is_digit),
        to_digit => primitive!(2 char::to_digit),
        len_utf8 => primitive!(1 char::len_utf8),
        len_utf16 => primitive!(1 char::len_utf16),
        is_alphabetic => primitive!(1 char::is_alphabetic),
        is_lowercase => primitive!(1 char::is_lowercase),
        is_uppercase => primitive!(1 char::is_uppercase),
        is_whitespace => primitive!(1 char::is_whitespace),
        is_alphanumeric => primitive!(1 char::is_alphanumeric),
        is_control => primitive!(1 char::is_control),
        is_numeric => primitive!(1 char::is_numeric)
    ),
    )?;
    vm.define_global(
        "prim",
        record!(
        show_Int => primitive!(1 prim::show_int),
        show_Float => primitive!(1 prim::show_float),
        show_Char => primitive!(1 prim::show_char)
    ),
    )?;

    vm.define_global(
        "#error",
        primitive::<fn(StdString) -> Generic<A>>(
            "#error",
            prim::error,
        ),
    )?;
    vm.define_global(
        "error",
        primitive::<fn(StdString) -> Generic<A>>(
            "error",
            prim::error,
        ),
    )?;

    ::lazy::load(vm)?;
    ::reference::load(vm)?;
    Ok(())
}
