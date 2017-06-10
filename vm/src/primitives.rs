//! Module containing functions for interacting with gluon's primitive types.
use std::string::String as StdString;
use std::result::Result as StdResult;

use {Variants, Error};
use primitives as prim;
use api::{generic, Generic, Getable, Array, RuntimeResult, primitive, WithVM};
use api::generic::A;
use gc::{Gc, Traverseable, DataDef, WriteOnly};
use Result;
use vm::{Thread, Status};
use value::{Def, GcStr, Repr, Value, ValueArray};
use stack::StackFrame;
use types::VmInt;

mod array {
    use super::*;
    use thread::ThreadInternal;

    pub fn len(array: Array<generic::A>) -> VmInt {
        array.len() as VmInt
    }

    pub fn index<'vm>(
        array: Array<'vm, Generic<generic::A>>,
        index: VmInt,
    ) -> RuntimeResult<Generic<generic::A>, String> {
        match array.get(index) {
            Some(value) => RuntimeResult::Return(value),
            None => RuntimeResult::Panic(format!("Index {} is out of range", index)),
        }
    }

    pub fn append<'vm>(
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
}

mod string {
    use super::*;
    use api::AsyncPushable;
    use thread::ThreadInternal;

    pub fn append(lhs: WithVM<&str>, rhs: &str) -> RuntimeResult<String, Error> {
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
        let value = unsafe {
            let mut context = vm.context();
            let result = context.alloc(StrAppend { lhs: lhs, rhs: rhs });
            match result {
                Ok(x) => GcStr::from_utf8_unchecked(x),
                Err(err) => return RuntimeResult::Panic(err),
            }
        };
        RuntimeResult::Return(
            Getable::from_value(vm, Variants(&Value::String(value))).expect("Array"),
        )
    }

    pub fn slice(s: &str, start: usize, end: usize) -> RuntimeResult<&str, String> {
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

    pub extern "C" fn from_utf8(thread: &Thread) -> Status {
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

    pub fn char_at(s: &str, index: usize) -> RuntimeResult<char, String> {
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

#[allow(non_camel_case_types)]
pub fn load(vm: &Thread) -> Result<()> {
    use std::f64;
    use std::char;
    type float = f64;
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
        is_nan => primitive!(1 float::is_nan),
        is_infinite => primitive!(1 float::is_infinite),
        is_finite => primitive!(1 float::is_finite),
        is_normal => primitive!(1 float::is_normal),
        floor => primitive!(1 float::floor),
        ceil => primitive!(1 float::ceil),
        round => primitive!(1 float::round),
        trunc => primitive!(1 float::trunc),
        fract => primitive!(1 float::fract),
        abs => primitive!(1 float::abs),
        signum => primitive!(1 float::signum),
        is_sign_positive => primitive!(1 float::is_sign_positive),
        is_sign_negative => primitive!(1 float::is_sign_negative),
        mul_add => primitive!(3 float::mul_add),
        recip => primitive!(1 float::recip),
        powi => primitive!(2 float::powi),
        powf => primitive!(2 float::powf),
        sqrt => primitive!(1 float::sqrt),
        exp => primitive!(1 float::exp),
        exp2 => primitive!(1 float::exp2),
        ln => primitive!(1 float::ln),
        log2 => primitive!(1 float::log2),
        log10 => primitive!(1 float::log10),
        to_degrees => primitive!(1 float::to_degrees),
        to_radians => primitive!(1 float::to_radians),
        max => primitive!(2 float::max),
        min => primitive!(2 float::min),
        cbrt => primitive!(1 float::cbrt),
        hypot => primitive!(2 float::hypot),
        sin => primitive!(1 float::sin),
        cos => primitive!(1 float::cos),
        tan => primitive!(1 float::tan),
        acos => primitive!(1 float::acos),
        atan => primitive!(1 float::atan),
        atan2 => primitive!(2 float::atan2),
        sin_cos => primitive!(1 float::sin_cos),
        exp_m1 => primitive!(1 float::exp_m1),
        ln_1p => primitive!(1 float::ln_1p),
        sinh => primitive!(1 float::sinh),
        cosh => primitive!(1 float::cosh),
        tanh => primitive!(1 float::tanh),
        acosh => primitive!(1 float::acosh),
        atanh => primitive!(1 float::atanh)
    ),
    )?;

    use types::VmInt as int;
    vm.define_global(
        "int",
        record!(
        min_value => int::min_value(),
        max_value => int::max_value(),
        count_ones => primitive!(1 int::count_ones),
        rotate_left => primitive!(2 int::rotate_left),
        rotate_right => primitive!(2 int::rotate_right),
        swap_bytes => primitive!(1 int::swap_bytes),
        from_be => primitive!(1 int::from_be),
        from_le => primitive!(1 int::from_le),
        to_be => primitive!(1 int::to_be),
        to_le => primitive!(1 int::to_le),
        pow => primitive!(2 int::pow),
        abs => primitive!(1 int::abs),
        signum => primitive!(1 int::signum),
        is_positive => primitive!(1 int::is_positive),
        is_negative => primitive!(1 int::is_negative)
    ),
    )?;

    {
        use self::array;
        vm.define_global(
            "array",
            record!(
            len => primitive!(1 array::len),
            index => primitive!(2 array::index),
            append => primitive!(2 array::append)
        ),
        )?;
    }

    type string_prim = str;
    use self::string;
    vm.define_global("string_prim",
                       record!(
        len => primitive!(1 string_prim::len),
        is_empty => primitive!(1 string_prim::is_empty),
        split_at => primitive!(2 string_prim::split_at),
        find => named_primitive!(2, "string_prim.find", string_prim::find::<&str>),
        rfind => named_primitive!(2, "string_prim.rfind", string_prim::rfind::<&str>),
        starts_with => named_primitive!(2, "string_prim.starts_with", string_prim::starts_with::<&str>),
        ends_with => named_primitive!(2, "string_prim.ends_with", string_prim::ends_with::<&str>),
        trim => primitive!(1 string_prim::trim),
        trim_left => primitive!(1 string_prim::trim_left),
        trim_right => primitive!(1 string_prim::trim_right),
        compare => named_primitive!(2, "string_prim.compare", string_prim::cmp),
        append => named_primitive!(2, "string_prim.append", string::append),
        eq => named_primitive!(2, "string_prim.eq", <str as PartialEq>::eq),
        slice => named_primitive!(3, "string_prim.slice", string::slice),
        from_utf8 =>
            primitive::<fn(Vec<u8>) -> StdResult<String, ()>>("string_prim.from_utf8",
                                                              string::from_utf8),
        char_at => named_primitive!(2, "string_prim.char_at", string::char_at),
        as_bytes => primitive!(1 string_prim::as_bytes)
    ),
    )?;
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
        show_int => primitive!(1 prim::show_int),
        show_float => primitive!(1 prim::show_float),
        show_char => primitive!(1 prim::show_char)
    ),
    )?;

    vm.define_global(
        "#error",
        primitive::<fn(StdString) -> Generic<A>>("#error", prim::error),
    )?;
    vm.define_global(
        "error",
        primitive::<fn(StdString) -> Generic<A>>("error", prim::error),
    )?;

    ::lazy::load(vm)?;
    ::reference::load(vm)?;
    Ok(())
}
