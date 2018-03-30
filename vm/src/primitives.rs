//! Module containing functions for interacting with gluon's primitive types.
use std::result::Result as StdResult;
use std::string::String as StdString;
use std::str::FromStr;

use {Error, ExternModule, Variants};
use api::{generic, primitive, Array, Generic, Getable, Pushable, RuntimeResult, ValueRef, WithVM};
use api::generic::A;
use gc::{DataDef, Gc, Traverseable, WriteOnly};
use Result;
use vm::{Status, Thread};
use value::{Def, GcStr, Repr, ValueArray, ValueRepr};
use stack::StackFrame;
use thread::ThreadInternal;
use types::VmInt;

#[doc(hidden)]
pub mod array {
    use super::*;

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
            RuntimeResult::Return(Getable::from_value(
                lhs.vm(),
                Variants::new(&ValueRepr::Array(value).into()),
            ))
        }
    }
}

mod string {
    use super::*;
    use api::Pushable;

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
        unsafe {
            RuntimeResult::Return(Getable::from_value(
                vm,
                Variants::new(&ValueRepr::String(value).into()),
            ))
        }
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
        let value = StackFrame::current(&mut context.stack)[0].get_repr();
        match value {
            ValueRepr::Array(array) => match GcStr::from_utf8(array) {
                Ok(string) => {
                    let value = ValueRepr::String(string).into();
                    let result = context.alloc_with(
                        thread,
                        Def {
                            tag: 1,
                            elems: &[value],
                        },
                    );
                    match result {
                        Ok(data) => {
                            context.stack.push(ValueRepr::Data(data));
                            Status::Ok
                        }
                        Err(err) => {
                            let result: RuntimeResult<(), _> = RuntimeResult::Panic(err);
                            result.status_push(thread, &mut context)
                        }
                    }
                }
                Err(()) => {
                    let err: StdResult<&str, ()> = Err(());
                    err.status_push(thread, &mut context)
                }
            },
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

fn parse<T>(s: &str) -> StdResult<T, ()>
where
    T: FromStr,
{
    s.parse().map_err(|_| ())
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

fn show_byte(c: u8) -> String {
    format!("{}", c)
}

extern "C" fn error(_: &Thread) -> Status {
    // We expect a string as an argument to this function but we only return Status::Error
    // and let the caller take care of printing the message
    Status::Error
}

extern "C" fn discriminant_value(thread: &Thread) -> Status {
    let mut context = thread.context();
    let tag = {
        let mut stack = StackFrame::current(&mut context.stack);
        let value = stack.get_variant(0).unwrap();
        match value.as_ref() {
            ValueRef::Data(data) => data.tag(),
            _ => 0,
        }
    };
    tag.push(thread, &mut context).unwrap();
    Status::Ok
}

#[allow(non_camel_case_types)]
mod std {
    pub use primitives as prim;

    pub mod string {
        pub type prim = str;
    }
    pub mod char {
        pub type prim = char;
    }
    pub mod array {
        pub use primitives::array as prim;
    }
    pub mod byte {
        pub type prim = u8;
    }
    pub mod int {
        pub type prim = ::types::VmInt;
    }
    pub mod float {
        pub type prim = f64;
    }
}

#[allow(non_camel_case_types)]
pub fn load_float(thread: &Thread) -> Result<ExternModule> {
    use std::f64;
    use self::std;

    ExternModule::new(
        thread,
        record! {
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
            is_nan => primitive!(1 std::float::prim::is_nan),
            is_infinite => primitive!(1 std::float::prim::is_infinite),
            is_finite => primitive!(1 std::float::prim::is_finite),
            is_normal => primitive!(1 std::float::prim::is_normal),
            floor => primitive!(1 std::float::prim::floor),
            ceil => primitive!(1 std::float::prim::ceil),
            round => primitive!(1 std::float::prim::round),
            trunc => primitive!(1 std::float::prim::trunc),
            fract => primitive!(1 std::float::prim::fract),
            abs => primitive!(1 std::float::prim::abs),
            signum => primitive!(1 std::float::prim::signum),
            is_sign_positive => primitive!(1 std::float::prim::is_sign_positive),
            is_sign_negative => primitive!(1 std::float::prim::is_sign_negative),
            mul_add => primitive!(3 std::float::prim::mul_add),
            recip => primitive!(1 std::float::prim::recip),
            powi => primitive!(2 std::float::prim::powi),
            powf => primitive!(2 std::float::prim::powf),
            sqrt => primitive!(1 std::float::prim::sqrt),
            exp => primitive!(1 std::float::prim::exp),
            exp2 => primitive!(1 std::float::prim::exp2),
            ln => primitive!(1 std::float::prim::ln),
            log2 => primitive!(1 std::float::prim::log2),
            log10 => primitive!(1 std::float::prim::log10),
            to_degrees => primitive!(1 std::float::prim::to_degrees),
            to_radians => primitive!(1 std::float::prim::to_radians),
            max => primitive!(2 std::float::prim::max),
            min => primitive!(2 std::float::prim::min),
            cbrt => primitive!(1 std::float::prim::cbrt),
            hypot => primitive!(2 std::float::prim::hypot),
            sin => primitive!(1 std::float::prim::sin),
            cos => primitive!(1 std::float::prim::cos),
            tan => primitive!(1 std::float::prim::tan),
            acos => primitive!(1 std::float::prim::acos),
            atan => primitive!(1 std::float::prim::atan),
            atan2 => primitive!(2 std::float::prim::atan2),
            sin_cos => primitive!(1 std::float::prim::sin_cos),
            exp_m1 => primitive!(1 std::float::prim::exp_m1),
            ln_1p => primitive!(1 std::float::prim::ln_1p),
            sinh => primitive!(1 std::float::prim::sinh),
            cosh => primitive!(1 std::float::prim::cosh),
            tanh => primitive!(1 std::float::prim::tanh),
            acosh => primitive!(1 std::float::prim::acosh),
            atanh => primitive!(1 std::float::prim::atanh),
            from_int => named_primitive!(1, "std.float.prim.from_int", |i: VmInt| i as f64),
            parse => named_primitive!(1, "std.float.prim.parse", parse::<f64>)
        },
    )
}

#[allow(non_camel_case_types)]
pub fn load_byte(vm: &Thread) -> Result<ExternModule> {
    use self::std;
    ExternModule::new(
        vm,
        record! {
            min_value => std::byte::prim::min_value(),
            max_value => std::byte::prim::max_value(),
            count_ones => primitive!(1 std::byte::prim::count_ones),
            count_zeros => primitive!(1 std::byte::prim::count_zeros),
            leading_zeros => primitive!(1 std::byte::prim::leading_zeros),
            trailing_zeros => primitive!(1 std::byte::prim::trailing_zeros),
            rotate_left => primitive!(2 std::byte::prim::rotate_left),
            rotate_right => primitive!(2 std::byte::prim::rotate_right),
            swap_bytes => primitive!(1 std::byte::prim::swap_bytes),
            from_be => primitive!(1 std::byte::prim::from_be),
            from_le => primitive!(1 std::byte::prim::from_le),
            to_be => primitive!(1 std::byte::prim::to_be),
            to_le => primitive!(1 std::byte::prim::to_le),
            pow => primitive!(2 std::byte::prim::pow),
            from_int => named_primitive!(1, "std.byte.prim.from_int", |i: VmInt| i as u8),
            parse => named_primitive!(1, "std.byte.prim.parse", parse::<u8>)
        },
    )
}

#[allow(non_camel_case_types)]
pub fn load_int(vm: &Thread) -> Result<ExternModule> {
    use self::std;
    ExternModule::new(
        vm,
        record! {
            min_value => std::int::prim::min_value(),
            max_value => std::int::prim::max_value(),
            count_ones => primitive!(1 std::int::prim::count_ones),
            count_zeros => primitive!(1 std::int::prim::count_zeros),
            leading_zeros => primitive!(1 std::int::prim::leading_zeros),
            trailing_zeros => primitive!(1 std::int::prim::trailing_zeros),
            rotate_left => primitive!(2 std::int::prim::rotate_left),
            rotate_right => primitive!(2 std::int::prim::rotate_right),
            swap_bytes => primitive!(1 std::int::prim::swap_bytes),
            from_be => primitive!(1 std::int::prim::from_be),
            from_le => primitive!(1 std::int::prim::from_le),
            to_be => primitive!(1 std::int::prim::to_be),
            to_le => primitive!(1 std::int::prim::to_le),
            pow => primitive!(2 std::int::prim::pow),
            abs => primitive!(1 std::int::prim::abs),
            signum => primitive!(1 std::int::prim::signum),
            is_positive => primitive!(1 std::int::prim::is_positive),
            is_negative => primitive!(1 std::int::prim::is_negative),
            from_byte => named_primitive!(1, "std.int.prim.from_byte", |b: u8| b as VmInt),
            from_float => named_primitive!(1, "std.int.prim.from_float", |f: f64| f as VmInt),
            parse => named_primitive!(1, "std.int.prim.parse", parse::<VmInt>)
        },
    )
}

#[allow(non_camel_case_types)]
pub fn load_array(vm: &Thread) -> Result<ExternModule> {
    use self::std;
    ExternModule::new(
        vm,
        record! {
            len => primitive!(1 std::array::prim::len),
            index => primitive!(2 std::array::prim::index),
            append => primitive!(2 std::array::prim::append)
        },
    )
}

pub fn load_string(vm: &Thread) -> Result<ExternModule> {
    use self::string;
    ExternModule::new(
        vm,
        record! {
            len => primitive!(1 std::string::prim::len),
            is_empty => primitive!(1 std::string::prim::is_empty),
            split_at => primitive!(2 std::string::prim::split_at),
            find => named_primitive!(2, "std.string.prim.find", std::string::prim::find::<&str>),
            rfind => named_primitive!(2, "std.string.prim.rfind", std::string::prim::rfind::<&str>),
            starts_with => named_primitive!(
                2,
                "std.string.prim.starts_with",
                std::string::prim::starts_with::<&str>
            ),
            ends_with => named_primitive!(
                2,
                "std.string.prim.ends_with",
                std::string::prim::ends_with::<&str>
            ),
            trim => primitive!(1 std::string::prim::trim),
            trim_left => primitive!(1 std::string::prim::trim_left),
            trim_right => primitive!(1 std::string::prim::trim_right),
            append => named_primitive!(2, "std.string.prim.append", string::append),
            slice => named_primitive!(3, "std.string.prim.slice", string::slice),
            from_utf8 => primitive::<fn(Vec<u8>) -> StdResult<String, ()>>(
                "std.string.prim.from_utf8",
                string::from_utf8
            ),
            char_at => named_primitive!(2, "std.string.prim.char_at", string::char_at),
            as_bytes => primitive!(1 std::string::prim::as_bytes)
        },
    )
}

#[allow(non_camel_case_types)]
pub fn load_char(vm: &Thread) -> Result<ExternModule> {
    ExternModule::new(
        vm,
        record! {
            from_int => named_primitive!(1, "std.char.prim.from_int", ::std::char::from_u32),
            to_int => named_primitive!(1, "std.char.prim.to_int", |c: char| c as u32),
            is_digit => primitive!(2 std::char::prim::is_digit),
            to_digit => primitive!(2 std::char::prim::to_digit),
            len_utf8 => primitive!(1 std::char::prim::len_utf8),
            len_utf16 => primitive!(1 std::char::prim::len_utf16),
            is_alphabetic => primitive!(1 std::char::prim::is_alphabetic),
            is_lowercase => primitive!(1 std::char::prim::is_lowercase),
            is_uppercase => primitive!(1 std::char::prim::is_uppercase),
            is_whitespace => primitive!(1 std::char::prim::is_whitespace),
            is_alphanumeric => primitive!(1 std::char::prim::is_alphanumeric),
            is_control => primitive!(1 std::char::prim::is_control),
            is_numeric => primitive!(1 std::char::prim::is_numeric),
        },
    )
}

#[allow(non_camel_case_types, deprecated)]
pub fn load(vm: &Thread) -> Result<ExternModule> {
    use self::std;

    vm.define_global(
        "@error",
        primitive::<fn(StdString) -> Generic<A>>("@error", std::prim::error),
    )?;

    vm.define_global(
        "@string_eq",
        named_primitive!(2, "@string_eq", <str as PartialEq>::eq),
    )?;

    ExternModule::new(
        vm,
        record! {
            show_int => primitive!(1 std::prim::show_int),
            show_float => primitive!(1 std::prim::show_float),
            show_byte => primitive!(1 std::prim::show_byte),
            show_char => primitive!(1 std::prim::show_char),
            string_compare => named_primitive!(2, "std.prim.string_compare", str::cmp),
            string_eq => named_primitive!(2, "std.prim.string_eq", <str as PartialEq>::eq),
            error => primitive::<fn(StdString) -> Generic<A>>("std.prim.error", std::prim::error),
            discriminant_value => primitive::<fn(Generic<A>) -> VmInt>(
                "std.prim.discriminant_value",
                std::prim::discriminant_value
            ),
        },
    )
}
