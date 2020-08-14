//! Module containing functions for interacting with gluon's primitive types.
use crate::real_std::{
    ffi::OsStr,
    fs, io,
    marker::PhantomData,
    path::{self, Path},
    result::Result as StdResult,
    str::FromStr,
    string::String as StdString,
    sync::Mutex,
};

use crate::base::types::ArcType;

use crate::{
    api::{
        generic::{self, A, S},
        primitive, Array, Getable, Opaque, OpaqueRef, Pushable, Pushed, RuntimeResult, ValueRef,
        VmType, WithVM, IO,
    },
    gc::{DataDef, Trace, WriteOnly},
    stack::{ExternState, StackFrame},
    types::VmInt,
    value::{GcStr, Repr, ValueArray},
    vm::{Status, Thread},
    Error, ExternModule, Result, Variants,
};

#[doc(hidden)]
pub mod array {
    use super::*;
    use crate::thread::ThreadInternal;

    pub fn len(array: Array<generic::A>) -> VmInt {
        array.len() as VmInt
    }

    pub(crate) fn index<'vm>(
        array: OpaqueRef<'vm, [generic::A]>,
        index: VmInt,
    ) -> RuntimeResult<OpaqueRef<'vm, generic::A>, String> {
        match array.get(index) {
            Some(value) => RuntimeResult::Return(value),
            None => RuntimeResult::Panic(format!("Index {} is out of range", index)),
        }
    }

    pub(crate) fn slice<'vm>(
        array: Array<'vm, generic::A>,
        start: usize,
        end: usize,
    ) -> RuntimeResult<Array<'vm, generic::A>, Error> {
        if start > end {
            return RuntimeResult::Panic(Error::Message(format!(
                "slice index starts at {} but ends at {}",
                start, end
            )));
        }

        if end > array.len() {
            return RuntimeResult::Panic(Error::Message(format!(
                "index {} is out of range for array of length {}",
                end,
                array.len()
            )));
        }

        #[derive(Trace)]
        #[gluon(gluon_vm)]
        struct Slice<'a> {
            start: usize,
            end: usize,
            array: &'a ValueArray,
        }

        unsafe impl<'a> DataDef for Slice<'a> {
            type Value = ValueArray;

            fn size(&self) -> usize {
                ValueArray::size_of(self.array.repr(), self.end - self.start)
            }

            fn initialize<'w>(self, mut result: WriteOnly<'w, ValueArray>) -> &'w mut ValueArray {
                unsafe {
                    let result = &mut *result.as_mut_ptr();
                    result.set_repr(self.array.repr());
                    result.initialize(
                        self.array
                            .iter()
                            .skip(self.start)
                            .take(self.end - self.start),
                    );
                    result
                }
            }
        }

        let mut context = array.vm().context();
        let result = context.alloc(Slice {
            start,
            end,
            array: &array.get_array(),
        });

        let value = match result {
            Ok(value) => value,
            Err(err) => return RuntimeResult::Panic(err),
        };

        RuntimeResult::Return(Getable::from_value(array.vm_(), Variants::from(value)))
    }

    pub(crate) fn append<'vm>(
        lhs: Array<'vm, generic::A>,
        rhs: Array<'vm, generic::A>,
    ) -> RuntimeResult<Array<'vm, generic::A>, Error> {
        #[derive(Trace)]
        #[gluon(gluon_vm)]
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
        let mut context = vm.context();
        let value = {
            let result = context.alloc(Append {
                lhs: &lhs.get_array(),
                rhs: &rhs.get_array(),
            });
            match result {
                Ok(x) => x,
                Err(err) => return RuntimeResult::Panic(err),
            }
        };
        RuntimeResult::Return(Getable::from_value(lhs.vm_(), Variants::from(value)))
    }
}

mod int {
    use super::*;
    use crate::types::VmInt;

    pub(crate) fn rem(dividend: VmInt, divisor: VmInt) -> RuntimeResult<VmInt, String> {
        if divisor != 0 {
            RuntimeResult::Return(dividend % divisor)
        } else {
            RuntimeResult::Panic(format!(
                "attempted to calculate remainder of {} divided by 0",
                dividend
            ))
        }
    }

    pub(crate) fn rem_euclid(dividend: VmInt, divisor: VmInt) -> RuntimeResult<VmInt, String> {
        if divisor != 0 {
            RuntimeResult::Return(dividend.rem_euclid(divisor))
        } else {
            RuntimeResult::Panic(format!(
                "attempted to calculate euclidean remainder of {} divided by 0",
                dividend
            ))
        }
    }

    pub(crate) fn wrapping_rem(dividend: VmInt, divisor: VmInt) -> RuntimeResult<VmInt, String> {
        if divisor != 0 {
            RuntimeResult::Return(dividend.wrapping_rem(divisor))
        } else {
            RuntimeResult::Panic(format!(
                "attempted to calculate wrapping remainder of {} divided by 0",
                dividend
            ))
        }
    }

    pub(crate) fn wrapping_rem_euclid(
        dividend: VmInt,
        divisor: VmInt,
    ) -> RuntimeResult<VmInt, String> {
        if divisor != 0 {
            RuntimeResult::Return(dividend.wrapping_rem_euclid(divisor))
        } else {
            RuntimeResult::Panic(format!(
                "attempted to calculate wrapping euclidean remainder of {} divided by 0",
                dividend
            ))
        }
    }

    pub(crate) fn overflowing_rem(
        dividend: VmInt,
        divisor: VmInt,
    ) -> RuntimeResult<(VmInt, bool), String> {
        if divisor != 0 {
            RuntimeResult::Return(dividend.overflowing_rem(divisor))
        } else {
            RuntimeResult::Panic(format!(
                "attempted to calculate overflowing remainder of {} divided by 0",
                dividend
            ))
        }
    }

    pub(crate) fn overflowing_rem_euclid(
        dividend: VmInt,
        divisor: VmInt,
    ) -> RuntimeResult<(VmInt, bool), String> {
        if divisor != 0 {
            RuntimeResult::Return(dividend.overflowing_rem_euclid(divisor))
        } else {
            RuntimeResult::Panic(format!(
                "attempted to calculate overflowing euclidean remainder of {} divided by 0",
                dividend
            ))
        }
    }
}

mod string {
    use super::*;
    use crate::value::ValueStr;

    pub(crate) fn append(lhs: WithVM<&str>, rhs: &str) -> RuntimeResult<Pushed<String>, Error> {
        #[derive(Trace)]
        #[gluon(gluon_vm)]
        struct StrAppend<'b> {
            lhs: &'b str,
            rhs: &'b str,
        }

        unsafe impl<'b> DataDef for StrAppend<'b> {
            type Value = ValueStr;
            fn size(&self) -> usize {
                use crate::real_std::mem::size_of;
                size_of::<ValueStr>() + (self.lhs.len() + self.rhs.len()) * size_of::<u8>()
            }
            fn initialize<'w>(self, mut result: WriteOnly<'w, ValueStr>) -> &'w mut ValueStr {
                unsafe {
                    let result = &mut *result.as_mut_ptr();
                    result.as_mut_array().set_repr(Repr::Byte);
                    result.as_mut_array().unsafe_array_mut::<u8>().initialize(
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

        let mut context = vm.current_context();
        let mut context = context.context();
        let value = match alloc!(context, StrAppend { lhs: lhs, rhs: rhs }) {
            Ok(x) => x,
            Err(err) => return RuntimeResult::Panic(err),
        };
        context.stack.push(Variants::from(value));
        RuntimeResult::Return(Pushed::default())
    }

    pub(crate) fn append_char(
        lhs: WithVM<&str>,
        rhs: char,
    ) -> RuntimeResult<Pushed<String>, Error> {
        append(lhs, rhs.encode_utf8(&mut [0; 4]))
    }

    pub(crate) fn from_char(c: WithVM<char>) -> RuntimeResult<Pushed<String>, Error> {
        append_char(
            WithVM {
                vm: c.vm,
                value: "",
            },
            c.value,
        )
    }

    pub fn split_at(s: &str, index: usize) -> RuntimeResult<(&str, &str), String> {
        if !s.is_char_boundary(index) {
            // Limit the amount of characters to print in the error message
            let mut iter = s.chars();
            for _ in iter.by_ref().take(256) {}
            RuntimeResult::Panic(format!(
                "index {} in `{}` does not lie on a character \
                 boundary",
                index,
                &s[..(s.len() - iter.as_str().len())]
            ))
        } else {
            RuntimeResult::Return(s.split_at(index))
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

    pub fn from_utf8<'a>(array: OpaqueRef<'a, [u8]>) -> StdResult<OpaqueRef<'a, str>, ()> {
        Ok(Opaque::from_value(Variants::from(GcStr::from_utf8(
            array.get_array(),
        )?)))
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
    format!("{:?}", c)
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
    let mut context = thread.current_context();
    let tag = {
        let stack = StackFrame::<ExternState>::current(context.stack());
        let value = stack.get_variant(0).unwrap();
        match value.as_ref() {
            ValueRef::Data(data) => data.tag(),
            _ => 0,
        }
    };
    tag.vm_push(&mut context).unwrap();
    Status::Ok
}

#[allow(non_camel_case_types)]
mod std {

    macro_rules! bit_const_inner {
        ($typ: ty, $($trait_: ident :: $name: ident,)*) => {
            $(
                #[allow(non_upper_case_globals)]
                pub const $name: fn(l: $typ, r: $typ) -> $typ = ::std::ops::$trait_::$name;
            )*
        }
    }

    macro_rules! bit_const {
        ($typ: ty) => {
            bit_const_inner! {
                $typ,
                BitAnd::bitand,
                BitOr::bitor,
                BitXor::bitxor,
                Shl::shl,
                Shr::shr,
            }
        };
    }

    pub use crate::primitives as prim;

    pub mod string {
        pub type prim = str;
    }
    pub mod char {
        pub type prim = char;
    }
    pub mod array {
        pub use crate::primitives::array as prim;
    }

    pub mod byte {
        pub type prim = u8;

        bit_const! { u8 }
    }
    pub mod int {
        use crate::types::VmInt;

        pub type prim = VmInt;

        bit_const! { VmInt }

        #[allow(non_upper_case_globals)]
        pub const arithmetic_shr: fn(l: VmInt, r: VmInt) -> VmInt = shr;
        #[allow(non_upper_case_globals)]
        pub const logical_shr: fn(l: u64, r: u64) -> u64 = ::std::ops::Shr::shr;
    }
    pub mod float {
        pub type prim = f64;
    }
    pub mod path {
        pub type prim = ::std::path::Path;
    }
    pub mod effect {
        pub mod st {
            pub mod string {
                pub use crate::primitives::st_string as prim;
            }
        }
    }
}

#[allow(non_camel_case_types)]
pub fn load_float(thread: &Thread) -> Result<ExternModule> {
    use crate::real_std::f64;

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
            is_nan => primitive!(1, std::float::prim::is_nan),
            is_infinite => primitive!(1, std::float::prim::is_infinite),
            is_finite => primitive!(1, std::float::prim::is_finite),
            is_normal => primitive!(1, std::float::prim::is_normal),
            floor => primitive!(1, std::float::prim::floor),
            ceil => primitive!(1, std::float::prim::ceil),
            round => primitive!(1, std::float::prim::round),
            trunc => primitive!(1, std::float::prim::trunc),
            fract => primitive!(1, std::float::prim::fract),
            abs => primitive!(1, std::float::prim::abs),
            signum => primitive!(1, std::float::prim::signum),
            is_sign_positive => primitive!(1, std::float::prim::is_sign_positive),
            is_sign_negative => primitive!(1, std::float::prim::is_sign_negative),
            mul_add => primitive!(3, std::float::prim::mul_add),
            recip => primitive!(1, std::float::prim::recip),
            rem => primitive!(2, "std::float::prim::rem", |a: f64, b: f64| a % b),
            rem_euclid => primitive!(2, std::float::prim::rem_euclid),
            powi => primitive!(2, std::float::prim::powi),
            powf => primitive!(2, std::float::prim::powf),
            sqrt => primitive!(1, std::float::prim::sqrt),
            exp => primitive!(1, std::float::prim::exp),
            exp2 => primitive!(1, std::float::prim::exp2),
            ln => primitive!(1, std::float::prim::ln),
            log2 => primitive!(1, std::float::prim::log2),
            log10 => primitive!(1, std::float::prim::log10),
            to_degrees => primitive!(1, std::float::prim::to_degrees),
            to_radians => primitive!(1, std::float::prim::to_radians),
            max => primitive!(2, std::float::prim::max),
            min => primitive!(2, std::float::prim::min),
            cbrt => primitive!(1, std::float::prim::cbrt),
            hypot => primitive!(2, std::float::prim::hypot),
            sin => primitive!(1, std::float::prim::sin),
            cos => primitive!(1, std::float::prim::cos),
            tan => primitive!(1, std::float::prim::tan),
            acos => primitive!(1, std::float::prim::acos),
            atan => primitive!(1, std::float::prim::atan),
            atan2 => primitive!(2, std::float::prim::atan2),
            sin_cos => primitive!(1, std::float::prim::sin_cos),
            exp_m1 => primitive!(1, std::float::prim::exp_m1),
            ln_1p => primitive!(1, std::float::prim::ln_1p),
            sinh => primitive!(1, std::float::prim::sinh),
            cosh => primitive!(1, std::float::prim::cosh),
            tanh => primitive!(1, std::float::prim::tanh),
            acosh => primitive!(1, std::float::prim::acosh),
            atanh => primitive!(1, std::float::prim::atanh),
            from_int => primitive!(1, "std.float.prim.from_int", |i: VmInt| i as f64),
            parse => primitive!(1, "std.float.prim.parse", parse::<f64>),
        },
    )
}

#[allow(non_camel_case_types)]
pub fn load_byte(vm: &Thread) -> Result<ExternModule> {
    ExternModule::new(
        vm,
        record! {
            min_value => std::byte::prim::min_value(),
            max_value => std::byte::prim::max_value(),
            shl => primitive!(2, std::byte::shl),
            shr => primitive!(2, std::byte::shr),
            bitxor => primitive!(2, std::byte::bitxor),
            bitand => primitive!(2, std::byte::bitand),
            bitor => primitive!(2, std::byte::bitor),
            count_ones => primitive!(1, std::byte::prim::count_ones),
            count_zeros => primitive!(1, std::byte::prim::count_zeros),
            leading_zeros => primitive!(1, std::byte::prim::leading_zeros),
            trailing_zeros => primitive!(1, std::byte::prim::trailing_zeros),
            rotate_left => primitive!(2, std::byte::prim::rotate_left),
            rotate_right => primitive!(2, std::byte::prim::rotate_right),
            swap_bytes => primitive!(1, std::byte::prim::swap_bytes),
            from_be => primitive!(1, std::byte::prim::from_be),
            from_le => primitive!(1, std::byte::prim::from_le),
            to_be => primitive!(1, std::byte::prim::to_be),
            to_le => primitive!(1, std::byte::prim::to_le),
            pow => primitive!(2, std::byte::prim::pow),
            saturating_add => primitive!(2, std::byte::prim::saturating_add),
            saturating_sub => primitive!(2, std::byte::prim::saturating_sub),
            saturating_mul => primitive!(2, std::byte::prim::saturating_mul),
            wrapping_add => primitive!(2, std::byte::prim::wrapping_add),
            wrapping_sub => primitive!(2, std::byte::prim::wrapping_sub),
            wrapping_mul => primitive!(2, std::byte::prim::wrapping_mul),
            wrapping_div => primitive!(2, std::byte::prim::wrapping_div),
            overflowing_add => primitive!(2, std::byte::prim::overflowing_add),
            overflowing_sub => primitive!(2, std::byte::prim::overflowing_sub),
            overflowing_mul => primitive!(2, std::byte::prim::overflowing_mul),
            overflowing_div => primitive!(2, std::byte::prim::overflowing_div),
            from_int => primitive!(1, "std.byte.prim.from_int", |i: VmInt| i as u8),
            parse => primitive!(1, "std.byte.prim.parse", parse::<u8>),
        },
    )
}

#[allow(non_camel_case_types)]
pub fn load_int(vm: &Thread) -> Result<ExternModule> {
    ExternModule::new(
        vm,
        record! {
            min_value => std::int::prim::min_value(),
            max_value => std::int::prim::max_value(),
            from_str_radix => primitive!(
                2,
                "std.int.prim.from_str_radix",
                |src, radix| std::int::prim::from_str_radix(src, radix).map_err(|_| ())
            ),
            shl => primitive!(2, std::int::shl),
            arithmetic_shr => primitive!(2, std::int::arithmetic_shr),
            logical_shr => primitive!(2, std::int::logical_shr),
            bitxor => primitive!(2, std::int::bitxor),
            bitand => primitive!(2, std::int::bitand),
            bitor => primitive!(2, std::int::bitor),
            count_ones => primitive!(1, std::int::prim::count_ones),
            count_zeros => primitive!(1, std::int::prim::count_zeros),
            leading_zeros => primitive!(1, std::int::prim::leading_zeros),
            trailing_zeros => primitive!(1, std::int::prim::trailing_zeros),
            rotate_left => primitive!(2, std::int::prim::rotate_left),
            rotate_right => primitive!(2, std::int::prim::rotate_right),
            swap_bytes => primitive!(1, std::int::prim::swap_bytes),
            from_be => primitive!(1, std::int::prim::from_be),
            from_le => primitive!(1, std::int::prim::from_le),
            to_be => primitive!(1, std::int::prim::to_be),
            to_le => primitive!(1, std::int::prim::to_le),
            pow => primitive!(2, std::int::prim::pow),
            abs => primitive!(1, std::int::prim::abs),
            rem => primitive!(2, "std::int::prim::rem", int::rem),
            rem_euclid => primitive!(2, "std::int::prim::rem_euclid", int::rem_euclid),
            checked_rem => primitive!(2, std::int::prim::checked_rem),
            checked_rem_euclid => primitive!(2, std::int::prim::checked_rem_euclid),
            saturating_add => primitive!(2, std::int::prim::saturating_add),
            saturating_sub => primitive!(2, std::int::prim::saturating_sub),
            saturating_mul => primitive!(2, std::int::prim::saturating_mul),
            wrapping_add => primitive!(2, std::int::prim::wrapping_add),
            wrapping_sub => primitive!(2, std::int::prim::wrapping_sub),
            wrapping_mul => primitive!(2, std::int::prim::wrapping_mul),
            wrapping_div => primitive!(2, std::int::prim::wrapping_div),
            wrapping_abs => primitive!(1, std::int::prim::wrapping_abs),
            wrapping_rem => primitive!(2, "std::int::prim::wrapping_rem", int::wrapping_rem),
            wrapping_rem_euclid => primitive!(2, "std::int::prim::wrapping_rem", int::wrapping_rem_euclid),
            wrapping_negate => primitive!(1, "std.int.prim.wrapping_negate", std::int::prim::wrapping_neg),
            overflowing_add => primitive!(2, std::int::prim::overflowing_add),
            overflowing_sub => primitive!(2, std::int::prim::overflowing_sub),
            overflowing_mul => primitive!(2, std::int::prim::overflowing_mul),
            overflowing_div => primitive!(2, std::int::prim::overflowing_div),
            overflowing_abs => primitive!(1, std::int::prim::overflowing_abs),
            overflowing_rem => primitive!(2, "std::int::prim::overflowing_rem", int::overflowing_rem),
            overflowing_rem_euclid => primitive!(2, "std::int::prim::overflowing_rem_euclid", int::overflowing_rem_euclid),
            overflowing_negate => primitive!(1, "std.int.prim.overflowing_negate", std::int::prim::overflowing_neg),
            signum => primitive!(1, std::int::prim::signum),
            is_positive => primitive!(1, std::int::prim::is_positive),
            is_negative => primitive!(1, std::int::prim::is_negative),
            from_byte => primitive!(1, "std.int.prim.from_byte", |b: u8| b as VmInt),
            from_float => primitive!(1, "std.int.prim.from_float", |f: f64| f as VmInt),
            parse => primitive!(1, "std.int.prim.parse", parse::<VmInt>)
        },
    )
}

#[allow(non_camel_case_types)]
pub fn load_array(vm: &Thread) -> Result<ExternModule> {
    ExternModule::new(
        vm,
        record! {
            type Array a => Array<A>,
            len => primitive!(1, std::array::prim::len),
            index => primitive!(2, std::array::prim::index),
            append => primitive!(2, std::array::prim::append),
            slice => primitive!(3, std::array::prim::slice)
        },
    )
}

pub fn load_string(vm: &Thread) -> Result<ExternModule> {
    ExternModule::new(
        vm,
        record! {
            len => primitive!(1, std::string::prim::len),
            is_empty => primitive!(1, std::string::prim::is_empty),
            is_char_boundary => primitive!(2, std::string::prim::is_char_boundary),
            as_bytes => primitive!(1, std::string::prim::as_bytes),
            split_at => primitive!(2, "std.string.prim.split_at", string::split_at),
            contains => primitive!(2, std::string::prim::contains::<&str>),
            starts_with => primitive!(2, std::string::prim::starts_with::<&str>),
            ends_with => primitive!(2, std::string::prim::ends_with::<&str>),
            find => primitive!(2, std::string::prim::find::<&str>),
            rfind => primitive!(2, std::string::prim::rfind::<&str>),
            trim => primitive!(1, std::string::prim::trim),
            trim_start => primitive!(1, std::string::prim::trim_start),
            trim_start_matches => primitive!(2, std::string::prim::trim_start_matches::<&str>),
            trim_end => primitive!(1, std::string::prim::trim_end),
            trim_end_matches => primitive!(2, std::string::prim::trim_end_matches::<&str>),
            append => primitive!(2, "std.string.prim.append", string::append),
            append_char => primitive!(2, "std.string.prim.append_char", string::append_char),
            from_char => primitive!(1, "std.string.prim.from_char", string::from_char),
            slice => primitive!(3, "std.string.prim.slice", string::slice),
            from_utf8 => primitive!(
                1,
                "std.string.prim.from_utf8",
                string::from_utf8
            ),
            char_at => primitive!(2, "std.string.prim.char_at", string::char_at)
        },
    )
}

impl<'a> VmType for path::Component<'a> {
    type Type = Component<'static>;
    fn make_type(vm: &Thread) -> ArcType {
        Component::make_type(vm)
    }
}

#[derive(Pushable, VmType)]
#[gluon(vm_type = "std.path.types.Component")]
#[gluon(gluon_vm)]
pub enum Component<'a> {
    Prefix,
    RootDir,
    CurDir,
    ParentDir,
    Normal(&'a OsStr),
}

#[derive(Userdata, Debug, VmType)]
#[gluon(vm_type = "std.fs.Metadata")]
#[gluon(gluon_vm)]
pub struct Metadata(fs::Metadata);

unsafe impl Trace for Metadata {
    impl_trace! { self, _gc, { } }
}

#[derive(Userdata, Debug, VmType)]
#[gluon(vm_type = "std.fs.DirEntry")]
#[gluon(gluon_vm)]
pub struct DirEntry(fs::DirEntry);

unsafe impl Trace for DirEntry {
    impl_trace! { self, _gc, { } }
}

pub fn load_fs(vm: &Thread) -> Result<ExternModule> {
    vm.register_type::<Metadata>("std.fs.Metadata", &[])?;
    vm.register_type::<DirEntry>("std.fs.DirEntry", &[])?;

    ExternModule::new(
        vm,
        record! {
            type Metadata => Metadata,
            type DirEntry => DirEntry,

            read_dir => primitive!(1, "std.fs.prim.read_dir", |p: &Path| {
                IO::from(fs::read_dir(p).and_then(|iter| iter.map(|result| result.map(DirEntry)).collect::<io::Result<Vec<_>>>()))
            }),

            dir_entry => record! {
                path => primitive!(1, "std.fs.prim.dir_entry.path", |m: &DirEntry| m.0.path()),
                metadata => primitive!(1, "std.fs.prim.dir_entry.metadata", |m: &DirEntry| IO::from(m.0.metadata().map(Metadata))),
                file_name => primitive!(1, "std.fs.prim.dir_entry.file_name", |m: &DirEntry| m.0.file_name()),
            },

            metadata => record! {
                is_dir => primitive!(1, "std.fs.prim.metadata.is_dir", |m: &Metadata| m.0.is_dir()),
                is_file => primitive!(1, "std.fs.prim.metadata.is_file", |m: &Metadata| m.0.is_file()),
                len => primitive!(1, "std.fs.prim.metadata.len", |m: &Metadata| m.0.len()),
            },
        },
    )
}

pub fn load_path(vm: &Thread) -> Result<ExternModule> {
    ExternModule::new(
        vm,
        record! {
            is_absolute => primitive!(1, std::path::prim::is_absolute),
            is_relative => primitive!(1, std::path::prim::is_relative),
            has_root => primitive!(1, std::path::prim::has_root),
            parent => primitive!(1, std::path::prim::parent),
            ancestors => primitive!(1, "std.path.prim.ancestors", |p: &Path| p.ancestors().collect::<Vec<_>>()),
            file_name => primitive!(1, std::path::prim::file_name),
            strip_prefix => primitive!(2, "std.path.prim.strip_prefix", |p: &Path, b: &Path| p.strip_prefix(b).ok()),
            starts_with => primitive!(2, "std.path.prim.starts_with", |p: &Path, b: &Path| p.starts_with(b)),
            ends_with => primitive!(2, "std.path.prim.ends_with", |p: &Path, b: &Path| p.ends_with(b)),
            file_stem => primitive!(1, std::path::prim::file_stem),
            extension => primitive!(1, std::path::prim::extension),
            join => primitive!(2, "std.path.prim.join", std::path::prim::join::<&Path>),
            with_file_name => primitive!(2, std::path::prim::with_file_name::<&Path>),
            with_extension => primitive!(2, std::path::prim::with_extension::<&Path>),
            components => primitive!(1, "std.path.prim.components", |p: &Path| {
                p.components()
                    .map(|c| match c {
                        path::Component::Prefix(..) => Component::Prefix,
                        path::Component::RootDir => Component::RootDir,
                        path::Component::CurDir => Component::CurDir,
                        path::Component::ParentDir => Component::ParentDir,
                        path::Component::Normal(p) => Component::Normal(p),
                    })
                    .collect::<Vec<_>>()
            }),
            metadata => primitive!(1, "std.path.prim.metadata", |p: &Path| IO::from(p.metadata().map(Metadata))),
            symlink_metadata => primitive!(1, "std.path.prim.symlink_metadata", |p: &Path| IO::from(p.symlink_metadata().map(Metadata))),
            canonicalize => primitive!(1, "std.path.prim.canonicalize", |p: &Path| IO::from(p.canonicalize())),
            read_link => primitive!(1, "std.path.prim.read_link", |p: &Path| IO::from(p.read_link())),
            read_dir => primitive!(
                1,
                "std.path.prim.read_dir",
                |p: &Path| IO::from(
                        p.read_dir()
                            .and_then(|iter| iter.map(|result| Ok(result?.path())).collect::<StdResult<Vec<_>, _>>())
                            .map_err(|err| Error::Message(err.to_string()))
                    )
            ),
            exists => primitive!(1, "std.path.prim.exists", |p: &Path| IO::Value(p.exists())),
            is_file => primitive!(1, "std.path.prim.is_file", |p: &Path| IO::Value(p.is_file())),
            is_dir => primitive!(1, "std.path.prim.is_file", |p: &Path| IO::Value(p.is_dir())),
        },
    )
}

#[allow(non_camel_case_types)]
pub fn load_char(vm: &Thread) -> Result<ExternModule> {
    ExternModule::new(
        vm,
        record! {
            from_int => primitive!(1, "std.char.prim.from_int", ::std::char::from_u32),
            to_int => primitive!(1, "std.char.prim.to_int", |c: char| c as u32),
            is_digit => primitive!(2, std::char::prim::is_digit),
            to_digit => primitive!(2, std::char::prim::to_digit),
            len_utf8 => primitive!(1, std::char::prim::len_utf8),
            len_utf16 => primitive!(1, std::char::prim::len_utf16),
            is_alphabetic => primitive!(1, std::char::prim::is_alphabetic),
            is_lowercase => primitive!(1, std::char::prim::is_lowercase),
            is_uppercase => primitive!(1, std::char::prim::is_uppercase),
            is_whitespace => primitive!(1, std::char::prim::is_whitespace),
            is_alphanumeric => primitive!(1, std::char::prim::is_alphanumeric),
            is_control => primitive!(1, std::char::prim::is_control),
            is_numeric => primitive!(1, std::char::prim::is_numeric),
        },
    )
}

pub mod st_string {
    use super::*;

    pub(crate) fn len(buf: &StringBuf<S>) -> usize {
        buf.0.lock().unwrap().len()
    }

    pub(crate) fn slice(
        buf: &StringBuf<S>,
        start: usize,
        end: usize,
    ) -> RuntimeResult<String, String> {
        string::slice(&buf.0.lock().unwrap(), start, end).map(|s| s.to_string())
    }

    pub(crate) fn pop(buf: &StringBuf<S>) -> Option<char> {
        buf.0.lock().unwrap().pop()
    }

    pub(crate) fn push_str(buf: &StringBuf<S>, s: &str) {
        buf.0.lock().unwrap().push_str(s)
    }
}

#[derive(Debug, Default, VmType, Userdata, Trace)]
#[gluon(vm_type = "std.effect.st.string.StringBuf")]
#[gluon(gluon_vm)]
pub(crate) struct StringBuf<S>(Mutex<String>, PhantomData<S>);

pub fn load_string_buf(vm: &Thread) -> Result<ExternModule> {
    vm.register_type::<StringBuf<S>>("std.effect.st.string.StringBuf", &["s"])?;

    ExternModule::new(
        vm,
        record! {
            type StringBuf s => StringBuf<S>,
            len => primitive!(1, std::effect::st::string::prim::len),
            new => primitive!(1, "std.effect.st.string.new", |()| StringBuf(Default::default(), PhantomData::<S>)),
            slice => primitive!(3, std::effect::st::string::prim::slice),
            pop => primitive!(1, std::effect::st::string::prim::pop),
            push_str => primitive!(2, std::effect::st::string::prim::push_str)
        },
    )
}

#[allow(non_camel_case_types, deprecated)]
pub fn load<'vm>(vm: &'vm Thread) -> Result<ExternModule> {
    ExternModule::new(
        vm,
        record! {
            show_int => primitive!(1, std::prim::show_int),
            show_float => primitive!(1, std::prim::show_float),
            show_byte => primitive!(1, std::prim::show_byte),
            show_char => primitive!(1, std::prim::show_char),
            string_compare => primitive!(2, "std.prim.string_compare", str::cmp),
            string_eq => primitive!(2, "std.prim.string_eq", <str as PartialEq>::eq),
            error => primitive::<fn(StdString) -> Pushed<A>>("std.prim.error", std::prim::error),
            discriminant_value => primitive::<fn(OpaqueRef<'vm, A>) -> VmInt>(
                "std.prim.discriminant_value",
                std::prim::discriminant_value
            ),
        },
    )
}
