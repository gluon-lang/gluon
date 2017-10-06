//! Module containing functions for interacting with gluon's primitive types.
use std::result::Result as StdResult;
use std::string::String as StdString;
use std::str::FromStr;

use {Error, ExternModule, Variants};
use primitives as prim;
use api::{generic, primitive, Array, Generic, Getable, RuntimeResult, WithVM};
use api::generic::A;
use gc::{DataDef, Gc, Traverseable, WriteOnly};
use Result;
use vm::{Status, Thread};
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
        unsafe {
            RuntimeResult::Return(
                Getable::from_value(vm, Variants::new(&Value::String(value))).expect("Array"),
            )
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
        let value = StackFrame::current(&mut context.stack)[0];
        match value {
            Value::Array(array) => match GcStr::from_utf8(array) {
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

extern "C" fn error(_: &Thread) -> Status {
    // We expect a string as an argument to this function but we only return Status::Error
    // and let the caller take care of printing the message
    Status::Error
}

#[allow(non_camel_case_types)]
pub fn load_float(thread: &Thread) -> Result<ExternModule> {
    use std::f64;
    type float_prim = f64;

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
            is_nan => primitive!(1 float_prim::is_nan),
            is_infinite => primitive!(1 float_prim::is_infinite),
            is_finite => primitive!(1 float_prim::is_finite),
            is_normal => primitive!(1 float_prim::is_normal),
            floor => primitive!(1 float_prim::floor),
            ceil => primitive!(1 float_prim::ceil),
            round => primitive!(1 float_prim::round),
            trunc => primitive!(1 float_prim::trunc),
            fract => primitive!(1 float_prim::fract),
            abs => primitive!(1 float_prim::abs),
            signum => primitive!(1 float_prim::signum),
            is_sign_positive => primitive!(1 float_prim::is_sign_positive),
            is_sign_negative => primitive!(1 float_prim::is_sign_negative),
            mul_add => primitive!(3 float_prim::mul_add),
            recip => primitive!(1 float_prim::recip),
            powi => primitive!(2 float_prim::powi),
            powf => primitive!(2 float_prim::powf),
            sqrt => primitive!(1 float_prim::sqrt),
            exp => primitive!(1 float_prim::exp),
            exp2 => primitive!(1 float_prim::exp2),
            ln => primitive!(1 float_prim::ln),
            log2 => primitive!(1 float_prim::log2),
            log10 => primitive!(1 float_prim::log10),
            to_degrees => primitive!(1 float_prim::to_degrees),
            to_radians => primitive!(1 float_prim::to_radians),
            max => primitive!(2 float_prim::max),
            min => primitive!(2 float_prim::min),
            cbrt => primitive!(1 float_prim::cbrt),
            hypot => primitive!(2 float_prim::hypot),
            sin => primitive!(1 float_prim::sin),
            cos => primitive!(1 float_prim::cos),
            tan => primitive!(1 float_prim::tan),
            acos => primitive!(1 float_prim::acos),
            atan => primitive!(1 float_prim::atan),
            atan2 => primitive!(2 float_prim::atan2),
            sin_cos => primitive!(1 float_prim::sin_cos),
            exp_m1 => primitive!(1 float_prim::exp_m1),
            ln_1p => primitive!(1 float_prim::ln_1p),
            sinh => primitive!(1 float_prim::sinh),
            cosh => primitive!(1 float_prim::cosh),
            tanh => primitive!(1 float_prim::tanh),
            acosh => primitive!(1 float_prim::acosh),
            atanh => primitive!(1 float_prim::atanh),
            parse => named_primitive!(1, "float_prim.parse", parse::<f64>)
        },
    )
}

#[allow(non_camel_case_types)]
pub fn load_int(vm: &Thread) -> Result<ExternModule> {
    use types::VmInt as int_prim;
    ExternModule::new(
        vm,
        record! {
            min_value => int_prim::min_value(),
            max_value => int_prim::max_value(),
            count_ones => primitive!(1 int_prim::count_ones),
            rotate_left => primitive!(2 int_prim::rotate_left),
            rotate_right => primitive!(2 int_prim::rotate_right),
            swap_bytes => primitive!(1 int_prim::swap_bytes),
            from_be => primitive!(1 int_prim::from_be),
            from_le => primitive!(1 int_prim::from_le),
            to_be => primitive!(1 int_prim::to_be),
            to_le => primitive!(1 int_prim::to_le),
            pow => primitive!(2 int_prim::pow),
            abs => primitive!(1 int_prim::abs),
            signum => primitive!(1 int_prim::signum),
            is_positive => primitive!(1 int_prim::is_positive),
            is_negative => primitive!(1 int_prim::is_negative),
            parse => named_primitive!(1, "int_prim.parse", parse::<VmInt>)
        },
    )
}

#[allow(non_camel_case_types)]
pub fn load_array(vm: &Thread) -> Result<ExternModule> {
    use self::array;
    ExternModule::new(
        vm,
        record! {
            len => primitive!(1 array::len),
            index => primitive!(2 array::index),
            append => primitive!(2 array::append)
        },
    )
}

#[allow(non_camel_case_types)]
pub fn load_string(vm: &Thread) -> Result<ExternModule> {
    use self::string;
    type string_prim = str;
    vm.define_global(
        "string_compare",
        named_primitive!(2, "string_compare", string_prim::cmp),
    )?;
    vm.define_global(
        "string_eq",
        named_primitive!(2, "string_eq", <str as PartialEq>::eq),
    )?;
    ExternModule::new(
        vm,
        record! {
            len => primitive!(1 string_prim::len),
            is_empty => primitive!(1 string_prim::is_empty),
            split_at => primitive!(2 string_prim::split_at),
            find => named_primitive!(2, "string_prim.find", string_prim::find::<&str>),
            rfind => named_primitive!(2, "string_prim.rfind", string_prim::rfind::<&str>),
            starts_with => named_primitive!(
                2,
                "string_prim.starts_with",
                string_prim::starts_with::<&str>
            ),
            ends_with => named_primitive!(
                2,
                "string_prim.ends_with",
                string_prim::ends_with::<&str>
            ),
            trim => primitive!(1 string_prim::trim),
            trim_left => primitive!(1 string_prim::trim_left),
            trim_right => primitive!(1 string_prim::trim_right),
            append => named_primitive!(2, "string_prim.append", string::append),
            slice => named_primitive!(3, "string_prim.slice", string::slice),
            from_utf8 => primitive::<fn(Vec<u8>) -> StdResult<String, ()>>(
                "string_prim.from_utf8",
                string::from_utf8
            ),
            char_at => named_primitive!(2, "string_prim.char_at", string::char_at),
            as_bytes => primitive!(1 string_prim::as_bytes)
        },
    )
}

#[allow(non_camel_case_types)]
pub fn load_char(vm: &Thread) -> Result<ExternModule> {
    use std::char;
    type char_prim = char;
    ExternModule::new(
        vm,
        record! {
            is_digit => primitive!(2 char_prim::is_digit),
            to_digit => primitive!(2 char_prim::to_digit),
            len_utf8 => primitive!(1 char_prim::len_utf8),
            len_utf16 => primitive!(1 char_prim::len_utf16),
            is_alphabetic => primitive!(1 char_prim::is_alphabetic),
            is_lowercase => primitive!(1 char_prim::is_lowercase),
            is_uppercase => primitive!(1 char_prim::is_uppercase),
            is_whitespace => primitive!(1 char_prim::is_whitespace),
            is_alphanumeric => primitive!(1 char_prim::is_alphanumeric),
            is_control => primitive!(1 char_prim::is_control),
            is_numeric => primitive!(1 char_prim::is_numeric)
        },
    )
}

#[allow(non_camel_case_types)]
pub fn load(vm: &Thread) -> Result<()> {
    vm.define_global(
        "prim",
        record! {
            show_int => primitive!(1 prim::show_int),
            show_float => primitive!(1 prim::show_float),
            show_char => primitive!(1 prim::show_char)
        },
    )?;

    vm.define_global(
        "#error",
        primitive::<fn(StdString) -> Generic<A>>("#error", prim::error),
    )?;

    vm.define_global(
        "error",
        primitive::<fn(StdString) -> Generic<A>>("error", prim::error),
    )?;

    Ok(())
}
