//! Module containing functions for interacting with gluon's primitive types.
use crate::real_std::{
    ffi::OsStr,
    fs, io,
    path::{self, Path},
    result::Result as StdResult,
    str::FromStr,
    string::String as StdString,
};

use crate::base::types::ArcType;

use crate::api::{
    generic::{self, A},
    primitive, Array, Getable, OpaqueRef, Pushable, Pushed, RuntimeResult, ValueRef, VmType,
    WithVM, IO,
};
use crate::gc::{DataDef, Gc, Traverseable, WriteOnly};
use crate::stack::{ExternState, StackFrame};
use crate::types::VmInt;
use crate::value::{Def, GcStr, Repr, ValueArray, ValueRepr};
use crate::vm::{Status, Thread};
use crate::{Error, ExternModule, Result, Variants};

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

        struct Slice<'a> {
            start: usize,
            end: usize,
            array: &'a ValueArray,
        }

        impl<'a> Traverseable for Slice<'a> {
            fn traverse(&self, gc: &mut Gc) {
                self.array.traverse(gc);
            }
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
            array: array.get_value_array(),
        });

        let value = match result {
            Ok(value) => value,
            Err(err) => return RuntimeResult::Panic(err),
        };

        unsafe {
            RuntimeResult::Return(Getable::from_value(
                array.vm_(),
                Variants::new(&ValueRepr::Array(value).into()),
            ))
        }
    }

    pub(crate) fn append<'vm>(
        lhs: Array<'vm, generic::A>,
        rhs: Array<'vm, generic::A>,
    ) -> RuntimeResult<Array<'vm, generic::A>, Error> {
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
                lhs.vm_(),
                Variants::new(&ValueRepr::Array(value).into()),
            ))
        }
    }
}

mod string {
    use super::*;
    use crate::api::Pushable;
    use crate::thread::ThreadInternal;

    pub fn append(lhs: WithVM<&str>, rhs: &str) -> RuntimeResult<String, Error> {
        struct StrAppend<'b> {
            lhs: &'b str,
            rhs: &'b str,
        }

        impl<'b> Traverseable for StrAppend<'b> {}

        unsafe impl<'b> DataDef for StrAppend<'b> {
            type Value = ValueArray;
            fn size(&self) -> usize {
                use crate::real_std::mem::size_of;
                size_of::<ValueArray>() + (self.lhs.len() + self.rhs.len()) * size_of::<u8>()
            }
            fn initialize<'w>(self, mut result: WriteOnly<'w, ValueArray>) -> &'w mut ValueArray {
                use crate::value::Repr;
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
        let mut context = thread.current_context();
        let value = StackFrame::<ExternState>::current(context.stack())[0].get_repr();
        match value {
            ValueRepr::Array(array) => match GcStr::from_utf8(array) {
                Ok(string) => {
                    let value = ValueRepr::String(string).into();
                    let result = context.context().alloc_with(
                        thread,
                        Def {
                            tag: 1,
                            elems: &[value],
                        },
                    );
                    match result {
                        Ok(data) => {
                            context.stack().push(ValueRepr::Data(data));
                            Status::Ok
                        }
                        Err(err) => {
                            let result: RuntimeResult<(), _> = RuntimeResult::Panic(err);
                            result.status_push(&mut context)
                        }
                    }
                }
                Err(()) => {
                    let err: StdResult<&str, ()> = Err(());
                    err.status_push(&mut context)
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
    let mut context = thread.current_context();
    let tag = {
        let stack = StackFrame::<ExternState>::current(context.stack());
        let value = stack.get_variant(0).unwrap();
        match value.as_ref() {
            ValueRef::Data(data) => data.tag(),
            _ => 0,
        }
    };
    tag.push(&mut context).unwrap();
    Status::Ok
}

#[allow(non_camel_case_types)]
mod std {
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
    }
    pub mod int {
        pub type prim = crate::types::VmInt;
    }
    pub mod float {
        pub type prim = f64;
    }
    pub mod path {
        pub type prim = ::std::path::Path;
    }
}

#[allow(non_camel_case_types)]
pub fn load_float(thread: &Thread) -> Result<ExternModule> {
    use self::std;
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
            parse => primitive!(1, "std.float.prim.parse", parse::<f64>)
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
            parse => primitive!(1, "std.byte.prim.parse", parse::<u8>)
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
            from_str_radix => primitive!(
                2,
                "std.int.prim.from_str_radix",
                |src, radix| std::int::prim::from_str_radix(src, radix).map_err(|_| ())
            ),
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
            saturating_add => primitive!(2, std::int::prim::saturating_add),
            saturating_sub => primitive!(2, std::int::prim::saturating_sub),
            saturating_mul => primitive!(2, std::int::prim::saturating_mul),
            wrapping_add => primitive!(2, std::int::prim::wrapping_add),
            wrapping_sub => primitive!(2, std::int::prim::wrapping_sub),
            wrapping_mul => primitive!(2, std::int::prim::wrapping_mul),
            wrapping_div => primitive!(2, std::int::prim::wrapping_div),
            wrapping_abs => primitive!(1, std::int::prim::wrapping_abs),
            wrapping_negate => primitive!(1, "std.int.prim.wrapping_negate", std::int::prim::wrapping_neg),
            overflowing_add => primitive!(2, std::int::prim::overflowing_add),
            overflowing_sub => primitive!(2, std::int::prim::overflowing_sub),
            overflowing_mul => primitive!(2, std::int::prim::overflowing_mul),
            overflowing_div => primitive!(2, std::int::prim::overflowing_div),
            overflowing_abs => primitive!(1, std::int::prim::overflowing_abs),
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
    use self::std;
    ExternModule::new(
        vm,
        record! {
            len => primitive!(1, std::array::prim::len),
            index => primitive!(2, std::array::prim::index),
            append => primitive!(2, std::array::prim::append),
            slice => primitive!(3, std::array::prim::slice)
        },
    )
}

pub fn load_string(vm: &Thread) -> Result<ExternModule> {
    use self::string;
    ExternModule::new(
        vm,
        record! {
            len => primitive!(1, std::string::prim::len),
            is_empty => primitive!(1, std::string::prim::is_empty),
            is_char_boundary => primitive!(2, std::string::prim::is_char_boundary),
            as_bytes => primitive!(1, std::string::prim::as_bytes),
            split_at => primitive!(2, std::string::prim::split_at),
            contains => primitive!(2, std::string::prim::contains::<&str>),
            starts_with => primitive!(2, std::string::prim::starts_with::<&str>),
            ends_with => primitive!(2, std::string::prim::ends_with::<&str>),
            find => primitive!(2, std::string::prim::find::<&str>),
            rfind => primitive!(2, std::string::prim::rfind::<&str>),
            trim => primitive!(1, std::string::prim::trim),
            trim_left => primitive!(1, std::string::prim::trim_left),
            trim_left_matches => primitive!(2, std::string::prim::trim_left_matches::<&str>),
            trim_right => primitive!(1, std::string::prim::trim_right),
            trim_right_matches => primitive!(2, std::string::prim::trim_right_matches::<&str>),
            append => primitive!(2, "std.string.prim.append", string::append),
            slice => primitive!(3, "std.string.prim.slice", string::slice),
            from_utf8 => primitive::<fn(Vec<u8>) -> StdResult<String, ()>>(
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

#[derive(Userdata, Debug)]
#[gluon(gluon_vm)]
pub struct Metadata(fs::Metadata);

#[derive(Userdata, Debug)]
#[gluon(gluon_vm)]
pub struct DirEntry(fs::DirEntry);

pub fn load_fs(vm: &Thread) -> Result<ExternModule> {
    vm.register_type::<Metadata>("Metadata", &[])?;
    vm.register_type::<DirEntry>("DirEntry", &[])?;

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
                file_name => primitive!(1, "std.fs.prim.dir_entry.file_name", |m: &DirEntry| m.0.file_name())
            },

            metadata => record! {
                is_dir => primitive!(1, "std.fs.prim.metadata.is_dir", |m: &Metadata| m.0.is_dir()),
                is_file => primitive!(1, "std.fs.prim.metadata.is_file", |m: &Metadata| m.0.is_file()),
                len => primitive!(1, "std.fs.prim.metadata.len", |m: &Metadata| m.0.len())
            }
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
            is_dir => primitive!(1, "std.path.prim.is_file", |p: &Path| IO::Value(p.is_dir()))
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

#[allow(non_camel_case_types, deprecated)]
pub fn load<'vm>(vm: &'vm Thread) -> Result<ExternModule> {
    use self::std;

    vm.define_global(
        "@error",
        primitive::<fn(StdString) -> Pushed<A>>("@error", std::prim::error),
    )?;

    vm.define_global(
        "@string_eq",
        primitive!(2, "@string_eq", <str as PartialEq>::eq),
    )?;

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
