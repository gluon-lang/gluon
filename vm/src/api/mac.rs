#[doc(hidden)]
#[macro_export]
macro_rules! primitive_cast {
    (0, $name: expr) => { $name as fn () -> _ };
    (1, $name: expr) => { $name as fn (_) -> _ };
    (2, $name: expr) => { $name as fn (_, _) -> _ };
    (3, $name: expr) => { $name as fn (_, _, _) -> _ };
    (4, $name: expr) => { $name as fn (_, _, _, _) -> _ };
    (5, $name: expr) => { $name as fn (_, _, _, _, _) -> _ };
    (6, $name: expr) => { $name as fn (_, _, _, _, _, _) -> _ };
    (7, $name: expr) => { $name as fn (_, _, _, _, _, _, _) -> _ };
}

/// Creates a `GluonFunction` from a function implementing `VMFunction`
///
/// ```rust
/// #[macro_use]
/// extern crate gluon_vm;
/// fn test(_x: i32, _y: String) -> f64 {
///     panic!()
/// }
///
/// fn main() {
///     primitive!(2 test);
/// }
/// ```
#[macro_export]
macro_rules! primitive {
    (0 $name: expr) => { named_primitive!(0, stringify!($name), $name) };
    (1 $name: expr) => { named_primitive!(1, stringify!($name), $name) };
    (2 $name: expr) => { named_primitive!(2, stringify!($name), $name) };
    (3 $name: expr) => { named_primitive!(3, stringify!($name), $name) };
    (4 $name: expr) => { named_primitive!(4, stringify!($name), $name) };
    (5 $name: expr) => { named_primitive!(5, stringify!($name), $name) };
    (6 $name: expr) => { named_primitive!(6, stringify!($name), $name) };
    (7 $name: expr) => { named_primitive!(7, stringify!($name), $name) };
}

#[macro_export]
macro_rules! named_primitive {
    ($count: tt, $name: expr, $func: expr) => {
        unsafe {
            extern "C" fn wrapper(thread: &$crate::thread::Thread) -> $crate::thread::Status {
                 $crate::api::VmFunction::unpack_and_call(
                     &primitive_cast!($count, $func), thread)
            }
            $crate::api::primitive_f($name, wrapper, primitive_cast!($count, $func))
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! field_decl_inner {
    () => {
    };

    ($field: ident) => {
        field_decl_inner!{
            ($field stringify!($field))
        }
    };
    (($alias: ident $field: expr)) => {
        #[allow(non_camel_case_types)]
        #[derive(Default)]
        pub struct $alias;
        impl $crate::api::record::Field for $alias {
            fn name() -> &'static str {
                $field
            }
        }
    };

    ($field: ident, $($rest: tt)*) => {
        field_decl_inner!{
            ($field stringify!($field)),
            $($rest)*
        }
    };
    (($alias: ident $field: expr), $($rest: tt)*) => {
        field_decl_inner!{ ($alias $field) }
        field_decl_inner!{$($rest)*}
    }
}

/// Declares fields useable by the record macros
///
/// ```rust
/// #[macro_use]
/// extern crate gluon_vm;
/// # fn main() { }
///
/// field_decl! {x, y}
/// ```
#[macro_export]
macro_rules! field_decl {
    ($($tt: tt)*) => {
        mod _field { field_decl_inner!($($tt)*); }
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! field_decl_record {
    ([$($acc: tt)*]) => {
        field_decl!($($acc)*);
    };

    ([ $($acc: tt)* ] $field: ident => $ignore: expr) => {
        field_decl_record!{
            [$($acc)* ($field stringify!($field)),]
        }
    };
    ([ $($acc: tt)* ] ($alias: ident $field: expr) => $ignore: expr) => {
        field_decl_record!{
            [$($acc)* ($alias $field),]
        }
    };

    ([ $($acc: tt)* ] $field: ident => $ignore: expr, $($rest: tt)*) => {
        field_decl_record!{
            [$($acc)* ($field stringify!($field)),]
            $($rest)*
        }
    };
    ([ $($acc: tt)* ] ($alias: ident $field: expr) => $ignore: expr, $($rest: tt)*) => {
        field_decl_record!{
            [$($acc)* ($alias $field),]
            $($rest)*
        }
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! record_no_decl_inner {
    () => { $crate::frunk_core::hlist::HNil };
    ($field: ident => $value: expr) => {
        $crate::frunk_core::hlist::h_cons((_field::$field, $value), record_no_decl_inner!())
    };
    ( ($field: ident $ignore: expr) => $value: expr) => {
        record_no_decl_inner!($field => $value)
    };
    ($field: ident => $value: expr, $($rest: tt)*) => {
        $crate::frunk_core::hlist::h_cons(
            (_field::$field, $value),
            record_no_decl_inner!($($rest)*)
        )
    };
    ( ($field: ident $ignore: expr) => $value: expr, $($rest: tt)*) => {
        record_no_decl_inner!($field => $value, $($rest)*)
    };
}

/// Macro that creates a record that can be passed to gluon. Reuses already declared fields
/// instead of generating unique ones.
///
/// ```rust
/// #[macro_use]
/// extern crate gluon_vm;
///
/// field_decl! {x, y, name}
///
/// fn main() {
///     record_no_decl!(x => 1, y => 2, name => "Gluon");
/// }
/// ```
#[macro_export]
macro_rules! record_no_decl {
    ($($tt: tt)*) => {
        {
            $crate::api::Record {
                fields: record_no_decl_inner!($($tt)*)
            }
        }
    }
}

/// Macro that creates a record that can be passed to gluon
///
/// ```rust
/// #[macro_use]
/// extern crate gluon_vm;
/// fn main() {
///     record!(x => 1, y => 2, name => "Gluon");
/// }
/// ```
#[macro_export]
macro_rules! record {
    ($($tt: tt)*) => {{
        field_decl_record!([] $($tt)*);
        record_no_decl!($($tt)*)
    }}
}

#[doc(hidden)]
#[macro_export]
macro_rules! record_type_inner {
    () => { $crate::frunk_core::hlist::HNil };
    ($field: ident => $value: ty) => {
        $crate::frunk_core::hlist::HCons<(_field::$field, $value), record_type_inner!()>
    };
    ($field: ident => $value: ty, $($field_tail: ident => $value_tail: ty),*) => {
        $crate::frunk_core::hlist::HCons<(_field::$field, $value),
                                record_type_inner!( $($field_tail => $value_tail),*)>
    }
}

/// Creates a Rust type compatible with the type of `record_no_decl!`
///
/// ```rust
/// #[macro_use]
/// extern crate gluon_vm;
/// # fn main() { }
/// // Fields used in `record_type!` needs to be forward declared
/// field_decl! {x, y}
/// fn new_vec(x: f64, y: f64) -> record_type!(x => f64, y => f64) {
///     record_no_decl!(x => y, y => y)
/// }
/// ```
#[macro_export]
macro_rules! record_type {
    ($($field: ident => $value: ty),*) => {
        $crate::api::Record<
            record_type_inner!($($field => $value),*)
            >
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! record_p_impl {
    () => { $crate::frunk_core::hlist::HNil };
    ($field: pat) => {
        $crate::frunk_core::hlist::HCons { head: (_, $field), tail: record_p_impl!() }
    };
    ($field: pat, $($field_tail: pat),*) => {
        $crate::frunk_core::hlist::HCons { head: (_, $field),
                                           tail: record_p_impl!($($field_tail),*) }
    }
}

/// Creates a pattern which matches on marshalled gluon records
///
/// ```rust
/// #[macro_use]
/// extern crate gluon_vm;
/// fn main() {
///     match record!(x => 1, y => "y") {
///         record_p!(a, "y") => assert_eq!(a, 1),
///         _ => assert!(false),
///     }
/// }
/// ```
#[macro_export]
macro_rules! record_p {
    ($($field: pat),*) => {
        $crate::api::Record {
            fields: record_p_impl!($($field),*)
        }
    }
}
