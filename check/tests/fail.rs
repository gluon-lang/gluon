#[macro_use]
extern crate collect_mac;
extern crate env_logger;

extern crate gluon_base as base;
extern crate gluon_parser as parser;
extern crate gluon_check as check;

use base::pos::Spanned;
use base::types;

mod support;

macro_rules! assert_err {
    ($e: expr, $($id: pat),+) => {{
        use check::typecheck::TypeError::*;
        #[allow(unused_imports)]
        use check::unify::Error::{TypeMismatch, Occurs, Other};
        #[allow(unused_imports)]
        use check::unify_type::TypeError::FieldMismatch;

        let symbols = support::get_local_interner();
        match $e {
            Ok(x) => assert!(false, "Expected error, got {}",
                             types::display_type(&*symbols.borrow(), &x)),
            Err(err) => {
                let mut iter = err.errors.iter();
                $(
                match iter.next() {
                    Some(&Spanned { value: $id, .. }) => (),
                    _ => assert!(false, "Found errors:\n{}\nbut expected {}",
                                        err, stringify!($id)),
                }
                )+
                assert!(iter.count() == 0, "Found more errors than expected\n{}", err);
            }
        }
    }}
}

macro_rules! assert_unify_err {
    ($e: expr, $($id: pat),+) => {{
        use check::typecheck::TypeError::*;
        #[allow(unused_imports)]
        use check::unify::Error::{TypeMismatch, Occurs, Other};
        #[allow(unused_imports)]
        use check::unify_type::TypeError::{FieldMismatch, SelfRecursive, MissingFields};

        let symbols = support::get_local_interner();

        match $e {
            Ok(x) => assert!(false, "Expected error, got {}",
                             types::display_type(&*symbols.borrow(), &x)),
            Err(err) => {
                for err in err.errors.iter() {
                    match *err {
                        Spanned { value: Unification(_, _, ref errors), .. } => {
                            let mut iter = errors.iter();
                            $(
                            match iter.next() {
                                Some(&$id) => (),
                                Some(err2) => assert!(false, "Found errors:\n{}\nExpected:\n{}\nFound\n:{:?}",
                                                    err, stringify!($id), err2),
                                None => assert!(false, "Found errors:\n{}\nbut expected {}",
                                                    err, stringify!($id))
                            }
                            )+
                            assert!(iter.count() == 0,
                                    "Found more errors than expected\n{}",
                                    err);
                        }
                        _ => assert!(false,
                                     "Found errors:\n{}\nbut expected an unification error",
                                     err)
                    }
                }
            }
        }
    }}
}

#[test]
fn record_missing_field() {
    let _ = env_logger::init();
    let text = r"
match { x = 1 } with
| { x, y } -> 1
";
    let result = support::typecheck(text);

    assert_unify_err!(result, Other(MissingFields(..)));
}

#[test]
fn undefined_type() {
    let _ = env_logger::init();
    let text = r#"
let x =
    type Test = | Test String Int
    in { Test, x = 1 }
in
type Test2 = Test
in x
"#;
    let result = support::typecheck(text);

    assert_err!(result, UndefinedType(..));
}

#[test]
fn undefined_variant() {
    let _ = env_logger::init();
    let text = r#"
let x =
    type Test = | Test String Int
    { Test, x = 1 }
Test "" 2
"#;
    let result = support::typecheck(text);

    assert_err!(result, UndefinedVariable(..));
}

#[test]
fn mutually_recursive_types_error() {
    let _ = env_logger::init();
    let text = r#"
type List a = | Empty | Node (a (Data a))
and Data a = { value: a, list: List a }
in 1
"#;
    let result = support::typecheck(text);

    assert_err!(result, KindError(TypeMismatch(..)));
}

#[test]
fn unpack_field_which_does_not_exist() {
    let _ = env_logger::init();
    let text = r#"
let { y } = { x = 1 }
2
"#;
    let result = support::typecheck(text);

    assert_unify_err!(result, Other(MissingFields(..)));
}

#[test]
fn unpack_type_field_which_does_not_exist() {
    let _ = env_logger::init();
    let text = r#"
type Test = Int
let { Test2 } = { Test }
2
"#;
    let result = support::typecheck(text);

    assert_err!(result, UndefinedField(..));
}

#[test]
fn duplicate_type_definition() {
    let _ = env_logger::init();
    let text = r#"
type Test = Int
in
type Test = Float
in 1
"#;
    let result = support::typecheck(text);

    assert_err!(result, DuplicateTypeDefinition(..));
}

#[test]
fn no_matching_overloaded_binding() {
    let _ = env_logger::init();
    let text = r#"
let f x = x #Int+ 1
in
let f x = x #Float+ 1.0
in f ""
"#;
    let result = support::typecheck(text);

    assert_err!(result, Rename(..));
}

#[test]
fn no_matching_binop_binding() {
    let _ = env_logger::init();
    let text = r#"
let (++) x y = x #Int+ y
let (++) x y = x #Float+ y
"" ++ ""
"#;
    let result = support::typecheck(text);

    assert_err!(result, Rename(..));
}

#[test]
fn not_enough_information_to_decide_overload() {
    let _ = env_logger::init();
    let text = r#"
let f x = x #Int+ 1
let f x = x #Float+ 1.0
\x -> f x
"#;
    let result = support::typecheck(text);

    assert_err!(result, Rename(..));
}

#[test]
fn type_field_mismatch() {
    let _ = env_logger::init();
    let text = r#"
if True then
    type Test = Int
    { Test }
else
    type Test = Float
    { Test }
"#;
    let result = support::typecheck(text);

    assert_unify_err!(result, TypeMismatch(..));
}

#[test]
fn arguments_need_to_be_instantiated_before_any_access() {
    let _ = env_logger::init();
    // test_fn: forall a. (a -> ()) -> ()
    // To allow any type to be passed to `f` it should be
    // test_fn: (forall a. a -> ()) -> ()
    let text = r#"
let test_fn f: (a -> ()) -> () =
    f 2.0
1
"#;
    let result = support::typecheck(text);

    assert_unify_err!(result, TypeMismatch(..));
}

#[test]
fn infer_ord_int() {
    let _ = env_logger::init();
    let text = r#"
type Ordering = | LT | EQ | GT
type Ord a = {
    compare : a -> a -> Ordering
}
let ord_Int = {
    compare = \l r ->
        if l #Int< r
        then LT
        else if l #Int== r
        then EQ
        else GT
}
let make_Ord ord =
    let compare = ord.compare
    in {
        (<=) = \l r ->
            match compare l r with
                | LT -> True
                | EQ -> True
                | GT -> False
    }
let (<=) = (make_Ord ord_Int).(<=)

"" <= ""
"#;
    let result = support::typecheck(text);

    assert_unify_err!(result, TypeMismatch(..), TypeMismatch(..));
}

#[test]
fn recursive_types_with_differing_aliases() {
    let _ = env_logger::init();
    let text = r"
type Option a = | None | Some a
type R1 = Option R1
and R2 = Option R2

let x: R1 = None
let y: R2 = x
y
";
    let result = support::typecheck(text);

    assert_unify_err!(result, Other(SelfRecursive(..)));
}

#[test]
fn detect_self_recursive_aliases() {
    let _ = env_logger::init();
    let text = r"
type A a = A a

let g x: A a -> () = x
1
";
    let result = support::typecheck(text);

    assert_unify_err!(result, Other(SelfRecursive(..)));
}

#[test]
fn declared_generic_variables_may_not_make_outer_bindings_more_general() {
    let _ = ::env_logger::init();
    let text = r#"
let make m =
    let m2: m = m
    m

make
"#;
    let result = support::typecheck(text);
    assert!(result.is_err());
}

#[test]
fn duplicate_fields() {
    let _ = ::env_logger::init();
    let text = r#"
type Test = Int
let x = ""
{ Test, Test, x = 1, x }
"#;
    let result = support::typecheck(text);
    assert_err!(result, DuplicateField(..), DuplicateField(..));
}

#[test]
fn duplicate_fields_pattern() {
    let _ = ::env_logger::init();
    let text = r#"
type Test = Int
let { Test, Test, x = y, x } = { Test, x = 1 }
()
"#;
    let result = support::typecheck(text);
    assert_err!(result, DuplicateField(..), DuplicateField(..));
}
