#[macro_use]
extern crate pretty_assertions;

extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_parser as parser;

use crate::base::{
    ast::KindedIdent,
    symbol::Symbol,
    types::{ArcType, Type},
};

use crate::check::typecheck::TypeError;

#[macro_use]
mod support;

#[test]
fn record_missing_field() {
    let _ = env_logger::try_init();
    let text = r"
match { x = 1 } with
| { x, y } -> 1
";
    let result = support::typecheck(text);

    assert_unify_err!(result, Other(MissingFields(..)));
}

#[test]
fn match_different_alt_types() {
    let _ = env_logger::try_init();
    let text = r#"
match () with
| () -> 1
| () -> ""
"#;
    let result = support::typecheck(text);

    assert_unify_err!(result, TypeMismatch(..));
}

#[test]
fn match_different_alt_types_expected() {
    let _ = env_logger::try_init();
    let text = r#"
let x : _ =
    match () with
    | () -> 1
    | () -> ""
()
"#;
    let result = support::typecheck(text);

    assert_unify_err!(result, TypeMismatch(..));
}

#[test]
fn undefined_type_not_in_scope() {
    let _ = env_logger::try_init();
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
    let _ = env_logger::try_init();
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
fn undefined_type_in_pattern_match_triggers_only_one_error() {
    let _ = env_logger::try_init();
    let text = r#"
let { Test } = {}
type Test2 = Test
()
"#;
    let result = support::typecheck(text);

    assert_err!(result, UndefinedField(..));
}

#[test]
fn undefined_type_still_gets_exported() {
    let _ = env_logger::try_init();
    let text = r#"
let { Test } = { Test }
type Test2 = Test
()
"#;
    let result = support::typecheck(text);

    assert_err!(result, UndefinedType(..));
}

#[test]
fn mutually_recursive_types_error() {
    let _ = env_logger::try_init();
    let text = r#"
rec
type List a = | Empty | Node (a (Data a))
type Data a = { value: a, list: List a }
in 1
"#;
    let result = support::typecheck(text);

    assert_err!(result, KindError(TypeMismatch(..)));
}

#[test]
fn unpack_field_which_does_not_exist() {
    let _ = env_logger::try_init();
    let text = r#"
let { y } = { x = 1 }
2
"#;
    let result = support::typecheck(text);

    assert_unify_err!(result, Other(MissingFields(..)));
}

#[test]
fn unpack_type_field_which_does_not_exist() {
    let _ = env_logger::try_init();
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
    let _ = env_logger::try_init();
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
fn unable_to_resolve_implicit_without_attribute() {
    let _ = env_logger::try_init();
    let text = r#"
let f ?x y : [a] -> a -> a = x
let i = 123
f 1
"#;
    let result = support::typecheck(text);

    assert_err!(result, TypeError::UnableToResolveImplicit(..));
}

#[test]
fn type_field_mismatch() {
    let _ = env_logger::try_init();
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
    let _ = env_logger::try_init();
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
    let _ = env_logger::try_init();
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
let make_Ord ord : forall a . Ord a -> _ =
    let compare = ord.compare
    in {
        (<=) = \l r ->
            match compare l r with
            | LT -> True
            | EQ -> True
            | GT -> False
    }
#[infix(left, 4)]
let (<=) = (make_Ord ord_Int).(<=)

"" <= ""
"#;
    let result = support::typecheck(text);

    assert_multi_unify_err!(result, [TypeMismatch(..)], [TypeMismatch(..)]);
}

#[test]
fn recursive_types_with_differing_aliases() {
    let _ = env_logger::try_init();
    let text = r"
type Option a = | None | Some a
let none = None
type R1 = Option R1
type R2 = Option R2

let x: R1 = none
let y: R2 = x
y
";
    let result = support::typecheck(text);

    assert_multi_unify_err!(result, [Other(SelfRecursiveAlias(..))]);
}

#[test]
fn detect_self_recursive_aliases() {
    let _ = env_logger::try_init();
    let text = r"
type A a = A a

let g x: A a -> () = x
1
";
    let result = support::typecheck(text);

    assert_unify_err!(result, Other(SelfRecursiveAlias(..)));
}

#[test]
fn declared_generic_variables_may_not_make_outer_bindings_more_general() {
    let _ = ::env_logger::try_init();
    let text = r#"
let make m =
    let m2: m = m
    let _ = m2 1
    m

make 2
"#;
    let result = support::typecheck(text);
    assert_err!(result, Message(..), Message(..));
}

#[test]
fn duplicate_fields() {
    let _ = ::env_logger::try_init();
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
    let _ = ::env_logger::try_init();
    let text = r#"
type Test = Int
let { Test, Test, x = y, x } = { Test, x = 1 }
()
"#;
    let result = support::typecheck(text);
    assert_err!(result, DuplicateField(..), DuplicateField(..));
}

#[test]
fn type_alias_with_explicit_type_kind() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Test (a : Type) = a
type Foo a = a
type Bar = Test Foo
()
"#;
    let result = support::typecheck(text);
    assert_err!(result, KindError(TypeMismatch(..)));
}

#[test]
fn type_alias_with_explicit_row_kind() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Test (a : Row) = a
type Bar = Test Int
()
"#;
    let result = support::typecheck(text);
    assert_err!(result, KindError(TypeMismatch(..)));
}

#[test]
fn type_alias_with_explicit_function_kind() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Test (a : Type -> Type) = a Int
type Foo = Test Int
()
"#;
    let result = support::typecheck(text);
    assert_err!(result, KindError(TypeMismatch(..)));
}

#[test]
fn type_error_span() {
    use crate::base::pos::Span;

    let _ = ::env_logger::try_init();
    let text = r#"
let y = 1.0
y
"#;
    let result = support::typecheck_expr_expected(text, Some(&Type::int())).1;
    let errors: Vec<_> = result.unwrap_err().unwrap_check().into_errors().into();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].span, Span::new(14.into(), 15.into()));
}

#[test]
fn issue_286() {
    let _ = ::env_logger::try_init();
    let text = r#"
let Test = 1
1
"#;
    let result = support::typecheck(text);
    assert_err!(result, Message(..));
}

#[test]
fn no_inference_variable_in_error() {
    let _ = ::env_logger::try_init();
    let text = r#"
() 1
"#;
    let result = support::typecheck(text);

    insta::assert_snapshot!(&*format!("{}", result.unwrap_err()).replace("\t", "        "));
}

#[test]
fn alias_mismatch() {
    let _ = ::env_logger::try_init();
    let text = r#"
type A = | A Int
type B = | B Float
let eq x _ : a -> a -> a = x
eq (A 0) (B 0.0)
"#;
    let result = support::typecheck(text);

    insta::assert_snapshot!(&*format!("{}", result.unwrap_err()).replace("\t", "        "));
}

#[test]
fn unification_error_with_empty_record_displays_good_error_message() {
    let _ = ::env_logger::try_init();
    let text = r#"
let f x y : a -> a -> a = x

f { } { x = 1 }
"#;

    let result = support::typecheck(text);

    insta::assert_snapshot!(&*format!("{}", result.unwrap_err()).replace("\t", "        "));
}

#[test]
fn unable_to_resolve_implicit_error_message() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[implicit]
type Eq a = { }

type Test a = | Test a

let eq_Test : [Eq a] -> Eq (Test a) = { }

let f x : [Eq a] -> a -> a = x

f (Test (Test 1))
"#;

    let result = support::typecheck(text);

    insta::assert_snapshot!(&*format!("{}", result.unwrap_err()).replace("\t", "        "));
}

#[test]
fn long_type_error_format() {
    let long_type: ArcType = Type::function(
        vec![Type::int()],
        Type::ident(KindedIdent::new(Symbol::from(
            "loooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooong",
        ))),
    );
    let err = TypeError::Unification(Type::int(), long_type.clone(), vec![]);
    assert_eq!(
        &*err.to_string(),
        r#"Expected the following types to be equal
Expected: Int
Found: Int
        -> loooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooong
0 errors were found during unification:
"#
    );
}

test_check_err! {
    undefined_field_after_overload,
    r#"
let f =
    \x g ->
        let { x } = g x
        x
let r = f { x = 0 } (\r -> { x = r.x #Int+ 1 })
r.y
"#,
    InvalidProjection(..)
}

#[test]
fn type_constructor_in_function_name() {
    let _ = ::env_logger::try_init();
    let text = r#"
let Test x = x
1
"#;
    let result = support::typecheck(text);
    assert_err!(result, Message(..));
}

#[test]
fn record_base_not_record() {
    let _ = ::env_logger::try_init();
    let text = r#"
{ .. 1 }
"#;
    let result = support::typecheck(text);
    assert_unify_err!(result, TypeMismatch(..));
}

#[test]
fn undefined_type_variable() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Test = a
()
"#;
    let result = support::typecheck(text);
    assert_err!(result, UndefinedVariable(..));
}

#[test]
fn make_with_explicit_types_with_wrong_variable() {
    let _ = ::env_logger::try_init();

    let text = r#"
let make x : b -> _ =
    let f y : b -> a = x
    { f }

make
"#;
    let result = support::typecheck(text);

    assert!(result.is_err(), "{}", result.unwrap_err());
}

#[test]
fn double_type_variable_unification_bug() {
    let _ = ::env_logger::try_init();

    let text = r#"
\k ->
    let { k } = k
    insert k
"#;
    let result = support::typecheck(text);

    assert_err!(result, UndefinedVariable(..));
}

#[test]
fn do_expression_undefined_flat_map() {
    let _ = ::env_logger::try_init();

    let text = r#"
do x = 1
2
"#;
    let result = support::typecheck(text);

    assert_err!(result, UndefinedVariable(..));
}

#[test]
fn do_expression_type_mismatch() {
    let _ = ::env_logger::try_init();

    let text = r#"
let flat_map f = 1
do x = 1
2
"#;
    let result = support::typecheck(text);

    assert_unify_err!(result, TypeMismatch(..));
}

#[test]
fn undefined_type_in_variant() {
    let _ = ::env_logger::try_init();

    let text = r#"
type Test = | Test In
2
"#;
    let result = support::typecheck(text);

    assert_err!(result, UndefinedType(..));
}

#[test]
fn missing_infix_operator_is_reported() {
    let _ = ::env_logger::try_init();

    let text = r#"
2 <> 2 <> 2
"#;
    let result = support::typecheck(text);

    assert_err!(result, UndefinedVariable(..), UndefinedVariable(..));
}

#[test]
fn foldable_bug() {
    let _ = ::env_logger::try_init();

    let text = r#"
type Array a = { x : a }

type Foldable (f : Type -> Type) = {
    foldl : forall a b . (b -> a -> b) -> b -> f a -> b
}

let any x = any x

let foldable : Foldable Array =

    let foldl : forall a b . (a -> b -> b) -> b -> Array a -> b = any ()

    { foldl }
()
"#;
    let result = support::typecheck(text);

    assert_multi_unify_err!(
        result,
        [
            TypeMismatch(..),
            TypeMismatch(..),
            TypeMismatch(..),
            TypeMismatch(..)
        ]
    );
}

#[test]
fn issue_444() {
    let _ = ::env_logger::try_init();

    let text = r#"
let test x : () = () in 1
"#;
    let result = support::typecheck(text);

    assert_unify_err!(result, TypeMismatch(..));
}

#[test]
fn multiple_extra_parameters_error() {
    let _ = ::env_logger::try_init();
    let text = r#"
let id x = x
id "" 1 1.0
"#;
    let result = support::typecheck(text);

    insta::assert_snapshot!(&*format!("{}", result.unwrap_err()).replace("\t", "        "));
}

#[test]
#[ignore] // FIXME
fn effect_unify_function() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Eff r a =
    forall x . (| Pure a | Impure (r x) (x -> Eff r a))

let any x = any x
let x : Eff [| | r |] Int = any ()

let f x a : (a -> a -> b) -> a -> b = x a a

f x 1
"#;
    let result = support::typecheck(text);

    assert_eq!(
        &*format!("{}", result.unwrap_err()).replace("\t", "        "),
        r#"error: Expected the following types to be equal
Expected: Int -> Int -> a
Found: test.Eff [| | r |] Int
1 errors were found during unification:
Types do not match:
    Expected: Int -> Int -> a
    Found: test.Eff [| | r |] Int
- <test>:10:3
   |
10 | f x 1
   |   ^
   |
"#
    );
}

#[test]
fn undefined_alias_in_record_type() {
    let _ = env_logger::try_init();

    let text = r#"
type Test = { MyInt }

()
"#;
    let result = support::typecheck(text);

    assert_err!(result, UndefinedType(..));
}

#[test]
fn different_kind_on_scoped_variable() {
    let _ = env_logger::try_init();

    let text = r#"
let f x : a -> () =
    let g z : a () -> () = ()
    ()
()
"#;
    let result = support::typecheck(text);

    assert_err!(result, KindError(..));
}

test_check_err! {
    issue_703_type_mismatch_in_recursive_function,
    r#"
type List a = | Nil | Cons a (List a)

let reverse xs =
    match xs with
    | Nil -> Nil
    | l -> l

match reverse (Cons 1 Nil) with
| Cons x _ -> x
| Nil -> ""
"#,
Unification(..)
}

test_check_err! {
    missing_type_field,
    r#"
type Alternative f = {
    empty : forall a . f a,
}

rec
type Arr r a b = a -> Eff r b

type Eff r a =
    | Pure a
    | Impure : forall x . r x -> Arr r x a -> Eff r a
in

let any x = any x

let { HttpEffect } = ()

let alt =
    type Alt r a =
        | Empty
        .. r
    let alternative : Alternative (Eff [| alt : Alt | r |]) = {
        empty = any (),
    }
    { alternative }

let alternative : Alternative (Eff (HttpEffect r)) = alt.alternative

()
"#,
UndefinedField(..)
}

test_check_err! {
    issue_807_pattern_match_arg_mismatch,
    r#"
type Test = | Test Int

match Test 0 with
| Test -> ()
"#,
PatternError { .. }
}

test_check_err! {
    do_type_signature_error,
    r#"
type List a = | Cons a (List a) | Nil

let flat_map f x : (a -> List b) -> List a -> List b = Nil

do writer : Int = Cons "" Nil
Cons "" Nil
    "#,
Unification { .. }
}
