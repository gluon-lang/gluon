#[macro_use]
extern crate pretty_assertions;

extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_format as format;
extern crate gluon_parser as parser;

use crate::base::{
    ast::{self, Expr, Pattern, SpannedExpr, Typed, Visitor},
    source,
    symbol::Symbol,
    types::Type,
};

use crate::check::typecheck::{ImplicitError, ImplicitErrorKind, TypeError};

use crate::support::MockEnv;

fn pretty_expr(text: &str, expr: &SpannedExpr<Symbol>) -> String {
    format::pretty_expr(&source::FileMap::new("test".into(), text.to_string()), expr)
}

#[macro_use]
#[allow(unused_macros)]
mod support;

#[test]
fn single_implicit_arg() {
    let _ = ::env_logger::try_init();
    let text = r#"

let f ?x y: [Int] -> Int -> Int = x
#[implicit]
let i = 123
f 42
"#;
    let (expr, result) = support::typecheck_expr(text);

    assert_req!(result, Ok(Type::int()));

    // Verify that the insert implicit argument have the renamed symbol
    match expr.expr().value {
        Expr::LetBindings(_, ref expr) => match expr.value {
            Expr::LetBindings(ref bind, ref app) => match app.value {
                Expr::App {
                    ref implicit_args, ..
                } => match (&implicit_args[0].value, &bind[0].name.value) {
                    (&Expr::Ident(ref arg), &Pattern::Ident(ref bind_id)) => {
                        assert_eq!(arg.name, bind_id.name);
                    }
                    _ => panic!(),
                },
                _ => panic!(),
            },
            _ => panic!(),
        },
        _ => panic!(),
    }
}

#[test]
fn single_implicit_implicit_arg() {
    let _ = ::env_logger::try_init();
    let text = r#"
let f y : [Int] -> Int -> Int = y
#[implicit]
let i = 123
f 42
"#;
    let (expr, result) = support::typecheck_expr(text);

    assert_req!(result, Ok(Type::int()));
    assert_eq!(
        r#"let f ?__implicit_arg y : [Int] -> Int -> Int = y
#[implicit]
let i = 123
f ?i 42"#,
        pretty_expr(text, expr.expr()).trim()
    );
}

#[test]
fn single_implicit_explicit_arg() {
    let _ = ::env_logger::try_init();
    let text = r#"

let f ?x y: [Int] -> Int -> Int = x
f ?32 42
"#;
    let result = support::typecheck(text);

    assert_req!(result, Ok(Type::int()));
}

#[test]
fn multiple_implicit_args() {
    let _ = ::env_logger::try_init();
    let text = r#"

let f ?x ?y z w: [Int] -> [String] -> String -> Int -> Int = x
#[implicit]
let i = 123
#[implicit]
let x = "abc"
f x 42
"#;
    let result = support::typecheck(text);

    assert_req!(result, Ok(Type::int()));
}

#[test]
fn just_a_implicit_arg() {
    let _ = ::env_logger::try_init();
    let text = r#"

let f ?x: [Int] -> Int = x
#[implicit]
let i = 123
f
"#;
    let result = support::typecheck(text);

    assert_req!(result.map(|t| t.to_string()), Ok("[Int] -> Int"));
}

#[test]
fn function_implicit_arg() {
    let _ = ::env_logger::try_init();
    let text = r#"

let f ?eq l r: [a -> a -> Bool] -> a -> a -> Bool = eq l r
#[implicit]
let eq_int l r : Int -> Int -> Bool = True
#[implicit]
let eq_string l r : String -> String -> Bool = True
let _ = f 1 2
let _ = f "" ""
()
"#;
    let result = support::typecheck(text);

    assert_req!(result, Ok(Type::unit()));
}

#[test]
fn infix_implicit_arg() {
    let _ = ::env_logger::try_init();
    let text = r#"

#[infix(left, 1)]
let (==) ?eq l r: [a -> a -> Bool] -> a -> a -> Bool = eq l r
#[implicit]
let eq_int l r : Int -> Int -> Bool = True
#[implicit]
let eq_string l r : String -> String -> Bool = True
"" == ""
"#;
    let (expr, _result) = support::typecheck_expr(text);
    let mut expr = expr.expr();

    loop {
        match &expr.value {
            ast::Expr::LetBindings(_, body) => {
                expr = body;
            }
            _ => match expr.value {
                ast::Expr::Infix {
                    ref implicit_args, ..
                } if implicit_args.len() == 1 => {
                    let env = MockEnv::new();
                    assert_eq!(
                        implicit_args[0].env_type_of(&env).to_string(),
                        "String -> String -> Bool"
                    );
                    break;
                }
                _ => assert!(false),
            },
        }
    }
}

#[test]
fn implicit_from_record_field() {
    let _ = ::env_logger::try_init();
    let text = r#"

let f ?eq l r: [a -> a -> Bool] -> a -> a -> Bool = eq l r
#[implicit]
let eq_int l r : Int -> Int -> Bool = True
let eq_string @ { ? } =
    #[implicit]
    let eq l r : String -> String -> Bool = True
    { eq }
let _ = f 1 2
let _ = f "" ""
()
"#;
    let result = support::typecheck(text);

    assert_req!(result, Ok(Type::unit()));
}

#[test]
fn implicit_on_type() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[implicit]
type Test = | Test ()
let f ?x y: [a] -> a -> a = x
let i = Test ()
f (Test ())
"#;
    let result = support::typecheck(text);

    let test = support::alias_variant_implicit("Test", &[], &[("Test", &[Type::unit()])], true);
    assert_req!(result, Ok(test));
}

test_check! {
implicit_on_type_force_projection,
    r#"
#[implicit]
type Test = | Test ()
let record =
    let f ?x: [a] -> a = x
    { f }
let z = Test ()
let i : Test = record.f
()
"#,
"()"
}

#[test]
fn implicit_with_implicit_arguments() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[implicit]
type Test a = | Test a

type List a = | Nil | Cons a (List a)

let int : Test Int = Test 0
let list ?t : [Test a] -> Test (List a) = Test Nil

let f x : [Test a] -> a -> a = x
f (Cons 1 Nil)
"#;
    let (expr, result) = support::typecheck_expr(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());

    struct Visitor {
        text: &'static str,
        done: bool,
    }
    impl<'a> base::ast::Visitor<'a, '_> for Visitor {
        type Ident = Symbol;

        fn visit_expr(&mut self, expr: &'a SpannedExpr<Symbol>) {
            match expr.value {
                ast::Expr::App {
                    ref func,
                    ref implicit_args,
                    ..
                } => match func.value {
                    ast::Expr::Ident(ref id) if id.name.definition_name() == "f" => {
                        assert!(implicit_args.len() == 1);
                        let implicit = &implicit_args[0];

                        assert_eq!("list int", pretty_expr(self.text, implicit).trim());
                        self.done = true;
                    }
                    _ => base::ast::walk_expr(self, expr),
                },
                _ => base::ast::walk_expr(self, expr),
            }
        }
    }
    let mut visitor = Visitor { text, done: false };
    visitor.visit_expr(&expr.expr());
    assert!(visitor.done);
}

#[test]
fn catch_infinite_loop() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[implicit]
type Test a = | Test a

type List a = | Nil | Cons a (List a)

let f ?x : [Test a] -> Test a = x
let g ?x y : [Test a] -> Int -> Test a = x

g 1
"#;
    let result = support::typecheck(text);

    assert_err!(
        result,
        TypeError::UnableToResolveImplicit(ImplicitError {
            kind: ImplicitErrorKind::LoopInImplicitResolution(..),
            ..
        })
    );
}

#[test]
fn implicit_ord() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[implicit]
type Eq a = { (==) : a -> a -> Bool }

#[implicit]
type Ord a = { eq : Eq a, compare : a -> a -> () }

type Option a = | None | Some a

let any x = any x

let eq ?a : [Eq a] -> Eq (Option a) = {
    (==) = \l r -> True
}

let ord : [Ord a] -> Ord (Option a) =
    {
        eq = eq,
        compare = any ()
    }
()
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn forward_implicit_parameter() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[implicit]
type Test a = | Test a
let f ?x y : [Test a] -> () -> Test a = x
let g ?x y : [Test a] -> a -> Test a = f ()
let i = Test 1
let _ = g 2
()
"#;
    let (expr, result) = support::typecheck_expr(text);

    assert_req!(result, Ok(Type::unit()));

    struct Visitor {
        text: &'static str,
        done: bool,
    }
    impl<'a> base::ast::Visitor<'a, '_> for Visitor {
        type Ident = Symbol;

        fn visit_expr(&mut self, expr: &'a SpannedExpr<Symbol>) {
            match expr.value {
                ast::Expr::LetBindings(ref bindings, _) => {
                    if let ast::Pattern::Ident(ref id) = bindings[0].name.value {
                        if id.name.definition_name() == "g" {
                            assert_eq!("f ?x ()", pretty_expr(self.text, &bindings[0].expr).trim());
                            self.done = true;
                        }
                    }
                }
                _ => (),
            }
            base::ast::walk_expr(self, expr)
        }
    }
    let mut visitor = Visitor { text, done: false };
    visitor.visit_expr(&expr.expr());
    assert!(visitor.done);
}

#[test]
fn implicit_as_function_argument() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[infix(left, 1)]
let (==) ?eq l r: [a -> a -> Bool] -> a -> a -> Bool = eq l r
#[implicit]
let eq_int l r : Int -> Int -> Bool = True
#[implicit]
let eq_string l r : String -> String -> Bool = True

let f eq l r : (a -> a -> Bool) -> a -> a -> Bool = eq l r
f (==) 1 2
"#;
    let (expr, result) = support::typecheck_expr(text);
    let mut expr = expr.expr();

    assert!(result.is_ok(), "{}", result.unwrap_err());

    loop {
        match &expr.value {
            ast::Expr::LetBindings(_, body) => {
                expr = body;
            }
            _ => match expr.value {
                ast::Expr::App { ref args, .. } if args.len() == 3 => {
                    assert_eq!(args.len(), 3);
                    match args[0].value {
                        ast::Expr::App {
                            args: ref args_eq,
                            implicit_args: ref implicit_args_eq,
                            ..
                        } => {
                            assert_eq!(args_eq.len(), 0);
                            assert_eq!(implicit_args_eq.len(), 1);
                        }
                        _ => panic!(),
                    }
                    break;
                }
                _ => assert!(false),
            },
        }
    }
}

#[test]
fn applicative_resolve_implicit() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[implicit]
type Functor f = {
    map : forall a b . (a -> b) -> f a -> f b
}

#[implicit]
type Applicative (f : Type -> Type) = {
    functor : Functor f,
    apply : forall a b . f (a -> b) -> f a -> f b,
}

#[infix(left, 1)]
let (<*>) ?app : [Applicative f] -> f (a -> b) -> f a -> f b = app.apply
#[infix(left, 1)]
let (<*) ?app l r : [Applicative f] -> f a -> f b -> f a = app.functor.map (\x _ -> x) l <*> r
()
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn select_functor_from_applicative() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[implicit]
type Functor f = {
    map : forall a b . (a -> b) -> f a -> f b
}

#[implicit]
type Applicative (f : Type -> Type) = {
    functor : Functor f,
    apply : forall a b . f (a -> b) -> f a -> f b,
}

let map ?functor : [Functor f] -> (a -> b) -> f a -> f b = functor.map

let test xs: [Applicative f] -> (a -> b) -> f a -> f b =
    map xs
()
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn wrap_call_selection() {
    let _ = ::env_logger::try_init();
    let text = r#"

#[implicit]
type Applicative (f : Type -> Type) = {
    wrap : forall a . a -> f a,
}

let wrap ?app : [Applicative f] -> a -> f a = app.wrap

type Test a = | Test a

let applicative : Applicative Test = {
    wrap = Test
}

let x: a -> Test Int = \_ -> wrap 123
()
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn unknown_implicit_arg_type() {
    let _ = ::env_logger::try_init();
    let text = r#"

#[implicit]
type Applicative (f : Type -> Type) = {
    wrap : forall a . a -> f a,
}

let wrap ?app : [Applicative f] -> a -> f a = app.wrap

type Test a = | Test a

let applicative : Applicative Test = {
    wrap = Test
}

\_ -> wrap 123
"#;
    let (_expr, result) = support::typecheck_expr(text);
    assert_err!(result, TypeError::UnableToResolveImplicit(..));
}

#[test]
fn dont_insert_extra_implicit_arg_type() {
    let _ = ::env_logger::try_init();
    let text = r#"

#[implicit]
type Applicative (f : Type -> Type) = {
    wrap : forall a . a -> f a,
}

let wrap ?app : [Applicative f] -> a -> f a = app.wrap

type Test a = | Test a

let applicative : Applicative Test = {
    wrap = Test
}

wrap
"#;
    let result = support::typecheck(text);
    assert_req!(
        result.map(|typ| typ.to_string()),
        Ok("forall a a0 . [test.Applicative a] -> a0 -> a a0")
    );
}

#[test]
fn dont_insert_implicit_with_unresolved_arguments() {
    let _ = ::env_logger::try_init();
    let text = r#"

#[implicit]
type Alternative f = {
    empty : forall a . f a
}

type Test a = | Test a | Empty

let empty ?alt : [Alternative f] -> f a = alt.empty

let x: Test Int = empty
x
"#;
    let result = support::typecheck(text);
    assert_err!(result, TypeError::UnableToResolveImplicit(..));
}

#[test]
fn resolve_implicit_for_fold_m() {
    let _ = ::env_logger::try_init();
    let text = r#"
type List a = | Nil | Cons a (List a)

#[implicit]
type Foldable (f : Type -> Type) = {
}

type Monad (m : Type -> Type) = {
}

let foldable : Foldable List =
    { }

let monad : Monad List =
    { }

let fold_m monad f z w : forall a b m t . [Foldable t] -> Monad m -> (a -> b -> m a) -> a -> t b -> () = ()

let fold_m2 ?x : [Foldable t] -> _ -> _ -> t b -> _ = fold_m monad

let f x : List Int -> _ = fold_m2 (\a b -> Cons a Nil) x
f
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn resolve_implicit_which_is_generic() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[implicit]
type Semigroup a = {
    append : a -> a -> a
}

type List a = | Nil | Cons a (List a)

let semigroup : Semigroup (List a) =
    let append xs ys =
        match xs with
        | Cons x zs -> Cons x (append zs ys)
        | Nil -> ys

    { append }

#[infix(left, 1)]
let (<>) ?s : [Semigroup a] -> a -> a -> a = s.append

Nil <> Nil
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn resolve_implicit_semigroup() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[implicit]
type Semigroup a = {
    append : a -> a -> a
}

#[implicit]
type Applicative (f : Type -> Type) = {
    apply : forall a b . f (a -> b) -> f a -> f b,
}

#[implicit]
type Eq a = { (==) : a -> a -> Bool }

type List a = | Nil | Cons a (List a)

let any x = any x

let semigroup : Semigroup (List a) = any ()

let eq ?eq : [Eq a] -> Eq (List a) =
    #[infix(left, 1)]
    let (==) l r = True
    { (==) }


#[infix(left, 1)]
let (<>) ?s : [Semigroup a] -> a -> a -> a = s.append

let map f xs =
    match xs with
    | Cons y ys -> Cons (f y) (map f ys)
    | Nil -> Nil

let applicative : Applicative List =

    let apply f xs =
        match f with
        | Cons g gs -> (map g xs) <> (apply gs xs)
        | Nil -> Nil

    { apply }

()
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn resolve_generic_type_multiple_times() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[implicit]
type Applicative (f : Type -> Type) = {
}

type State s a = s -> (s, a)

let any x = any x

let impls =
    let applicative : Applicative (State s) = { }

    { applicative }

let { ? } = impls

#[infix(left, 1)]
let (*>) ?app l r : [Applicative f] -> f a -> f b -> f b = any ()

let put value : s -> State s () = any ()

let get : State s s = any ()

let _ = (put 1 *> get)
(put "hello" *> get)
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn implicit_list_without_inner_type_determined() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[implicit]
type Test a = | Test a

type List a = | Nil | Cons a (List a)

let int : Test Int = Test 0
let list ?t : [Test a] -> Test (List a) = Test Nil

let f x : [Test a] -> a -> a = x
f Nil
"#;
    let result = support::typecheck(text);
    assert_err!(
        result,
        TypeError::UnableToResolveImplicit(ImplicitError {
            kind: ImplicitErrorKind::LoopInImplicitResolution(..),
            ..
        })
    );
}

#[test]
fn compare() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Ordering = | LT | EQ | GT
#[implicit]
type Ord a = { compare : a -> a -> Ordering }

let compare ?ord : [Ord a] -> a -> a -> Ordering = ord.compare

#[infix(left, 1)]
let (<) l r : [Ord a] -> a -> a -> Bool =
    match compare l r with
    | LT -> True
    | EQ -> False
    | GT -> False
()
"#;
    let (expr, _result) = support::typecheck_expr(text);

    struct Visitor {
        text: &'static str,
        done: bool,
    }
    impl<'a> base::ast::Visitor<'a, '_> for Visitor {
        type Ident = Symbol;

        fn visit_expr(&mut self, expr: &'a SpannedExpr<Symbol>) {
            match expr.value {
                ast::Expr::App {
                    ref func,
                    ref implicit_args,
                    ..
                } => {
                    if let ast::Expr::Ident(ref id) = func.value {
                        if id.name.definition_name() == "compare" {
                            assert_eq!(
                                "__implicit_arg",
                                pretty_expr(self.text, &implicit_args[0]).trim()
                            );
                            self.done = true;
                        }
                    }
                }
                _ => (),
            }
            base::ast::walk_expr(self, expr)
        }
    }
    let mut visitor = Visitor { text, done: false };
    visitor.visit_expr(&expr.expr());
    assert!(visitor.done);
}

#[test]
fn disambiguate_distinct_records() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[implicit]
type Implicit a = { f : a -> String }

type Test1 = { x : Int }
let t1_test : Implicit Test1 = { f = \x -> "" }

type Test2 = { x : Int, y : Int }
let t2_test : Implicit Test2 = { f = \x -> "" }

let f ?x y: [Implicit a] -> a -> String = ""
f { x = 1 }
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn type_hole_applicative() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[implicit]
type Functor f = {
    map : forall a b . (a -> b) -> f a -> f b
}

#[implicit]
type Applicative (f : Type -> Type) = {
    functor : Functor f,
    apply : forall a b . f (a -> b) -> f a -> f b,
}

let map ?f : [Functor f] -> (a -> b) -> f a -> f b = f.map

let apply ?app : [Applicative f] -> f (a -> b) -> f a -> f b = app.apply

#[infix(left, 4)]
let (<*>) : [Applicative f] -> f (a -> b) -> f a -> f b = apply

let map2 fn a b : [Applicative f] -> _
    = map fn a <*> b

{}
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn allow_importing_same_record_twice() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[implicit]
type Test a = | Test a

let mod =
    let int : Test Int = Test 0
    let string : Test String = Test ""
    { int, string }

let { ? } = mod
let { ? } = mod

let f x : [Test a] -> a -> a = x
f 1
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn allow_sub_classed_duplicate() {
    let _ = ::env_logger::try_init();
    let text = r#"
#[implicit]
type Base a = { x : a }
#[implicit]
type Derived a = { base : Base a, y : a }
#[implicit]
type Derived2 a = { derived : Derived a, z : a }

let { ? } =
    let base : Base Int = { x = 0 }
    let derived : Derived Int = { base, y = 1 }
    let derived2 : Derived2 Int = { derived, z = 2 }
    { base, derived, derived2 }

let f ?b x : [Base a] -> a -> a = b.x
f 1
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

test_check_err! {
break_infinite_implicit_resolve_early,
    r#"
#[implicit]
type Implicit a = { f : a -> String }

type Test a = { x : a }

let any x = any x

let test : [Implicit a] -> Implicit (Test a) = any ()

let f : [Implicit a] -> a -> () = any ()

f (any ())
"#,
TypeError::UnableToResolveImplicit(ImplicitError {
    kind: ImplicitErrorKind::LoopInImplicitResolution(..),
    ..
})
}

test_check! {
one_binding_used_twice,
r#"
#[implicit]
type Test a = | Test a

type Pair a b = { x : a, y : b }

let any x = any x

let pair_test: [Test a] -> [Test b] -> Test (Pair a b) = any ()
let int_test: Test Int = Test 1

let test x : [Test a] -> a -> () = ()

test { x = 1, y = 2 }
"#,
"()"
}

test_check! {
one_binding_nested_1,
r#"
#[implicit]
type Test a = | Test a

type Value a = { x : a }

let any x = any x

let value_test: [Test a] -> Test (Value a) = any ()
let int_test: Test Int = Test 1

let test x : [Test a] -> a -> () = ()

test { x = { x = 1 } }
"#,
"()"
}

test_check! {
one_binding_nested_2,
r#"
#[implicit]
type Test a = | Test a

type Value a = { x : a }

let any x = any x

let value_test: [Test a] -> Test (Value a) = any ()
let value_test: [Test a] -> Test (Array a) = any ()
let int_test: Test Int = Test 1

let test x : [Test a] -> a -> () = ()

test { x = [{ x = 1 }] }
"#,
"()"
}

test_check! {
recursive_binding_scoped_variables,
r#"
type Show a = { show : a -> () }

type Test a =
    | Test a

rec
let eq_Test a : a -> () = ()
let show_Test : Show (Test a) =
    rec let show_ x : Test a -> () = ()
    { show = show_ }

()
"#,
"()"
}

test_check! {
field_with_implicit_parameter,
r#"
#[implicit]
type Monad m = { wrap : a -> m a }

type StateT s m a = s -> m { value : a, state : s }

let any x = any x

#[implicit]
type Transformer t = {
    wrap_monad : forall a m . [Monad m] -> m a -> t m a
}

let transformer : Transformer (StateT s) =
    let wrap_monad : [Monad m] -> m a -> StateT s m a = any ()

    { wrap_monad }

()
"#,
"()"
}

test_check! {
unable_to_resolve_double_nested_instance,
r#"
#[implicit]
type Functor f = {
    map : forall a b . (a -> b) -> f a -> f b
}
#[implicit]
type Applicative f = {
    functor : Functor f,
}
#[implicit]
type Monad m = { functor : Applicative m }

let any x = any x

let eval_state_t f : [Functor m] -> m a -> () = ()

let associativity mx : [Monad m] -> m a -> () =
    eval_state_t mx

()
"#,
"()"
}

test_check! {
match_inference,
r#"
let any x = any x
let assert x : Bool -> () = ()
type Result e t = | Err e | Ok t
type Channel t = { x : t }
let recv x : Channel t -> Result e t = any ()
#[infix(left, 4)]
let (==) :  a -> a -> Bool = any ()

let f receiver : Channel Int -> _ =
    match recv receiver with
    | Ok x -> assert (x == 1)
    | Err _ -> assert False

()
"#,
"()"
}

test_check! {
ord_array_implicit_resolution,
r#"

#[implicit]
type Eq a = { (==) : a -> a -> Bool }

#[implicit]
type Ord a = { eq : Eq a, compare : a -> a -> () }

let eq ?eq : [Eq a] -> Eq (Array a) =
    { (==) = \x y -> False }

let ord ?ord : [Ord a] -> Ord (Array a) =
    let array_cmp l r = array_cmp l r
    { eq, compare = \_ _ -> () }

()
"#,
"()"
}

test_check! {
ord_array_implicit_resolution2,
r#"

#[implicit]
type Eq a = { (==) : a -> a -> Bool }

#[implicit]
type Ord a = { eq : Eq a, compare : a -> a -> () }

let eq ?eq : [Eq a] -> Eq (Array a) =
    { (==) = \x y -> False }

let ord ?ord : [Ord a] -> Ord (Array a) =
    { eq, compare = \_ _ -> () }

()
"#,
"()"
}

test_check! {
do_expression_with_fully_applied_alias_1,
r#"
#[implicit]
type Monad (m : Type -> Type) = {
    flat_map : forall a b . (a -> m b) -> m a -> m b
}

let flat_map ?m : [Monad m] -> (a -> m b) -> m a -> m b = m.flat_map

type Test a = { x : a }
let monad : Monad Test = {
    flat_map = \f x -> f x.x,
}
let test x : a -> Test a = { x }

type TestInt = Test Int

let x : TestInt =
    do x = test 1
    test x
x
"#,
"test.TestInt"
}

test_check! {
implicits_in_multiple_scopes,
r#"
#[implicit]
type Test a = { x : a }

let module =
    let test: Test Int = { x = 0 }
    { test }

let module2 =
    let test: Test Int = { x = 1 }
    { test }

let test ?t : [Test a] -> a = t.x

[
    (\_ ->
        let { ? } = module
        let x: Int = test
        x
    ),
    (\_ ->
        let { ? } = module2
        let x: Int = test
        x
    ),
]
"#,
"forall a . Array (a -> Int)"
}
