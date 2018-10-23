#[macro_use]
extern crate quick_error;
#[macro_use]
extern crate collect_mac;
extern crate env_logger;
#[macro_use]
extern crate pretty_assertions;

extern crate gluon_base as base;
extern crate gluon_check as check;
extern crate gluon_parser as parser;

use base::ast::{Expr, Pattern, SpannedExpr};
use base::pos::{BytePos, Span};
use base::symbol::Symbol;
use base::types::{Field, Type};

use support::{alias, intern, typ, MockEnv};

#[macro_use]

mod support;

#[test]
fn module() {
    let _ = env_logger::try_init();

    let text = r"
type SortedList a = | Cons a (SortedList a)
                | Nil
in \(<) ->
    let empty = Nil
    let insert x xs =
        match xs with
        | Nil -> Cons x Nil
        | Cons y ys -> if x < y
                       then Cons x xs
                       else Cons y (insert x ys)
    let ret = { empty, insert }
    ret
";
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn call_error_span() {
    let _ = env_logger::try_init();

    let text = r#"
let f x = x #Int+ 1
in f "123"
"#;
    let result = support::typecheck(text);

    assert!(result.is_err());
    let errors: Vec<_> = result.unwrap_err().errors().into();
    assert_eq!(errors.len(), 1);
    assert_eq!(
        errors[0].span,
        Span::new(BytePos::from(27), BytePos::from(32))
    );
}

#[test]
fn shadowed_binding() {
    let _ = env_logger::try_init();

    let text = r"
let test x: Int -> Int = 1
let test x: Int -> Int = 0
test 1
";
    let (expr, result) = support::typecheck_expr(text);

    assert!(result.is_ok());
    let (bind, call) = match expr.value {
        Expr::LetBindings(_, ref body) => match body.value {
            Expr::LetBindings(ref binds, ref body) => (&binds[0], body),
            _ => panic!(),
        },
        _ => panic!(),
    };
    let call_id = match call.value {
        Expr::App { ref func, .. } => match func.value {
            Expr::Ident(ref id) => id,
            _ => panic!(),
        },
        _ => panic!(),
    };
    let test_id = match bind.name.value {
        Pattern::Ident(ref id) => id,
        _ => panic!(),
    };
    assert_eq!(test_id.name, call_id.name);
}

#[test]
fn types_should_be_fully_instantiated_even_on_errors() {
    let _ = env_logger::try_init();

    let text = r#"
let a = { id = \x -> x, z = 1 #Int== 2.0 }
a.id
"#;
    let (expr, _result) = support::typecheck_expr(text);
    let t = match expr.value {
        Expr::LetBindings(_, ref body) => match body.value {
            Expr::Projection(_, _, ref typ) => typ,
            _ => panic!(),
        },
        _ => panic!(),
    };
    let expected = Type::function(vec![typ("a")], typ("a"));

    assert_eq2!(*t, expected);
}

#[test]
fn non_self_recursive_alias() {
    let _ = env_logger::try_init();

    let text = r#"
type Type1 = { x: Int }
type Type2 = Type1
type Type3 = { x: Int }
let r1: Type1 = { x = 0 }
let r2: Type2 = r1
let r3: Type3 = r2
in r1"#;
    let result = support::typecheck(text);
    let expected = Ok(alias(
        "Type1",
        &[],
        Type::record(vec![], vec![Field::new(intern("x"), typ("Int"))]),
    ));

    assert_eq!(result, expected);
}

#[test]
fn scoped_generic_variable() {
    let _ = ::env_logger::try_init();
    let text = r#"
let any x = any x
let make m: m -> { test: m, test2: m } =
    let m2: m = any ()
    { test = m, test2 = m2 }

make
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn simplified_applicative() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Applicative f = {
    map : forall a b . (a -> b) -> f a -> f b,
    apply : forall c d . f (c -> d) -> f c -> f d
}

let applicative_Function : forall a. Applicative ((->) a) = {
    map = \f g x -> f (g x),
    apply = \f g x -> f x (g x)
}

let id : forall a. a -> a = \x -> x

let const : forall a b. a -> b -> a = \x _ -> x

let make_applicative app : forall f. Applicative f -> _ =
    let { map, apply } = app

    #[infix(left, 1)]
    let (*>) l r: forall a b . f a -> f b -> f b =
        apply (map (const id) l) r

    ()

make_applicative applicative_Function
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn type_alias_with_explicit_hole_kind() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Test (a : _) = a
type Bar = Test Int
()
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn type_alias_with_explicit_type_kind() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Test (a : Type) = a
type Bar = Test Int
()
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn type_alias_with_explicit_row_kind() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Test (a : Row -> Type) (b : Row) = a b
()
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn type_alias_with_explicit_function_kind() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Test (a : Type -> Type) = a Int
type Foo a = a
type Bar = Test Foo
()
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

/// Check that after typechecking, the resulting types are `Alias`, not `Ident`. This is necessary
/// so that when the type is later propagated it knows what its internal representation are without
/// any extra information
#[test]
fn applied_constructor_returns_alias_type() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Test = | Test Int
Test 0
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
    match *result.unwrap() {
        Type::Alias(_) => (),
        ref typ => panic!("Expected alias, got {:?}", typ),
    }
}
#[test]
fn dont_guess_a_record_when_the_construction_has_no_fields() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Test = { x : Int }
type Test2 = Int

{ Test2 }
"#;
    let result = support::typecheck(text);
    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn simple_tuple_type() {
    let _ = ::env_logger::try_init();
    let text = r#"
("test", 123)
"#;
    let result = support::typecheck(text);

    let interner = support::get_local_interner();
    let mut interner = interner.borrow_mut();
    assert_eq!(
        result,
        Ok(Type::tuple(
            &mut *interner,
            vec![Type::string(), Type::int()]
        ))
    );
}

#[test]
fn match_tuple_type() {
    let _ = ::env_logger::try_init();
    let text = r#"
match (1, "test") with
| (x, y) -> (y, x)
"#;
    let result = support::typecheck(text);

    let interner = support::get_local_interner();
    let mut interner = interner.borrow_mut();
    assert_eq!(
        result,
        Ok(Type::tuple(
            &mut *interner,
            vec![Type::string(), Type::int()]
        ))
    );
}

#[test]
fn match_tuple_record() {
    let _ = ::env_logger::try_init();
    let text = r#"
match (1, "test") with
| { _1, _0 } -> _1
"#;
    let result = support::typecheck(text);

    assert_eq!(result, Ok(Type::string()));
}

#[test]
fn field_access_tuple() {
    let _ = ::env_logger::try_init();
    let text = r#"
(1, "test")._0
"#;
    let result = support::typecheck(text);

    assert_eq!(result, Ok(Type::int()));
}

#[test]
fn unit_tuple_match() {
    let _ = ::env_logger::try_init();
    let text = r#"
match () with
| () -> ()
"#;
    let result = support::typecheck(text);

    assert_eq!(result, Ok(Type::unit()));
}

#[test]
fn alias_selection_on_pattern_match() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Test = {
    x : Float,
    y : Float
}
type Test2 = {
    x : Int
}
let { x } = { x = 1 }
x
"#;
    let result = support::typecheck(text);

    assert_eq!(result, Ok(Type::int()));
}

#[test]
fn dont_lookup_record_alias_on_pattern_match() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Test = {
    x : Float,
    y : Float
}
let { x } = { x = 1, z = 3 }
x
"#;
    let result = support::typecheck(text);

    assert_eq!(result, Ok(Type::int()));
}

#[test]
fn record_expr_base() {
    let _ = ::env_logger::try_init();
    let text = r#"
let vec2 = { x = 1, y = 2 }
{ z = 3, .. vec2 }
"#;
    let result = support::typecheck(text);

    assert_eq!(
        result,
        Ok(Type::record(
            vec![],
            vec![
                Field::new(intern("z"), typ("Int")),
                Field::new(intern("x"), typ("Int")),
                Field::new(intern("y"), typ("Int")),
            ]
        ))
    );
}

#[test]
fn record_expr_base_overwrite_field() {
    let _ = ::env_logger::try_init();
    let text = r#"
let record = { x = 1 }
{ x = "", .. record }
"#;
    let result = support::typecheck(text);

    assert_eq!(
        result,
        Ok(Type::record(
            vec![],
            vec![Field::new(intern("x"), typ("String"))]
        ))
    );
}

#[test]
fn undefined_type_variable_in_record() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Test = {
    x: a
}
let any x = any x
{ x = any () }.x
"#;
    let result = support::typecheck(text);
    assert_req!(
        result.map(|x| x.to_string()),
        Ok("forall a . a".to_string())
    );
}

#[test]
fn make_category() {
    let _ = ::env_logger::try_init();
    let text = r#"
type Category (cat : Type -> Type -> Type) = {
    id : forall a a . cat a a,
    compose : forall a b c . cat b c -> cat a b -> cat a c
}

let category_Function : Category (->) = {
    id = \x -> x,
    compose = \f g x -> f (g x)
}

let make_Category cat : Category cat -> _ =
    let { id, compose } = cat

    #[infix(left, 1)]
    let (<<) : forall a b c . cat b c -> cat a b -> cat a c = compose

    { id, compose, (<<) }

make_Category category_Function
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn functor_function() {
    let _ = ::env_logger::try_init();

    let text = r#"
type Category (cat : Type -> Type -> Type) = {
    id : forall a . cat a a,
    compose : forall a b c . cat b c -> cat a b -> cat a c
}

let category_Function : Category (->) = {
    id = \x -> x,
    compose = \f g x -> f (g x)
}

let id : a -> a = category_Function.id

type Functor f = {
    map : forall a b . (a -> b) -> f a -> f b
}

let functor_Function : Functor ((->) a) = { map = category_Function.compose }
0
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn type_field_and_make_function_do_not_introduce_forall() {
    let _ = ::env_logger::try_init();

    let text = r#"
type Test a = { x : a }
let id x : forall a . a -> a = x
let make_Category id : (forall a . a -> a) -> _ =

    { id, }
let x = { Test, make_Category }
let { Test } = x
1
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn type_constructor_is_specialized() {
    let _ = ::env_logger::try_init();

    let text = r#"
type Option a = | None | Some a

type Functor f = {
    map : forall a b . (a -> b) -> f a -> f b
}

type Applicative (f : Type -> Type) = {
    functor : Functor f,
    apply : forall a b . f (a -> b) -> f a -> f b,
    wrap : forall a . a -> f a
}

type Traversable t = {
    traverse : forall a b m . Applicative m -> (a -> m b) -> t a -> m (t b)
}

let any x = any x

let traversable : Traversable Option = {
    traverse = \app f o ->
        match o with
        | None -> app.wrap None
        | Some x -> app.functor.map Some (f x)
}

1
"#;
    let (expr, result) = support::typecheck_expr(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());

    struct Visitor;
    impl<'a> base::ast::Visitor<'a> for Visitor {
        type Ident = Symbol;

        fn visit_expr(&mut self, expr: &'a SpannedExpr<Symbol>) {
            match expr.value {
                Expr::Ident(ref id) if id.name.declared_name() == "Some" => {
                    assert_eq!(id.typ.to_string(), "b -> test.Option b");
                }
                _ => base::ast::walk_expr(self, expr),
            }
        }
    }
    base::ast::Visitor::visit_expr(&mut Visitor, &expr)
}

#[test]
fn writer_bug() {
    let _ = ::env_logger::try_init();

    let text = r#"
type Writer w a = { value : a, writer : w }

type Functor f = {
    map : forall a b . (a -> b) -> f a -> f b
}

let functor : Functor (Writer w) = {
    map = \f m -> { value = f m.value, writer = m.writer }
}

1
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn test_bug() {
    let _ = ::env_logger::try_init();

    let text = r#"
type List a = | Cons a (List a) | Nil

type Writer w a = { value : a, writer : w }

type Applicative (f : Type -> Type) = {
    apply : forall a b . f (a -> b) -> f a -> f b,
    wrap : forall a . a -> f a
}

let any x = any x

let writer : { applicative : Applicative (Writer (List b)) } = any ()
let { wrap } = writer.applicative

let tell : List String -> Writer (List String) () = any ()

let assert_eq show eq = \x y ->
    if True
    then wrap ()
    else tell (Cons ("Assertion failed: ") Nil)

1
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn unpack_make_record_with_alias() {
    let _ = ::env_logger::try_init();

    let text = r#"
type List a = | Cons a (List a) | Nil

let make x : b -> _ =
    let f y : b -> b = x
    { List, x, f }

let { List, f } = make 1
1
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

// Unsure if this should be able to compile as is (without  type annotations)
#[test]
#[ignore]
fn preserve_forall_when_lifting_into_record() {
    let _ = ::env_logger::try_init();

    let text = r#"
type Map k a = | Bin k a (Map k a) (Map k a) | Tip
type List a = | Cons a

let cons x = Cons x

let make x : b -> _ =
    { x, cons }
make 1
"#;
    let result = support::typecheck(text);

    assert_eq!(
        result.map(|x| x.to_string()),
        Ok("{ x : Int, cons : forall a . a -> test.List a }".to_string())
    );
}

#[test]
fn resolve_app_app() {
    use base::resolve;

    let record = Type::record(
        vec![],
        vec![
            Field::new(support::intern_unscoped("x"), typ("a")),
            Field::new(support::intern_unscoped("y"), typ("b")),
        ],
    );
    let alias = Type::app(
        Type::app(
            alias("Test", &["a", "b"], record.clone()),
            collect![Type::unit()],
        ),
        collect![Type::int()],
    );

    let actual = resolve::remove_aliases(&MockEnv::new(), alias);
    assert_eq!(actual.to_string(), "{ x : (), y : Int }");
}

#[test]
fn make_with_explicit_types() {
    let _ = ::env_logger::try_init();

    let text = r#"
let make x : b -> _ =
    let f y : b -> b = x
    { f }

make
"#;
    let result = support::typecheck(text);

    assert_req!(
        result.map(|x| x.to_string()),
        Ok("forall a . a -> { f : a -> a }".to_string())
    );
}

#[test]
fn universally_quantified_argument() {
    let _ = ::env_logger::try_init();

    let text = r#"
let test x : (forall a . a -> a) -> () = ()
1
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn alternative_dont_unify_skolem() {
    let _ = ::env_logger::try_init();

    let text = r#"
type Option a = | None | Some a

type Applicative (f : Type -> Type) = {
    wrap : forall a . a -> f a
}

type Alternative f = {
    or : forall a . f a -> f a -> f a,
}

let alternative : Alternative Option = {
    or = \x y ->
        match x with
        | Some _ -> x
        | None -> y,
}

let make_Alternative alternative : Alternative f -> _ =
    { (<|>) = alternative.or }

#[infix(left, 1)]
let (<|>) = (make_Alternative alternative).(<|>)

None <|> Some 1
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn unify_record_field_with_forall() {
    let _ = ::env_logger::try_init();

    let text = r#"
type Option a = | None | Some a

type Function = {
    vararg : Option String,
}

type Expr = | Function Function

Function {
    vararg = None,
}
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn make_singleton() {
    let _ = ::env_logger::try_init();

    let text = r#"

type Map k a = | Bin k a (Map k a) (Map k a) | Tip

let empty = Tip

let singleton_ k v = Bin k v empty empty

let make ord : k -> _ =
    { singleton = singleton_ }

let { singleton } = make ()

singleton "" ()
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn foldable_bug() {
    let _ = ::env_logger::try_init();

    let text = r#"
type Option a = | None | Some a

type Semigroup a = {
    append : a -> a -> a
}
type Monoid a = {
    semigroup : Semigroup a,
    empty : a
}

type Foldable (f : Type -> Type) = {
    foldr : forall a b . (a -> b -> b) -> b -> f a -> b,
    foldl : forall a b . (b -> a -> b) -> b -> f a -> b
}

let make_Foldable foldable : Foldable t -> _ =
    let { foldr, foldl } = foldable

    let concat monoid : Monoid m -> t m -> m =
        foldr monoid.semigroup.append monoid.empty

    let concat_map monoid f : Monoid m -> (a -> m) -> t a -> m =
        foldr (\x -> monoid.semigroup.append (f x)) monoid.empty

    ()
()
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn parser_bug() {
    let _ = ::env_logger::try_init();

    let text = r#"
type Result e t = | Err e | Ok t
type Functor f = {
    map : forall a b . (a -> b) -> f a -> f b
}

type OffsetString = { start : Int, end : Int, buffer : String }
type Position = Int
type Parser a =
        OffsetString -> { value : a }

let parser x : Parser a -> Parser a = x

let functor : Functor Parser = {
    map = \f m -> parser (\buffer ->
            let result = parser m buffer
            { value = f result.value })
}
()
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn make_writer_bug() {
    let _ = ::env_logger::try_init();

    let text = r#"

type Monoid a = {
    append : a -> a -> a,
    empty : a
}

type Applicative (f : Type -> Type) = {
    apply : forall a b . f (a -> b) -> f a -> f b,
    wrap : forall a . a -> f a
}

type Writer w a = { value : a, writer : w }

let make monoid : Monoid w -> () =
    let { append } = monoid
    #[infix(left, 1)]
    let (<>) = append

    let applicative : Applicative (Writer w) = {
        apply = \mf m -> { value = mf.value m.value, writer = mf.writer <> m.writer },
        wrap = \value -> { value, writer = monoid.empty },
    }
    ()

()
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn mutually_recursive_with_type_signature() {
    let _ = ::env_logger::try_init();

    let text = r#"
rec
let test x : a -> () = test2 x
let test2 x : a -> () = test x
()
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn show_list_bug() {
    let _ = ::env_logger::try_init();

    let text = r#"
type List a = | Nil | Cons a (List a)

type Show a = {
    show : a -> String,
}

let any x = any x

let show : Show a -> Show (List a) = \d ->
    #[infix(left, 1)]
    let (++) : String -> String -> String = any ()

    {
        show = \xs ->
            let show_elems ys =
                match ys with
                | Cons y ys2 ->
                    match ys2 with
                    | Cons z zs -> d.show y ++ ", " ++ show_elems ys2
                    | Nil -> d.show y
                | Nil -> ""

            "[" ++ show_elems xs ++ "]",
    }
()
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn show_list_bug_with_as_pattern() {
    let _ = ::env_logger::try_init();

    let text = r#"
type List a = | Nil | Cons a (List a)
type Show a = { show : a -> String }

let any x = any x
let string_show : Show String = { show = \_ -> "" }
let int_show : Show Int = { show = \_ -> "" }

let show : Show a -> Show (List a) = \d ->
    {
        show = \_ -> ""
    }
let list@{ } = { show }

list.show string_show
list.show int_show
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn generalize_record_unpacks() {
    let _ = ::env_logger::try_init();

    let text = r#"
type Semigroup a = {
    append : a -> a -> a
}

/// A linked list type
type List a = | Nil | Cons a (List a)

let semigroup : Semigroup (List a) =
    let append xs ys =
        match xs with
        | Cons x zs -> Cons x (append zs ys)
        | Nil -> ys

    { append }

let { append } = semigroup

append (Cons 1 Nil) Nil
append (Cons "" Nil) Nil
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
#[ignore]
fn generalize_tuple_unpacks() {
    let _ = ::env_logger::try_init();

    let text = r#"
type Semigroup a = (a -> a -> a, Int)

/// A linked list type
type List a = | Nil | Cons a (List a)

let semigroup : Semigroup (List a) =
    let append xs ys =
        match xs with
        | Cons x zs -> Cons x (append zs ys)
        | Nil -> ys

    (append, 0)

let (append, _) = semigroup

append (Cons 1 Nil) Nil
append (Cons "" Nil) Nil
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn dont_let_forall_escape() {
    let _ = ::env_logger::try_init();

    let text = r#"
let foo f: forall b. (forall a. a -> b) -> b = f ()
let id x: forall a. a -> a = x
let false: forall a. a = foo id // Oops
let some_int: Int = false
some_int // Undefined behaviour
"#;
    let (expr, result) = support::typecheck_expr(text);

    support::print_ident_types(&expr);
    assert!(result.is_err(), "{}", result.unwrap());
}

#[test]
fn unify_with_inferred_forall_in_record() {
    let _ = ::env_logger::try_init();

    let text = r#"
type Option a = | None | Some a

let f : forall a . () -> Option { x : Option a } = \x ->
    match () with
    | _ -> Some { x = None }
f
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn unify_with_inferred_forall_in_nested_call() {
    let _ = ::env_logger::try_init();

    let text = r#"
type Option a = | None | Some a

type Deserializer i a = i -> Option { value : a, input : i }

/// Deserializer which extracts the data from the `Value` type 
type ValueDeserializer a = Deserializer String a

let any x = any x

let deserializer : Deserializer i a -> Deserializer i a = any ()

type Functor f = {
    map : forall a b . (a -> b) -> f a -> f b
}

let functor : Functor (Deserializer i) = {
    map = \f m -> any ()
}

let option a : ValueDeserializer a -> ValueDeserializer (Option a) = \input ->
    match input with
    | "null" -> Some { value = None, input }
    | _ -> (functor.map Some a) input
()
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}

#[test]
fn forall_scope() {
    let _ = ::env_logger::try_init();

    let text = r#"
type Proxy h = | Proxy
let foo : (forall i . Proxy i -> ()) -> Proxy i -> () =
    \m p -> m p
()
"#;
    let result = support::typecheck(text);

    assert!(result.is_ok(), "{}", result.unwrap_err());
}
