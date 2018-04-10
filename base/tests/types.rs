extern crate gluon_base as base;
extern crate pretty;
#[macro_use]
extern crate pretty_assertions;

use std::ops::Deref;

use pretty::{Arena, DocAllocator};

use base::ast::{Expr, Literal, SpannedExpr, Typed, TypedIdent};
use base::kind::{ArcKind, Kind, KindEnv};
use base::types::*;
use base::symbol::{Symbol, SymbolRef};
use base::source::Source;
use base::pos::{self, BytePos, Span, Spanned};

fn type_con<I, T>(s: I, args: Vec<T>) -> Type<I, T>
where
    I: Deref<Target = str>,
    T: From<Type<I, T>>,
{
    assert!(s.len() != 0);
    match s.parse() {
        Ok(b) => Type::Builtin(b),
        Err(()) if s.starts_with(char::is_lowercase) => Type::Generic(Generic::new(s, Kind::typ())),
        Err(()) => Type::App(Type::ident(s), args.into_iter().collect()),
    }
}

macro_rules! assert_eq_display {
    ($l: expr, $r: expr) => {
        assert_eq!($l.to_string(), $r.to_string());
    }
}

#[test]
fn show_function() {
    let int: ArcType<&str> = Type::int();
    let int_int = Type::function(vec![int.clone()], int.clone());
    assert_eq_display!(format!("{}", int_int), "Int -> Int");

    assert_eq_display!(
        format!("{}", Type::function(vec![int_int.clone()], int.clone())),
        "(Int -> Int) -> Int"
    );

    assert_eq_display!(
        format!("{}", Type::function(vec![int.clone()], int_int.clone())),
        "Int -> Int -> Int"
    );
}

#[test]
fn show_forall() {
    let arg = |id| Generic::new(id, Kind::typ());
    let typ: ArcType<&str> = Type::forall(vec![arg("a"), arg("b")], Type::unit());

    assert_eq_display!(format!("{}", typ), "forall a b . ()");
}

#[test]
fn show_record_empty() {
    let record: ArcType<&str> = Type::record(vec![], vec![]);
    assert_eq_display!(format!("{}", record), "()");
}

#[test]
fn show_record_singleton() {
    let typ: ArcType<&str> = Type::record(vec![], vec![Field::new("x", Type::int())]);
    assert_eq_display!(format!("{}", typ), "{ x : Int }");
}

#[test]
fn show_record_singleton_polymorphic() {
    let data = |s, a| ArcType::from(type_con(s, a));
    let fun = Type::function(vec![data("a", vec![])], Type::string());
    let typ = Type::record(
        vec![
            Field::new(
                "Test",
                Alias::new(
                    "Test",
                    Type::forall(vec![Generic::new("a", Kind::typ())], fun.clone()),
                ),
            ),
        ],
        vec![],
    );
    assert_eq_display!(format!("{}", typ), "{ Test = forall a . a -> String }");
}

#[test]
fn show_record_multifield() {
    let data = |s, a| ArcType::from(type_con(s, a));
    let fun = Type::function(vec![data("a", vec![])], Type::string());
    let typ = Type::record(
        vec![
            Field::new(
                "Test",
                Alias::new(
                    "Test",
                    Type::forall(vec![Generic::new("a", Kind::typ())], fun.clone()),
                ),
            ),
        ],
        vec![Field::new("x", Type::int())],
    );
    assert_eq_display!(
        format!("{}", typ),
        "{ Test = forall a . a -> String, x : Int }"
    );
}
#[test]
fn show_record_multiline() {
    let data = |s, a| ArcType::from(type_con(s, a));
    let fun = Type::function(vec![data("a", vec![])], Type::string());
    let test = data("Test", vec![data("a", vec![])]);
    let record = Type::record(
        vec![
            Field::new(
                "Test",
                Alias::new(
                    "Test",
                    Type::forall(vec![Generic::new("a", Kind::typ())], fun.clone()),
                ),
            ),
        ],
        vec![
            Field::new("x", Type::int()),
            Field::new("test", test.clone()),
            Field::new(
                "+",
                Type::function(vec![Type::int(), Type::int()], Type::int()),
            ),
        ],
    );

    assert_eq_display!(
        format!("{}", record),
        r#"{
    Test = forall a . a -> String,
    x : Int,
    test : Test a,
    (+) : Int -> Int -> Int
}"#
    );
}

#[test]
fn show_record_filtered() {
    let data = |s, a| ArcType::from(type_con(s, a));
    let test = data("Test", vec![data("a", vec![])]);
    let record = Type::record(
        vec![Field::new("Test", Alias::new("Test", Type::int()))],
        vec![
            Field::new("x", Type::int()),
            Field::new("y", Type::int()),
            Field::new("test", test.clone()),
            Field::new(
                "+",
                Type::function(vec![Type::int(), Type::int()], Type::int()),
            ),
        ],
    );

    assert_eq_display!(
        format!(
            "{}",
            TypeFormatter::new(&record).filter(&|field| (*field == "Test").into())
        ),
        r#"{ ..., Test = Int, ... }"#
    );

    assert_eq_display!(
        format!(
            "{}",
            TypeFormatter::new(&record).filter(&|field| (*field != "x").into())
        ),
        r#"{ ..., Test = Int, y : Int, test : Test a, (+) : Int -> Int -> Int, ... }"#
    );
    assert_eq_display!(
        format!(
            "{}",
            TypeFormatter::new(&record)
                .filter(&|field| (*field != "x").into())
                .width(50)
        ),
        r#"{
    ...,
    Test = Int,
    y : Int,
    test : Test a,
    (+) : Int -> Int -> Int,
    ...
}"#
    );
}

#[test]
fn show_record_multi_line_nested() {
    let data = |s, a| ArcType::from(type_con(s, a));
    let fun = Type::function(vec![data("a", vec![])], Type::string());
    let test = data("Test", vec![data("a", vec![])]);
    let inner_record = Type::record(
        vec![
            Field::new(
                "Test",
                Alias::new(
                    "Test",
                    Type::forall(vec![Generic::new("a", Kind::typ())], fun.clone()),
                ),
            ),
        ],
        vec![
            Field::new("x", Type::int()),
            Field::new("test", test.clone()),
            Field::new(
                "+",
                Type::function(vec![Type::int(), Type::int()], Type::int()),
            ),
        ],
    );
    let record = Type::record(
        vec![
            Field::new(
                "Test",
                Alias::new(
                    "Test",
                    Type::forall(vec![Generic::new("a", Kind::typ())], fun.clone()),
                ),
            ),
        ],
        vec![
            Field::new("x", Type::int()),
            Field::new(
                "test",
                Type::function(
                    vec![
                        data("Test", vec![Type::int(), fun.clone()]),
                        Type::float(),
                        fun.clone(),
                        fun.clone(),
                    ],
                    fun.clone(),
                ),
            ),
            Field::new(
                "record_looooooooooooooooooooooooooooooooooong",
                inner_record,
            ),
            Field::new("looooooooooooooooooooooooooooooooooong_field", test.clone()),
        ],
    );
    let expected = r#"{
    Test = forall a . a -> String,
    x : Int,
    test : Test Int (a -> String)
            -> Float
            -> (a -> String)
            -> (a -> String)
            -> a
            -> String,
    record_looooooooooooooooooooooooooooooooooong : {
        Test = forall a . a -> String,
        x : Int,
        test : Test a,
        (+) : Int -> Int -> Int
    },
    looooooooooooooooooooooooooooooooooong_field : Test a
}"#;

    assert_eq_display!(format!("{}", record), expected);
}

#[test]
fn show_variant() {
    let typ: ArcType<&str> = Type::variant(vec![
        Field::new("A", Type::function(vec![Type::int()], Type::ident("A"))),
        Field::new("B", Type::ident("A")),
    ]);
    assert_eq_display!(format!("{}", typ), "| A Int | B");
}

#[test]
fn show_kind() {
    let two_args = Kind::function(Kind::typ(), Kind::function(Kind::typ(), Kind::typ()));
    assert_eq_display!(format!("{}", two_args), "Type -> Type -> Type");
    let function_arg = Kind::function(Kind::function(Kind::typ(), Kind::typ()), Kind::typ());
    assert_eq_display!(format!("{}", function_arg), "(Type -> Type) -> Type");
}

#[test]
fn show_polymorphic_record() {
    let fields = vec![Field::new("x", Type::string())];
    let typ: ArcType<&str> = Type::poly_record(vec![], fields, Type::ident("r"));
    assert_eq_display!(format!("{}", typ), "{ x : String | r }");
}

#[test]
fn show_polymorphic_record_associated_type() {
    let type_fields = vec![
        Field::new(
            "Test",
            Alias::new(
                "Test",
                Type::forall(vec![Generic::new("a", Kind::typ())], Type::ident("a")),
            ),
        ),
    ];
    let typ: ArcType<&str> = Type::poly_record(type_fields, vec![], Type::ident("r"));
    assert_eq_display!(format!("{}", typ), "{ Test = forall a . a | r }");
}

#[test]
fn break_record() {
    let data = |s, a| ArcType::from(type_con(s, a));

    let test = data("Test", vec![data("a", vec![])]);
    let typ: ArcType<&str> = Type::record(
        vec![],
        vec![
            Field::new("x", Type::int()),
            Field::new("test", test.clone()),
            Field::new(
                "+",
                Type::function(vec![Type::int(), Type::int()], Type::int()),
            ),
        ],
    );
    let arena = Arena::new();
    let source = Source::new("");
    let printer = pretty_print::Printer::new(&arena, &source);
    let typ = arena
        .text("aaaaaaaaabbbbbbbbbbcccccccccc ")
        .append(pretty_print(&printer, &typ))
        .append(arena.newline());
    assert_eq_display!(
        format!("{}", typ.1.pretty(80)),
        r#"aaaaaaaaabbbbbbbbbbcccccccccc {
    x : Int,
    test : Test a,
    (+) : Int -> Int -> Int
}
"#
    );
}

pub struct MockEnv;

impl KindEnv for MockEnv {
    fn find_kind(&self, _id: &SymbolRef) -> Option<ArcKind> {
        None
    }
}

impl TypeEnv for MockEnv {
    fn find_type(&self, _id: &SymbolRef) -> Option<&ArcType> {
        None
    }

    fn find_type_info(&self, _id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>> {
        None
    }
}

pub type SpExpr = SpannedExpr<Symbol>;

pub fn intern(s: &str) -> Symbol {
    Symbol::from(s)
}

pub fn no_loc<T>(value: T) -> Spanned<T, BytePos> {
    pos::spanned(Span::default(), value)
}

pub fn int(i: i64) -> SpExpr {
    no_loc(Expr::Literal(Literal::Int(i)))
}

pub fn binop(l: SpExpr, s: &str, r: SpExpr) -> SpExpr {
    no_loc(Expr::Infix {
        lhs: Box::new(l),
        op: no_loc(TypedIdent::new(intern(s))),
        rhs: Box::new(r),
        implicit_args: Vec::new(),
    })
}

#[test]
fn take_implicits_into_account_on_infix_type() {
    let mut expr = binop(int(1), "+", int(2));
    if let Expr::Infix { ref mut op, .. } = expr.value {
        op.value.typ = Type::function_implicit(
            vec![Type::int()],
            Type::function(vec![Type::int(), Type::int()], Type::int()),
        );
    }

    assert_eq!(expr.env_type_of(&MockEnv), Type::int());
}
