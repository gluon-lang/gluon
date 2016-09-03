extern crate gluon_base as base;

use std::ops::Deref;

use base::types::*;
use base::ast::AstType;

fn type_con<I, T>(s: I, args: Vec<T>) -> Type<I, T>
    where I: Deref<Target = str>,
          T: From<Type<I, T>>,
{
    assert!(s.len() != 0);
    match s.parse() {
        Ok(b) => Type::Builtin(b),
        Err(()) if s.starts_with(char::is_lowercase) => {
            Type::Generic(Generic {
                kind: RcKind::new(Kind::Type),
                id: s,
            })
        }
        Err(()) => Type::App(Type::ident(s), args),
    }
}

#[test]
fn show_function() {
    let int: AstType<&str> = Type::int();
    let int_int = Type::function(vec![int.clone()], int.clone());
    assert_eq!(format!("{}", int_int), "Int -> Int");

    assert_eq!(format!("{}", Type::function(vec![int_int.clone()], int.clone())),
               "(Int -> Int) -> Int");

    assert_eq!(format!("{}", Type::function(vec![int.clone()], int_int.clone())),
               "Int -> Int -> Int");
}

fn some_record() -> RcType<&'static str> {
    let data = |s, a| RcType::from(type_con(s, a));
    let f = Type::function(vec![data("a", vec![])], Type::string());

    let test = data("Test", vec![data("a", vec![])]);
    Type::record(vec![Field {
                          name: "Test",
                          typ: Alias::new("Test",
                                          vec![Generic {
                                                   kind: Kind::typ(),
                                                   id: "a",
                                               }],
                                          f.clone()),
                      }],
                 vec![Field {
                          name: "x",
                          typ: Type::int(),
                      },
                      Field {
                          name: "test",
                          typ: test.clone(),
                      }])
}

#[test]
fn show_record() {
    assert_eq!(format!("{}", Type::<&str, AstType<&str>>::record(vec![], vec![])),
               "{}");
    let typ = Type::record(vec![],
                           vec![Field {
                                    name: "x",
                                    typ: Type::<&str, AstType<&str>>::int(),
                                }]);
    assert_eq!(format!("{}", typ), "{ x : Int }");

    let data = |s, a| RcType::from(type_con(s, a));
    let f = Type::function(vec![data("a", vec![])], Type::string());
    let typ = Type::record(vec![Field {
                                    name: "Test",
                                    typ: Alias::new("Test",
                                                    vec![Generic {
                                                             kind: Kind::typ(),
                                                             id: "a",
                                                         }],
                                                    f.clone()),
                                }],
                           vec![Field {
                                    name: "x",
                                    typ: Type::int(),
                                }]);
    assert_eq!(format!("{}", typ), "{ Test a = a -> String, x : Int }");
    assert_eq!(format!("{}", some_record()),
               "{ Test a = a -> String, x : Int, test : Test a }");
    let typ = Type::record(vec![Field {
                                    name: "Test",
                                    typ: Alias::new("Test",
                                                    vec![Generic {
                                                             kind: Kind::typ(),
                                                             id: "a",
                                                         }],
                                                    f.clone()),
                                }],
                           vec![]);
    assert_eq!(format!("{}", typ), "{ Test a = a -> String }");
}

#[test]
fn show_record_multi_line() {

    let data = |s, a| RcType::from(type_con(s, a));
    let f = Type::function(vec![data("a", vec![])], Type::string());
    let test = data("Test", vec![data("a", vec![])]);
    let typ = Type::record(vec![Field {
                                    name: "Test",
                                    typ: Alias::new("Test",
                                                    vec![Generic {
                                                             kind: Kind::typ(),
                                                             id: "a",
                                                         }],
                                                    f.clone()),
                                }],
                           vec![Field {
                                    name: "x",
                                    typ: Type::int(),
                                },
                                Field {
                                    name: "test",
                                    typ: Type::function(vec![data("Test",
                                                                  vec![Type::int(), f.clone()]),
                                                             Type::float(),
                                                             f.clone(),
                                                             f.clone()],
                                                        f.clone()),
                                },
                                Field {
                                    name: "record_looooooooooooooooooooooooooooooooooong",
                                    typ: some_record(),
                                },
                                Field {
                                    name: "looooooooooooooooooooooooooooooooooong_field",
                                    typ: test.clone(),
                                }]);
    let expected = r#"{
    Test a = a -> String,
    x : Int,
    test : Test Int (a -> String) ->
        Float ->
        (a -> String) ->
        (a -> String) ->
        a ->
        String,
    record_looooooooooooooooooooooooooooooooooong : {
        Test a = a -> String,
        x : Int,
        test : Test a
    },
    looooooooooooooooooooooooooooooooooong_field : Test a
}"#;

    assert_eq!(format!("{}", typ), expected);
}

#[test]
fn variants() {
    let typ: AstType<&str> =
        Type::variants(vec![("A", Type::function(vec![Type::int()], Type::ident("A"))),
                            ("B", Type::ident("A"))]);
    assert_eq!(format!("{}", typ), "| A Int | B");
}

#[test]
fn show_kind() {
    let two_args = Kind::function(Kind::typ(), Kind::function(Kind::typ(), Kind::typ()));
    assert_eq!(format!("{}", two_args), "Type -> Type -> Type");
    let function_arg = Kind::function(Kind::function(Kind::typ(), Kind::typ()), Kind::typ());
    assert_eq!(format!("{}", function_arg), "(Type -> Type) -> Type");
}
