extern crate base;

use std::ops::Deref;

use base::types::*;
use base::ast::ASTType;

fn type_con<I, T>(s: I, args: Vec<T>) -> Type<I, T>
    where I: Deref<Target = str>,
          T: From<Type<I, T>>
{
    assert!(s.len() != 0);
    let is_var = s.chars().next().unwrap().is_lowercase();
    match s.parse() {
        Ok(b) => Type::Builtin(b),
        Err(()) if is_var => {
            Type::Generic(Generic {
                kind: RcKind::new(Kind::Star),
                id: s,
            })
        }
        Err(()) => Type::Data(Type::id(s), args),
    }
}

#[test]
fn show_function() {
    let int: ASTType<&str> = Type::int();
    let int_int = Type::function(vec![int.clone()], int.clone());
    assert_eq!(format!("{}", int_int),
               "Int -> Int");

    assert_eq!(format!("{}", Type::function(vec![int_int.clone()], int.clone())),
               "(Int -> Int) -> Int");

    assert_eq!(format!("{}", Type::function(vec![int.clone()], int_int.clone())),
               "Int -> Int -> Int");
}

#[test]
fn show_record() {
    assert_eq!(format!("{}", Type::<&str, ASTType<&str>>::record(vec![], vec![])),
               "{}");
    let typ = Type::record(vec![],
                           vec![Field {
                                    name: "x",
                                    typ: Type::<&str, ASTType<&str>>::int(),
                                }]);
    assert_eq!(format!("{}", typ), "{ x: Int }");

    let data = |s, a| RcType::from(type_con(s, a));
    let f = Type::function(vec![data("a", vec![])], Type::string());
    let test = data("Test", vec![data("a", vec![])]);
    let typ = Type::record(vec![Field {
                                    name: "Test",
                                    typ: Alias::new(
                                        "Test",
                                        vec![Generic {
                                                       kind: Kind::star(),
                                                       id: "a",
                                                   }],
                                        f.clone(),
                                    ),
                                }],
                           vec![Field {
                                    name: "x",
                                    typ: Type::int(),
                                }]);
    assert_eq!(format!("{}", typ), "{ Test a = a -> String, x: Int }");
    let typ = Type::record(vec![Field {
                                    name: "Test",
                                    typ: Alias::new(
                                        "Test",
                                        vec![Generic {
                                                       kind: Kind::star(),
                                                       id: "a",
                                                   }],
                                        f.clone(),
                                    ),
                                }],
                           vec![Field {
                                    name: "x",
                                    typ: Type::int(),
                                },
                                Field {
                                    name: "test",
                                    typ: test.clone(),
                                }]);
    assert_eq!(format!("{}", typ),
               "{ Test a = a -> String, x: Int, test: Test a }");
    let typ = Type::record(vec![Field {
                                    name: "Test",
                                    typ: Alias::new(
                                        "Test",
                                        vec![Generic {
                                                       kind: Kind::star(),
                                                       id: "a",
                                                   }],
                                        f.clone(),
                                    ),
                                }],
                           vec![]);
    assert_eq!(format!("{}", typ), "{ Test a = a -> String }");
}

#[test]
fn variants() {
    let typ: ASTType<&str> = Type::variants(vec![("A", Type::function(vec![Type::int()], Type::id("A"))),
                                                 ("B", Type::id("A"))]);
    assert_eq!(format!("{}", typ), "| A Int | B");
}

#[test]
fn show_kind() {
    let two_args = Kind::function(Kind::star(), Kind::function(Kind::star(), Kind::star()));
    assert_eq!(format!("{}", two_args), "* -> * -> *");
    let function_arg = Kind::function(Kind::function(Kind::star(), Kind::star()), Kind::star());
    assert_eq!(format!("{}", function_arg), "(* -> *) -> *");
}
