extern crate base;

use base::types::*;
use base::ast::ASTType;

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
                                    typ: Alias {
                                        name: "Test",
                                        args: vec![Generic {
                                                       kind: Kind::star(),
                                                       id: "a",
                                                   }],
                                        typ: Some(f.clone()),
                                    },
                                }],
                           vec![Field {
                                    name: "x",
                                    typ: Type::int(),
                                }]);
    assert_eq!(format!("{}", typ), "{ Test a = a -> String, x: Int }");
    let typ = Type::record(vec![Field {
                                    name: "Test",
                                    typ: Alias {
                                        name: "Test",
                                        args: vec![Generic {
                                                       kind: Kind::star(),
                                                       id: "a",
                                                   }],
                                        typ: Some(f.clone()),
                                    },
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
                                    typ: Alias {
                                        name: "Test",
                                        args: vec![Generic {
                                                       kind: Kind::star(),
                                                       id: "a",
                                                   }],
                                        typ: Some(f.clone()),
                                    },
                                }],
                           vec![]);
    assert_eq!(format!("{}", typ), "{ Test a = a -> String }");
}

#[test]
fn show_kind() {
    let two_args = Kind::function(Kind::star(), Kind::function(Kind::star(), Kind::star()));
    assert_eq!(format!("{}", two_args), "* -> * -> *");
    let function_arg = Kind::function(Kind::function(Kind::star(), Kind::star()), Kind::star());
    assert_eq!(format!("{}", function_arg), "(* -> *) -> *");
}
