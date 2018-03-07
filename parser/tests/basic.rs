#[macro_use]
extern crate collect_mac;
extern crate env_logger;
extern crate gluon_base as base;
extern crate gluon_parser as parser;
#[macro_use]
extern crate pretty_assertions;

#[macro_use]
mod support;

use base::ast::*;
use base::pos::{self, BytePos, Span, Spanned};
use base::types::{Field, Type};
use support::*;

#[test]
fn dangling_in() {
    let _ = ::env_logger::try_init();
    // Check that the lexer does not insert an extra `in`
    let text = r#"
let x = 1
in

let y = 2
y
"#;
    let e = parse_clear_span!(text);
    assert_eq!(e, let_("x", int(1), let_("y", int(2), id("y"))));
}

#[test]
fn expression() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("2 * 3 + 4");
    assert_eq!(e, binop(binop(int(2), "*", int(3)), "+", int(4)));
    let e = parse_clear_span!(r#"\x y -> x + y"#);
    assert_eq!(
        e,
        lambda(
            "",
            vec![intern("x"), intern("y")],
            binop(id("x"), "+", id("y")),
        )
    );
    let e = parse_clear_span!(r#"type Test = Int in 0"#);
    assert_eq!(e, type_decl(intern("Test"), vec![], typ("Int"), int(0)));
}

#[test]
fn application() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("let f = \\x y -> x + y in f 1 2");
    let a = let_(
        "f",
        lambda(
            "",
            vec![intern("x"), intern("y")],
            binop(id("x"), "+", id("y")),
        ),
        app(id("f"), vec![int(1), int(2)]),
    );
    assert_eq!(e, a);
}

#[test]
fn if_else_test() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("if True then 1 else 0");
    let a = if_else(id("True"), int(1), int(0));
    assert_eq!(e, a);
}

#[test]
fn let_type_decl() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("let f: Int = \\x y -> x + y in f 1 2");
    match e.value {
        Expr::LetBindings(bind, _) => assert_eq!(bind[0].typ, Some(typ("Int"))),
        _ => assert!(false),
    }
}

#[test]
fn let_args() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("let f x y = y in f 2");
    assert_eq!(
        e,
        let_a("f", &["x", "y"], id("y"), app(id("f"), vec![int(2)]))
    );
}

#[test]
fn type_decl_record() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("type Test = { x: Int, y: {} } in 1");
    let record = Type::record(
        Vec::new(),
        vec![
            Field::new(intern("x"), typ("Int")),
            Field::new(intern("y"), Type::record(vec![], vec![])),
        ],
    );
    assert_eq!(e, type_decl(intern("Test"), vec![], record, int(1)));
}

#[test]
fn type_mutually_recursive() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("type Test = | Test Int and Test2 = { x: Int, y: {} } in 1");
    let test = Type::variant(vec![
        Field::new(
            intern("Test"),
            Type::function(vec![typ("Int")], typ("Test")),
        ),
    ]);
    let test2 = Type::record(
        Vec::new(),
        vec![
            Field::new(intern("x"), typ("Int")),
            Field::new(intern("y"), Type::record(vec![], vec![])),
        ],
    );
    let binds = vec![
        TypeBinding {
            comment: None,
            name: no_loc(intern("Test")),
            alias: alias(intern("Test"), Vec::new(), test),
            finalized_alias: None,
        },
        TypeBinding {
            comment: None,
            name: no_loc(intern("Test2")),
            alias: alias(intern("Test2"), Vec::new(), test2),
            finalized_alias: None,
        },
    ];
    assert_eq!(e, type_decls(binds, int(1)));
}

#[test]
fn type_decl_projection() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("type Test = x.y.Z in 1");
    let record = Type::ident(intern("x.y.Z"));
    assert_eq!(e, type_decl(intern("Test"), vec![], record, int(1)));
}

#[test]
fn tuple_type() {
    let _ = ::env_logger::try_init();

    let expr = r#"
        let _: (Int, String, Option Int) = (1, "", None)
        1"#;
    parse_new!(expr);
}

#[test]
fn field_access_test() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("{ x = 1 }.x");
    assert_eq!(
        e,
        field_access(record(vec![(intern("x"), Some(int(1)))]), "x")
    );
}

#[test]
fn builtin_op() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("x #Int+ 1");
    assert_eq!(e, binop(id("x"), "#Int+", int(1)));
}

#[test]
fn op_identifier() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("let (==) = \\x y -> x #Int== y in (==) 1 2");
    assert_eq!(
        e,
        let_(
            "==",
            lambda(
                "",
                vec![intern("x"), intern("y")],
                binop(id("x"), "#Int==", id("y")),
            ),
            app(id("=="), vec![int(1), int(2)]),
        )
    );
}

#[test]
fn variant_type() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("type Option a = | None | Some a in Some 1");
    let option = Type::app(typ("Option"), collect![typ("a")]);
    let none = Type::function(vec![], option.clone());
    let some = Type::function(vec![typ("a")], option.clone());
    assert_eq!(
        e,
        type_decl(
            intern("Option"),
            vec![generic("a")],
            Type::variant(vec![
                Field::new(intern("None"), none),
                Field::new(intern("Some"), some),
            ]),
            app(id("Some"), vec![int(1)]),
        )
    );
}

#[test]
fn case_expr() {
    let _ = ::env_logger::try_init();
    let text = r#"
match None with
    | Some x -> x
    | None -> 0"#;
    let e = parse_clear_span!(text);
    assert_eq!(
        e,
        case(
            id("None"),
            vec![
                (
                    Pattern::Constructor(
                        TypedIdent::new(intern("Some")),
                        vec![no_loc(Pattern::Ident(TypedIdent::new(intern("x"))))],
                    ),
                    id("x"),
                ),
                (
                    Pattern::Constructor(TypedIdent::new(intern("None")), vec![]),
                    int(0),
                ),
            ],
        )
    );
}

#[test]
fn array_expr() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("[1, a]");
    assert_eq!(e, array(vec![int(1), id("a")]));
}

#[test]
fn operator_expr() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("test + 1 * 23 #Int- test");
    assert_eq!(
        e,
        binop(
            binop(id("test"), "+", binop(int(1), "*", int(23))),
            "#Int-",
            id("test"),
        )
    );
}

#[test]
fn record_trailing_comma() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("{ y, x = z,}");
    assert_eq!(
        e,
        record(vec![("y".into(), None), ("x".into(), Some(id("z")))])
    );
}

#[test]
fn array_trailing_comma() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("[y, 1, 2,]");
    assert_eq!(e, array(vec![id("y"), int(1), int(2)]));
}

#[test]
fn record_pattern() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("match x with | { y, x = z } -> z");
    let pattern = Pattern::Record {
        typ: Type::hole(),
        types: Vec::new(),
        fields: vec![
            PatternField {
                name: no_loc(intern("y")),
                value: None,
            },
            PatternField {
                name: no_loc(intern("x")),
                value: Some(no_loc(Pattern::Ident(TypedIdent::new(intern("z"))))),
            },
        ],
        implicit_import: None,
    };
    assert_eq!(e, case(id("x"), vec![(pattern, id("z"))]));
}

#[test]
fn let_pattern() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("let {x, y} = test in x");
    assert_eq!(
        e,
        no_loc(Expr::LetBindings(
            vec![
                ValueBinding {
                    comment: None,
                    name: no_loc(Pattern::Record {
                        typ: Type::hole(),
                        types: Vec::new(),
                        fields: vec![
                            PatternField {
                                name: no_loc(intern("x")),
                                value: None,
                            },
                            PatternField {
                                name: no_loc(intern("y")),
                                value: None,
                            },
                        ],
                        implicit_import: None,
                    }),
                    typ: None,
                    resolved_type: Type::hole(),
                    args: vec![],
                    expr: id("test"),
                },
            ],
            Box::new(id("x")),
        ),)
    );
}

#[test]
fn nested_pattern() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("match x with | { y = Some x } -> z");
    let nested = no_loc(Pattern::Constructor(
        TypedIdent::new(intern("Some")),
        vec![no_loc(Pattern::Ident(TypedIdent::new(intern("x"))))],
    ));
    let pattern = Pattern::Record {
        typ: Type::hole(),
        types: Vec::new(),
        fields: vec![
            PatternField {
                name: no_loc(intern("y")),
                value: Some(nested),
            },
        ],
        implicit_import: None,
    };
    assert_eq!(e, case(id("x"), vec![(pattern, id("z"))]));
}

#[test]
fn nested_pattern_parens() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("match x with | (Some (Some z)) -> z");

    let inner_pattern = no_loc(Pattern::Constructor(
        TypedIdent::new(intern("Some")),
        vec![no_loc(Pattern::Ident(TypedIdent::new(intern("z"))))],
    ));
    let pattern = Pattern::Constructor(TypedIdent::new(intern("Some")), vec![inner_pattern]);
    assert_eq!(e, case(id("x"), vec![(pattern, id("z"))]));
}

#[test]
fn span_identifier() {
    let _ = ::env_logger::try_init();

    let e = parse_new!("test");
    assert_eq!(e.span, Span::new(BytePos::from(0), BytePos::from(4)));
}

#[test]
fn span_integer() {
    let _ = ::env_logger::try_init();

    let e = parse_new!("1234");
    assert_eq!(e.span, Span::new(BytePos::from(0), BytePos::from(4)));
}

#[test]
fn span_string_literal() {
    let _ = ::env_logger::try_init();

    let e = parse_new!(r#" "test" "#);
    assert_eq!(e.span, Span::new(BytePos::from(1), BytePos::from(7)));
}

#[test]
fn span_app() {
    let _ = ::env_logger::try_init();

    let e = parse_new!(r#" f 123 "asd""#);
    assert_eq!(e.span, Span::new(BytePos::from(1), BytePos::from(12)));
}

#[test]
fn span_match() {
    let _ = ::env_logger::try_init();

    let e = parse_new!(
        r#"
match False with
    | True -> "asd"
    | False -> ""
"#
    );
    assert_eq!(e.span, Span::new(BytePos::from(1), BytePos::from(55)));
}

#[test]
fn span_if_else() {
    let _ = ::env_logger::try_init();

    let e = parse_new!(
        r#"
if True then
    1
else
    123.45
"#
    );
    assert_eq!(e.span, Span::new(BytePos::from(1), BytePos::from(35)));
}

#[test]
fn span_byte() {
    let _ = ::env_logger::try_init();

    let e = parse_new!(r#"124b"#);
    assert_eq!(e.span, Span::new(BytePos::from(0), BytePos::from(4)));
}

#[test]
fn span_field_access() {
    let _ = ::env_logger::try_init();
    let expr = parse_new!("record.x");
    assert_eq!(expr.span, Span::new(BytePos::from(0), BytePos::from(8)));
    match expr.value {
        Expr::Projection(ref e, _, _) => {
            assert_eq!(e.span, Span::new(BytePos::from(0), BytePos::from(6)));
        }
        _ => panic!(),
    }
}

#[test]
fn comment_on_let() {
    let _ = ::env_logger::try_init();
    let text = r#"
/// The identity function
let id x = x
id
"#;
    let e = parse_clear_span!(text);
    assert_eq!(
        e,
        no_loc(Expr::LetBindings(
            vec![
                ValueBinding {
                    comment: Some(Comment {
                        typ: CommentType::Line,
                        content: "The identity function".into(),
                    }),
                    name: no_loc(Pattern::Ident(TypedIdent::new(intern("id")))),
                    typ: None,
                    resolved_type: Type::hole(),
                    args: vec![Argument::explicit(no_loc(TypedIdent::new(intern("x"))))],
                    expr: id("x"),
                },
            ],
            Box::new(id("id")),
        ),)
    );
}

#[test]
fn comment_on_and() {
    let _ = ::env_logger::try_init();
    let text = r#"
let id x = x
/// The identity function
and id2 y = y
id
"#;
    let e = parse_clear_span!(text);
    assert_eq!(
        e,
        no_loc(Expr::LetBindings(
            vec![
                ValueBinding {
                    comment: None,
                    name: no_loc(Pattern::Ident(TypedIdent::new(intern("id")))),
                    typ: None,
                    resolved_type: Type::hole(),
                    args: vec![Argument::explicit(no_loc(TypedIdent::new(intern("x"))))],
                    expr: id("x"),
                },
                ValueBinding {
                    comment: Some(Comment {
                        typ: CommentType::Line,
                        content: "The identity function".into(),
                    }),
                    name: no_loc(Pattern::Ident(TypedIdent::new(intern("id2")))),
                    typ: None,
                    resolved_type: Type::hole(),
                    args: vec![Argument::explicit(no_loc(TypedIdent::new(intern("y"))))],
                    expr: id("y"),
                },
            ],
            Box::new(id("id")),
        ),)
    );
}

#[test]
fn comment_on_type() {
    let _ = ::env_logger::try_init();
    let text = r#"
/** Test type */
type Test = Int
id
"#;
    let e = parse_clear_span!(text);
    assert_eq!(
        e,
        type_decls(
            vec![
                TypeBinding {
                    comment: Some(Comment {
                        typ: CommentType::Block,
                        content: "Test type".into(),
                    }),
                    name: no_loc(intern("Test")),
                    alias: alias(intern("Test"), Vec::new(), typ("Int")),
                    finalized_alias: None,
                },
            ],
            id("id"),
        )
    );
}

#[test]
fn comment_after_integer() {
    let _ = ::env_logger::try_init();
    let text = r#"
let x = 1

/** Test type */
type Test = Int
id
"#;
    let e = parse_clear_span!(text);
    assert_eq!(
        e,
        let_a(
            "x",
            &[],
            int(1),
            type_decls(
                vec![
                    TypeBinding {
                        comment: Some(Comment {
                            typ: CommentType::Block,
                            content: "Test type".into(),
                        }),
                        name: no_loc(intern("Test")),
                        alias: alias(intern("Test"), Vec::new(), typ("Int")),
                        finalized_alias: None,
                    },
                ],
                id("id"),
            ),
        )
    );
}

#[test]
fn merge_line_comments() {
    let _ = ::env_logger::try_init();
    let text = r#"
/// Merge
/// consecutive
/// line comments.
type Test = Int
id
"#;
    let e = parse_clear_span!(text);
    assert_eq!(
        e,
        type_decls(
            vec![
                TypeBinding {
                    comment: Some(Comment {
                        typ: CommentType::Line,
                        content: "Merge\nconsecutive\nline comments.".into(),
                    }),
                    name: no_loc(intern("Test")),
                    alias: alias(intern("Test"), Vec::new(), typ("Int")),
                    finalized_alias: None,
                },
            ],
            id("id"),
        )
    );
}

#[test]
fn partial_field_access_simple() {
    let _ = ::env_logger::try_init();
    let text = r#"test."#;
    let e = parse(text);
    assert!(e.is_err());
    assert_eq!(
        clear_span(e.unwrap_err().0.unwrap()),
        Spanned {
            span: Span::new(BytePos::from(0), BytePos::from(0)),
            value: Expr::Projection(Box::new(id("test")), intern(""), Type::hole()),
        }
    );
}

#[test]
fn partial_field_access_in_block() {
    let _ = ::env_logger::try_init();
    let text = r#"
test.
test
"#;
    let e = parse(text);
    assert!(e.is_err());
    assert_eq!(
        clear_span(e.unwrap_err().0.unwrap()),
        Spanned {
            span: Span::default(),
            value: Expr::Block(vec![
                Spanned {
                    span: Span::new(BytePos::from(0), BytePos::from(0)),
                    value: Expr::Projection(Box::new(id("test")), intern(""), Type::hole()),
                },
                id("test"),
            ]),
        }
    );
}

#[test]
fn function_operator_application() {
    let _ = ::env_logger::try_init();
    let text = r#"
let x: ((->) Int Int) = x
x
"#;
    let e = parse_clear_span!(text);
    assert_eq!(
        e,
        no_loc(Expr::LetBindings(
            vec![
                ValueBinding {
                    comment: None,
                    name: no_loc(Pattern::Ident(TypedIdent::new(intern("x")))),
                    typ: Some(Type::app(typ("->"), collect![typ("Int"), typ("Int")])),
                    resolved_type: Type::hole(),
                    args: vec![],
                    expr: id("x"),
                },
            ],
            Box::new(id("x")),
        ),)
    );
}

#[test]
fn quote_in_identifier() {
    let _ = ::env_logger::try_init();
    let e = parse_clear_span!("let f' = \\x y -> x + y in f' 1 2");
    let a = let_(
        "f'",
        lambda(
            "",
            vec![intern("x"), intern("y")],
            binop(id("x"), "+", id("y")),
        ),
        app(id("f'"), vec![int(1), int(2)]),
    );
    assert_eq!(e, a);
}

// Test that this is `let x = 1 in {{ a; b }}` and not `{{ (let x = 1 in a) ; b }}`
#[test]
fn block_open_after_let_in() {
    let _ = ::env_logger::try_init();
    let text = r#"
        let x = 1
        a
        b
        "#;
    let e = parse_new!(text);
    match e.value {
        Expr::LetBindings(..) => (),
        _ => panic!("{:?}", e),
    }
}

#[test]
fn block_open_after_explicit_let_in() {
    let _ = ::env_logger::try_init();
    let text = r#"
        let x = 1
        in
        a
        b
        "#;
    let e = parse_new!(text);
    match e.value {
        Expr::LetBindings(..) => (),
        _ => panic!("{:?}", e),
    }
}

#[test]
fn record_type_field() {
    let _ = ::env_logger::try_init();
    let text = r"{ Test, x }";
    let e = parse_clear_span!(text);
    assert_eq!(
        e,
        record_a(vec![("Test".into(), None)], vec![("x".into(), None)])
    )
}

#[test]
fn parse_macro() {
    let _ = ::env_logger::try_init();
    let text = r#" import! "#;
    let e = parse_clear_span!(text);
    assert_eq!(e, id("import!"));
}

#[test]
fn doc_comment_on_record_field() {
    let _ = ::env_logger::try_init();
    let text = r"{ /** test*/ Test,
    /// x binding
    x = 1 }";
    let e = parse_clear_span!(text);
    assert_eq!(
        e,
        no_loc(Expr::Record {
            typ: Type::hole(),
            types: vec![
                ExprField {
                    comment: Some(Comment {
                        typ: CommentType::Block,
                        content: "test".into(),
                    }),
                    name: no_loc("Test".into()),
                    value: None,
                },
            ],
            exprs: vec![
                ExprField {
                    comment: Some(Comment {
                        typ: CommentType::Line,
                        content: "x binding".into(),
                    }),
                    name: no_loc("x".into()),
                    value: Some(int(1)),
                },
            ],
            base: None,
        })
    )
}

#[test]
fn shebang_at_top_is_ignored() {
    let _ = ::env_logger::try_init();
    let text = r"#!/bin/gluon
{ Test, x }";
    let e = parse_clear_span!(text);
    assert_eq!(
        e,
        record_a(vec![("Test".into(), None)], vec![("x".into(), None)])
    )
}

#[test]
fn do_in_parens() {
    let _ = ::env_logger::try_init();
    let text = r"
        scope_state (
            do _ = add_args
            eval_exprs
        )
    ";
    parse_clear_span!(text);
}

#[test]
fn parse_let_or_expr() {
    let _ = ::env_logger::try_init();

    let mut module = MockEnv::new();

    let line = "let x = test";
    match parser::parse_partial_let_or_expr(&mut module, line) {
        Ok(x) => assert_eq!(
            x,
            Err(ValueBinding {
                comment: None,
                name: pos::spanned2(
                    4.into(),
                    5.into(),
                    Pattern::Ident(TypedIdent::new(intern("x")))
                ),
                typ: None,
                resolved_type: Type::hole(),
                args: Vec::new(),
                expr: pos::spanned2(
                    8.into(),
                    12.into(),
                    Expr::Ident(TypedIdent::new(intern("test")))
                ),
            })
        ),
        Err((_, err)) => panic!("{}", err),
    }
}
