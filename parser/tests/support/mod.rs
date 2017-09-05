#![allow(unused)]

use base::ast::{Alternative, Array, AstType, DisplayEnv, Expr, ExprField, IdentEnv, Lambda,
                Literal, Pattern, SpannedExpr, TypeBinding, TypedIdent, ValueBinding};
use base::error::Errors;
use base::pos::{self, BytePos, Span, Spanned};
use base::kind::Kind;
use base::types::{AliasData, ArcType, Field, Generic, Type};
use parser::{parse_string, Error, ParseErrors};
use std::marker::PhantomData;

pub struct MockEnv<T>(PhantomData<T>);

impl<T> MockEnv<T> {
    pub fn new() -> MockEnv<T> {
        MockEnv(PhantomData)
    }
}

impl<T: AsRef<str>> DisplayEnv for MockEnv<T> {
    type Ident = T;

    fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
        ident.as_ref()
    }
}

impl<T> IdentEnv for MockEnv<T>
where
    T: AsRef<str> + for<'a> From<&'a str>,
{
    fn from_str(&mut self, s: &str) -> Self::Ident {
        T::from(s)
    }
}

pub fn parse(
    input: &str,
) -> Result<SpannedExpr<String>, (Option<SpannedExpr<String>>, ParseErrors)> {
    parse_string(&mut MockEnv::new(), input)
}

macro_rules! parse_new {
    ($input:expr) => {{
        // Replace windows line endings so that byte positins match up on multiline expressions
        let input = $input.replace("\r\n", "\n");
        parse(&input).unwrap_or_else(|(_, err)| panic!("{}", err))
    }}
}

pub fn intern(s: &str) -> String {
    String::from(s)
}

pub type SpExpr = SpannedExpr<String>;

pub fn no_loc<T>(value: T) -> Spanned<T, BytePos> {
    pos::spanned(Span::default(), value)
}

pub fn binop(l: SpExpr, s: &str, r: SpExpr) -> SpExpr {
    no_loc(Expr::Infix(
        Box::new(l),
        no_loc(TypedIdent::new(intern(s))),
        Box::new(r),
    ))
}

pub fn int(i: i64) -> SpExpr {
    no_loc(Expr::Literal(Literal::Int(i)))
}

pub fn let_(s: &str, e: SpExpr, b: SpExpr) -> SpExpr {
    let_a(s, &[], e, b)
}

pub fn let_a(s: &str, args: &[&str], e: SpExpr, b: SpExpr) -> SpExpr {
    no_loc(Expr::LetBindings(
        vec![
            ValueBinding {
                comment: None,
                name: no_loc(Pattern::Ident(TypedIdent::new(intern(s)))),
                typ: None,
                resolved_type: Type::hole(),
                args: args.iter()
                    .map(|i| no_loc(TypedIdent::new(intern(i))))
                    .collect(),
                expr: e,
            },
        ],
        Box::new(b),
    ))
}

pub fn id(s: &str) -> SpExpr {
    no_loc(Expr::Ident(TypedIdent::new(intern(s))))
}

pub fn typ(s: &str) -> AstType<String> {
    assert!(s.len() != 0);
    match s.parse() {
        Ok(b) => Type::builtin(b),
        Err(()) if s.starts_with(char::is_lowercase) => generic_ty(s),
        Err(()) => Type::ident(intern(s)),
    }
}

pub fn generic_ty(s: &str) -> AstType<String> {
    Type::generic(generic(s))
}

pub fn generic(s: &str) -> Generic<String> {
    Generic::new(intern(s), Kind::hole())
}

pub fn app(e: SpExpr, args: Vec<SpExpr>) -> SpExpr {
    no_loc(Expr::App(Box::new(e), args))
}

pub fn if_else(p: SpExpr, if_true: SpExpr, if_false: SpExpr) -> SpExpr {
    no_loc(Expr::IfElse(
        Box::new(p),
        Box::new(if_true),
        Box::new(if_false),
    ))
}

pub fn case(e: SpExpr, alts: Vec<(Pattern<String>, SpExpr)>) -> SpExpr {
    no_loc(Expr::Match(
        Box::new(e),
        alts.into_iter()
            .map(|(p, e)| {
                Alternative {
                    pattern: no_loc(p),
                    expr: e,
                }
            })
            .collect(),
    ))
}

pub fn lambda(name: &str, args: Vec<String>, body: SpExpr) -> SpExpr {
    no_loc(Expr::Lambda(Lambda {
        id: TypedIdent::new(intern(name)),
        args: args.into_iter()
            .map(|id| no_loc(TypedIdent::new(id)))
            .collect(),
        body: Box::new(body),
    }))
}

pub fn type_decl(
    name: String,
    args: Vec<Generic<String>>,
    typ: AstType<String>,
    body: SpExpr,
) -> SpExpr {
    type_decls(
        vec![
            TypeBinding {
                comment: None,
                name: no_loc(name.clone()),
                alias: alias(name, args, typ),
                finalized_alias: None,
            },
        ],
        body,
    )
}

pub fn type_decls(binds: Vec<TypeBinding<String>>, body: SpExpr) -> SpExpr {
    no_loc(Expr::TypeBindings(binds, Box::new(body)))
}

pub fn record(fields: Vec<(String, Option<SpExpr>)>) -> SpExpr {
    record_a(Vec::new(), fields)
}

pub fn record_a(
    types: Vec<(String, Option<ArcType<String>>)>,
    fields: Vec<(String, Option<SpExpr>)>,
) -> SpExpr {
    no_loc(Expr::Record {
        typ: Type::hole(),
        types: types
            .into_iter()
            .map(|(name, value)| {
                ExprField {
                    comment: None,
                    name: no_loc(name),
                    value: value,
                }
            })
            .collect(),
        exprs: fields
            .into_iter()
            .map(|(name, value)| {
                ExprField {
                    comment: None,
                    name: no_loc(name),
                    value: value,
                }
            })
            .collect(),
    })
}

pub fn field_access(expr: SpExpr, field: &str) -> SpExpr {
    no_loc(Expr::Projection(
        Box::new(expr),
        intern(field),
        Type::hole(),
    ))
}

pub fn array(fields: Vec<SpExpr>) -> SpExpr {
    no_loc(Expr::Array(Array {
        typ: Type::hole(),
        exprs: fields,
    }))
}

pub fn error() -> SpExpr {
    no_loc(Expr::Error)
}

pub fn alias<Id>(
    name: Id,
    args: Vec<Generic<Id>>,
    typ: AstType<Id>,
) -> Spanned<AliasData<Id, AstType<Id>>, BytePos> {
    no_loc(AliasData::new(name, args, typ))
}
