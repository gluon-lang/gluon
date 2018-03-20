#![allow(unused)]

use base::ast::{walk_mut_alias, walk_mut_ast_type, walk_mut_expr, walk_mut_pattern, Alternative,
                Argument, Array, AstType, DisplayEnv, Expr, ExprField, IdentEnv, Lambda, Literal,
                MutVisitor, Pattern, SpannedAlias, SpannedAstType, SpannedExpr, SpannedIdent,
                SpannedPattern, TypeBinding, TypedIdent, ValueBinding};
use base::error::Errors;
use base::pos::{self, BytePos, Span, Spanned};
use base::kind::Kind;
use base::types::{Alias, AliasData, ArcType, Field, Generic, Type};
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

/// MutVisitor that clears spans.
pub struct NoSpan;

impl<'a> MutVisitor<'a> for NoSpan {
    type Ident = String;

    fn visit_expr(&mut self, e: &mut SpannedExpr<Self::Ident>) {
        e.span = Span::default();
        walk_mut_expr(self, e);
    }

    fn visit_pattern(&mut self, p: &mut SpannedPattern<Self::Ident>) {
        p.span = Span::default();
        walk_mut_pattern(self, &mut p.value);
    }

    fn visit_spanned_typed_ident(&mut self, id: &mut SpannedIdent<Self::Ident>) {
        id.span = Span::default();
        self.visit_ident(&mut id.value)
    }

    fn visit_alias(&mut self, alias: &mut SpannedAlias<Self::Ident>) {
        alias.span = Span::default();
        walk_mut_alias(self, alias);
    }

    fn visit_spanned_ident(&mut self, s: &mut Spanned<Self::Ident, BytePos>) {
        s.span = Span::default();
    }

    fn visit_ast_type(&mut self, s: &mut SpannedAstType<Self::Ident>) {
        s.span = Span::default();
        walk_mut_ast_type(self, s);
    }
}

pub fn parse(
    input: &str,
) -> Result<SpannedExpr<String>, (Option<SpannedExpr<String>>, ParseErrors)> {
    parse_string(&mut MockEnv::new(), input)
}

/// Clears spans of the expression.
pub fn clear_span(mut expr: SpannedExpr<String>) -> SpannedExpr<String> {
    use support::NoSpan;
    NoSpan.visit_expr(&mut expr);
    expr
}

macro_rules! parse_new {
    ($input:expr) => {{
        // Replace windows line endings so that byte positions match up on multiline expressions
        let input = $input.replace("\r\n", "\n");
        parse(&input).unwrap_or_else(|(_, err)| panic!("{}", ::base::error::InFile::new("test", &input, err)))
    }}
}

macro_rules! parse_clear_span {
    ($input:expr) => {{
        clear_span(parse_new!($input))
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
    no_loc(Expr::Infix {
        lhs: Box::new(l),
        op: no_loc(TypedIdent::new(intern(s))),
        rhs: Box::new(r),
        implicit_args: Vec::new(),
    })
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
                    .map(|i| Argument::explicit(no_loc(TypedIdent::new(intern(i)))))
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
    no_loc(Expr::App {
        func: Box::new(e),
        implicit_args: Vec::new(),
        args,
    })
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
            .map(|(p, e)| Alternative {
                pattern: no_loc(p),
                expr: e,
            })
            .collect(),
    ))
}

pub fn lambda(name: &str, args: Vec<String>, body: SpExpr) -> SpExpr {
    no_loc(Expr::Lambda(Lambda {
        id: TypedIdent::new(intern(name)),
        args: args.into_iter()
            .map(|id| Argument::explicit(no_loc(TypedIdent::new(id))))
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
                alias: no_loc(AliasData::new(name, args, typ)),
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
            .map(|(name, value)| ExprField {
                comment: None,
                name: no_loc(name),
                value: value,
            })
            .collect(),
        exprs: fields
            .into_iter()
            .map(|(name, value)| ExprField {
                comment: None,
                name: no_loc(name),
                value: value,
            })
            .collect(),
        base: None,
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
    no_loc(Expr::Error(None))
}

pub fn alias<Id>(
    name: Id,
    args: Vec<Generic<Id>>,
    typ: AstType<Id>,
) -> Spanned<AliasData<Id, AstType<Id>>, BytePos> {
    no_loc(AliasData::new(name, args, typ))
}
