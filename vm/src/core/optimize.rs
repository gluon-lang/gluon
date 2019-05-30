use std::marker::PhantomData;

use crate::base::{
    ast::TypedIdent,
    merge::{merge_fn, merge_iter},
    pos,
    symbol::Symbol,
    types::{ArcType, Field, TypeExt},
};

use crate::core::{Allocator, Alternative, CExpr, Closure, Expr, LetBinding, Named, Pattern};

pub trait ExprProducer<'a, 'b>: Visitor<'a, 'b> {
    fn new(allocator: &'a Allocator<'a>) -> Self;
    fn produce(&mut self, expr: CExpr<'b>) -> CExpr<'a>;
}

pub struct SameLifetime<'a>(&'a Allocator<'a>);
impl<'a> ExprProducer<'a, 'a> for SameLifetime<'a> {
    fn new(allocator: &'a Allocator<'a>) -> Self {
        SameLifetime(allocator)
    }
    fn produce(&mut self, expr: CExpr<'a>) -> CExpr<'a> {
        expr
    }
}

impl<'a> Visitor<'a, 'a> for SameLifetime<'a> {
    type Producer = SameLifetime<'a>;

    fn visit_expr(&mut self, expr: &'a Expr<'a>) -> Option<&'a Expr<'a>> {
        Some(self.produce(expr))
    }
    fn detach_allocator(&self) -> Option<&'a Allocator<'a>> {
        Some(self.0)
    }
}

pub struct DifferentLifetime<'a, 'b>(&'a Allocator<'a>, PhantomData<&'b ()>);

impl<'a, 'b> ExprProducer<'a, 'b> for DifferentLifetime<'a, 'b> {
    fn new(allocator: &'a Allocator<'a>) -> Self {
        DifferentLifetime(allocator, PhantomData)
    }
    fn produce(&mut self, expr: CExpr<'b>) -> CExpr<'a> {
        match *expr {
            Expr::Const(ref id, ref span) => {
                self.0.arena.alloc(Expr::Const(id.clone(), span.clone()))
            }
            Expr::Ident(ref id, ref span) => {
                self.0.arena.alloc(Expr::Ident(id.clone(), span.clone()))
            }
            Expr::Data(ref id, args, pos) if args.is_empty() => {
                self.0.arena.alloc(Expr::Data(id.clone(), &[], pos.clone()))
            }
            _ => walk_expr_alloc(self, expr).unwrap(),
        }
    }
}

impl<'a, 'b> Visitor<'a, 'b> for DifferentLifetime<'a, 'b> {
    type Producer = DifferentLifetime<'a, 'b>;

    fn visit_expr(&mut self, expr: &'b Expr<'b>) -> Option<&'a Expr<'a>> {
        Some(self.produce(expr))
    }

    fn detach_allocator(&self) -> Option<&'a Allocator<'a>> {
        Some(self.0)
    }
}

pub trait Visitor<'a, 'b> {
    type Producer: ExprProducer<'a, 'b>;

    fn visit_expr(&mut self, expr: CExpr<'b>) -> Option<&'a Expr<'a>>;
    fn visit_expr_(&mut self, expr: CExpr<'b>) -> Option<Expr<'a>> {
        self.visit_expr(expr).map(Clone::clone)
    }
    fn detach_allocator(&self) -> Option<&'a Allocator<'a>>;
    fn allocator(&self) -> &'a Allocator<'a> {
        self.detach_allocator().expect("Allocator")
    }
}

struct RecognizeUnnecessaryAllocation<'a> {
    allocator: &'a Allocator<'a>,
}

impl<'a> Visitor<'a, 'a> for RecognizeUnnecessaryAllocation<'a> {
    type Producer = SameLifetime<'a>;

    fn visit_expr(&mut self, expr: &'a Expr<'a>) -> Option<&'a Expr<'a>> {
        fn make_let<'b>(
            self_: &mut RecognizeUnnecessaryAllocation<'b>,
            fields: &[(TypedIdent<Symbol>, Option<Symbol>)],
            next_expr: &'b Expr<'b>,
            field: &Field<Symbol, ArcType>,
            expr: &'b Expr<'b>,
        ) -> &'b Expr<'b> {
            let pattern_field = fields
                .iter()
                .find(|f| f.0.name.name_eq(&field.name))
                .map(|pattern_field| {
                    pattern_field
                        .1
                        .as_ref()
                        .unwrap_or(&pattern_field.0.name)
                        .clone()
                })
                .unwrap_or_else(|| Symbol::from("dummy"));
            let new_expr = Expr::Let(
                self_.allocator.let_binding_arena.alloc(LetBinding {
                    name: TypedIdent {
                        name: pattern_field.clone(),
                        typ: field.typ.clone(),
                    },
                    expr: Named::Expr(expr),
                    span_start: pos::BytePos::default(),
                }),
                next_expr,
            );
            &*self_.allocator().arena.alloc(new_expr)
        }
        // Avoids boxing data which are destructured immediately after creation
        // match { l, r } with
        // | { l, r } -> ...
        //
        // to
        //
        // let l = x
        // let l = y
        // ...
        match *expr {
            Expr::Match(&Expr::Data(ref id, exprs, ..), alts) if alts.len() == 1 => {
                match alts[0].pattern {
                    Pattern::Record(ref fields) => {
                        debug_assert!(id.typ.row_iter().len() >= fields.len());
                        let next_expr = alts[0].expr;
                        Some(
                            id.typ
                                .row_iter()
                                .zip(exprs)
                                .collect::<Vec<_>>()
                                .into_iter()
                                .rev()
                                .fold(next_expr, |next_expr, (field, expr)| {
                                    make_let(self, fields, next_expr, field, expr)
                                }),
                        )
                    }
                    _ => walk_expr_alloc(self, expr),
                }
            }
            _ => walk_expr_alloc(self, expr),
        }
    }

    fn detach_allocator(&self) -> Option<&'a Allocator<'a>> {
        Some(self.allocator)
    }
}

pub fn optimize<'a>(allocator: &'a Allocator<'a>, expr: &'a Expr<'a>) -> &'a Expr<'a> {
    let mut optimizer = RecognizeUnnecessaryAllocation {
        allocator: allocator,
    };
    optimizer.visit_expr(expr).unwrap_or(expr)
}

pub fn walk_expr_alloc<'a, 'b, V>(visitor: &mut V, expr: CExpr<'b>) -> Option<CExpr<'a>>
where
    V: ?Sized + Visitor<'a, 'b>,
{
    walk_expr(visitor, expr).map(|expr| &*visitor.allocator().arena.alloc(expr))
}

pub fn walk_expr<'a, 'b, V>(visitor: &mut V, expr: CExpr<'b>) -> Option<Expr<'a>>
where
    V: ?Sized + Visitor<'a, 'b>,
{
    let allocator = visitor.detach_allocator();
    match *expr {
        Expr::Call(f, args) => {
            let new_f = visitor.visit_expr(f);
            let new_args = merge_iter(
                args,
                |expr| visitor.visit_expr_(expr),
                |e| {
                    V::Producer::new(allocator.expect("Allocator"))
                        .produce(e)
                        .clone()
                },
            )
            .map(|exprs: Vec<_>| &*visitor.allocator().arena.alloc_extend(exprs.into_iter()));

            merge_fn(
                &f,
                |e| V::Producer::new(visitor.allocator()).produce(e),
                new_f,
                &args,
                |a| {
                    let a = a
                        .iter()
                        .map(|a| V::Producer::new(visitor.allocator()).produce(a).clone())
                        .collect::<Vec<_>>();
                    visitor.allocator().arena.alloc_extend(a)
                },
                new_args,
                Expr::Call,
            )
        }
        Expr::Const(_, _) => None,
        Expr::Ident(_, _) => None,
        Expr::Data(ref id, exprs, pos) => merge_iter(
            exprs,
            |expr| visitor.visit_expr_(expr),
            |e| {
                V::Producer::new(allocator.expect("Allocator"))
                    .produce(e)
                    .clone()
            },
        )
        .map(|exprs: Vec<_>| {
            Expr::Data(
                id.clone(),
                visitor.allocator().arena.alloc_extend(exprs.into_iter()),
                pos,
            )
        }),
        Expr::Let(ref bind, expr) => {
            let new_bind = walk_bind(visitor, bind);
            let new_expr = visitor.visit_expr(expr);
            merge_fn(
                bind,
                |bind| walk_bind(&mut V::Producer::new(visitor.allocator()), bind).unwrap(),
                new_bind,
                &expr,
                |e| V::Producer::new(visitor.allocator()).produce(e),
                new_expr,
                Expr::Let,
            )
        }
        Expr::Match(expr, alts) => {
            let new_expr = visitor.visit_expr(expr);
            let new_alts = merge_iter(
                alts,
                |expr| walk_alt(visitor, expr),
                |alt| {
                    walk_alt(&mut V::Producer::new(allocator.expect("Allocator")), alt)
                        .expect("alt")
                },
            )
            .map(|alts: Vec<_>| {
                &*visitor
                    .allocator()
                    .alternative_arena
                    .alloc_extend(alts.into_iter())
            });
            merge_fn(
                &expr,
                |e| V::Producer::new(visitor.allocator()).produce(e),
                new_expr,
                &alts,
                |a| {
                    let a = a
                        .iter()
                        .map(|a| Alternative {
                            pattern: a.pattern.clone(),
                            expr: V::Producer::new(visitor.allocator()).produce(a.expr),
                        })
                        .collect::<Vec<_>>();
                    visitor.allocator().alternative_arena.alloc_extend(a)
                },
                new_alts,
                Expr::Match,
            )
        }
    }
}

fn walk_bind<'a, 'b, V>(visitor: &mut V, bind: &LetBinding<'b>) -> Option<&'a LetBinding<'a>>
where
    V: ?Sized + Visitor<'a, 'b>,
{
    let allocator = visitor.detach_allocator();
    let new_named = match bind.expr {
        Named::Recursive(ref closures) => merge_iter(
            closures,
            |closure| {
                visitor.visit_expr(closure.expr).map(|new_expr| Closure {
                    pos: closure.pos,
                    name: closure.name.clone(),
                    args: closure.args.clone(),
                    expr: new_expr,
                })
            },
            |closure| Closure {
                pos: closure.pos,
                name: closure.name.clone(),
                args: closure.args.clone(),
                expr: V::Producer::new(allocator.expect("Allocator")).produce(closure.expr),
            },
        )
        .map(Named::Recursive),
        Named::Expr(bind_expr) => visitor.visit_expr(bind_expr).map(Named::Expr),
    };
    new_named.map(|named| {
        &*allocator
            .expect("Allocator")
            .let_binding_arena
            .alloc(LetBinding {
                name: bind.name.clone(),
                expr: named,
                span_start: bind.span_start,
            })
    })
}

fn walk_alt<'a, 'b, V>(visitor: &mut V, alt: &'b Alternative<'b>) -> Option<Alternative<'a>>
where
    V: ?Sized + Visitor<'a, 'b>,
{
    let new_expr = visitor.visit_expr(alt.expr);
    new_expr.map(|expr| Alternative {
        pattern: alt.pattern.clone(),
        expr: expr,
    })
}

#[cfg(all(test, feature = "test"))]
pub(crate) mod tests {
    use super::*;

    use base::symbol::Symbols;

    use crate::core::{self, grammar::ExprParser, tests::PatternEq};

    pub(crate) fn check_optimization(
        initial_str: &str,
        expected_str: &str,
        optimize: impl for<'a> FnOnce(&'a Allocator<'a>, CExpr<'a>) -> CExpr<'a>,
    ) {
        let mut symbols = Symbols::new();
        let allocator = core::Allocator::new();

        let initial_expr = allocator.arena.alloc(
            ExprParser::new()
                .parse(&mut symbols, &allocator, initial_str)
                .unwrap(),
        );

        let optimized_expr = optimize(&allocator, initial_expr);

        let expected_expr = ExprParser::new()
            .parse(&mut symbols, &allocator, expected_str)
            .unwrap();
        assert_deq!(PatternEq(optimized_expr), expected_expr);
    }

    #[test]
    fn unnecessary_allocation() {
        let initial_str = r#"
            match { l, r } with
            | { l, r } -> l
            end
            "#;
        let expected_str = r#"
            let l = l
            in
            let r = r
            in
            l
            "#;
        check_optimization(initial_str, expected_str, optimize);
    }
}
