use base::merge::{merge, merge_iter};

use core::{Allocator, Alternative, Closure, Expr, Named, LetBinding};

pub trait Visitor<'a> {
    fn visit_expr(&mut self, &'a Expr<'a>) -> Option<&'a Expr<'a>>;
    fn allocator<'e>(&self) -> &'a Allocator<'a, 'e>;
}

pub fn optimize<'a, 'e, V>(visitor: &mut V, expr: &'a Expr<'a>) -> &'a Expr<'a>
    where V: ?Sized + Visitor<'a>,
{
    visitor.visit_expr(expr).unwrap_or(expr)
}

pub fn walk_expr_alloc<'a, V>(visitor: &mut V, expr: &'a Expr<'a>) -> Option<&'a Expr<'a>>
    where V: ?Sized + Visitor<'a>,
{
    walk_expr(visitor, expr).map(|expr| &*visitor.allocator().arena.alloc(expr))
}

pub fn walk_expr<'a, V>(visitor: &mut V, expr: &'a Expr<'a>) -> Option<Expr<'a>>
    where V: ?Sized + Visitor<'a>,
{
    match *expr {
        Expr::Call(f, args) => {
            let new_f = walk_expr_alloc(visitor, f);
            let new_args = merge_iter(args, |expr| walk_expr(visitor, expr), Expr::clone)
                .map(|exprs: Vec<_>| {
                    &*visitor.allocator()
                        .arena
                        .alloc_extend(exprs.into_iter())
                });

            merge(&f, new_f, &args, new_args, Expr::Call)
        }
        Expr::Const(_, _) => None,
        Expr::Data(ref id, exprs, pos, expansion) => {
            merge_iter(exprs, |expr| walk_expr(visitor, expr), Expr::clone)
                .map(|exprs: Vec<_>| {
                    Expr::Data(id.clone(),
                               visitor.allocator()
                                   .arena
                                   .alloc_extend(exprs.into_iter()),
                               pos,
                               expansion)
                })
        }
        Expr::Ident(_, _) => None,
        Expr::Let(ref bind, expr) => {
            let new_named = match bind.expr {
                Named::Recursive(ref closures) => {
                    merge_iter(closures,
                               |closure| {
                        walk_expr_alloc(visitor, closure.expr).map(|new_expr| {
                            Closure {
                                name: closure.name.clone(),
                                args: closure.args.clone(),
                                expr: new_expr,
                            }
                        })
                    },
                               Closure::clone)
                        .map(Named::Recursive)
                }
                Named::Expr(bind_expr) => walk_expr_alloc(visitor, bind_expr).map(Named::Expr),
            };
            let new_bind = new_named.map(|named| {
                LetBinding {
                    name: bind.name.clone(),
                    expr: named,
                    span_start: bind.span_start,
                }
            });
            let new_expr = walk_expr_alloc(visitor, expr);
            merge(bind, new_bind, &expr, new_expr, Expr::Let)
        }
        Expr::Match(expr, alts) => {
            let new_expr = walk_expr_alloc(visitor, expr);
            let new_alts = merge_iter(alts, |expr| walk_alt(visitor, expr), Alternative::clone)
                .map(|alts: Vec<_>| {
                    &*visitor.allocator()
                        .alternative_arena
                        .alloc_extend(alts.into_iter())
                });
            merge(&expr, new_expr, &alts, new_alts, Expr::Match)
        }
    }
}

fn walk_alt<'a, V>(visitor: &mut V, alt: &'a Alternative<'a>) -> Option<Alternative<'a>>
    where V: ?Sized + Visitor<'a>,
{
    let new_expr = walk_expr_alloc(visitor, alt.expr);
    new_expr.map(|expr| {
        Alternative {
            pattern: alt.pattern.clone(),
            expr: expr,
        }
    })
}
