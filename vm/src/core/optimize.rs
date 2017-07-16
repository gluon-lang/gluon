use base::ast::TypedIdent;
use base::merge::{merge, merge_iter};
use base::pos;

use core::{Allocator, Alternative, Closure, Expr, Named, LetBinding, Pattern};

pub trait Visitor<'a> {
    fn visit_expr(&mut self, expr: &'a Expr<'a>) -> Option<&'a Expr<'a>>;
    fn allocator(&self) -> &'a Allocator<'a>;
}

struct RecognizeUnnecessaryAllocation<'a> {
    allocator: &'a Allocator<'a>,
}

impl<'a> Visitor<'a> for RecognizeUnnecessaryAllocation<'a> {
    fn visit_expr(&mut self, expr: &'a Expr<'a>) -> Option<&'a Expr<'a>> {
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
                                    let pattern_field = fields
                                        .iter()
                                        .find(|f| f.0.name.name_eq(&field.name))
                                        .unwrap();
                                    let pattern_field =
                                        pattern_field.1.as_ref().unwrap_or(&pattern_field.0.name);
                                    let new_expr = Expr::Let(
                                        LetBinding {
                                            name: TypedIdent {
                                                name: pattern_field.clone(),
                                                typ: field.typ.clone(),
                                            },
                                            expr: Named::Expr(expr),
                                            span_start: pos::BytePos::default(),
                                        },
                                        next_expr,
                                    );
                                    &*self.allocator().arena.alloc(new_expr)
                                }),
                        )
                    }
                    _ => walk_expr_alloc(self, expr),
                }
            }
            _ => walk_expr_alloc(self, expr),
        }
    }

    fn allocator(&self) -> &'a Allocator<'a> {
        self.allocator
    }
}

pub fn optimize<'a>(allocator: &'a Allocator<'a>, expr: &'a Expr<'a>) -> &'a Expr<'a> {
    let mut optimizer = RecognizeUnnecessaryAllocation {
        allocator: allocator,
    };
    optimizer.visit_expr(expr).unwrap_or(expr)
}

pub fn walk_expr_alloc<'a, V>(visitor: &mut V, expr: &'a Expr<'a>) -> Option<&'a Expr<'a>>
where
    V: ?Sized + Visitor<'a>,
{
    walk_expr(visitor, expr).map(|expr| &*visitor.allocator().arena.alloc(expr))
}

pub fn walk_expr<'a, V>(visitor: &mut V, expr: &'a Expr<'a>) -> Option<Expr<'a>>
where
    V: ?Sized + Visitor<'a>,
{
    match *expr {
        Expr::Call(f, args) => {
            let new_f = walk_expr_alloc(visitor, f);
            let new_args = merge_iter(args, |expr| walk_expr(visitor, expr), Expr::clone)
                .map(|exprs: Vec<_>| {
                    &*visitor.allocator().arena.alloc_extend(exprs.into_iter())
                });

            merge(&f, new_f, &args, new_args, Expr::Call)
        }
        Expr::Const(_, _) => None,
        Expr::Data(ref id, exprs, pos, expansion) => {
            merge_iter(exprs, |expr| walk_expr(visitor, expr), Expr::clone).map(|exprs: Vec<_>| {
                Expr::Data(
                    id.clone(),
                    visitor.allocator().arena.alloc_extend(exprs.into_iter()),
                    pos,
                    expansion,
                )
            })
        }
        Expr::Ident(_, _) => None,
        Expr::Let(ref bind, expr) => {
            let new_named = match bind.expr {
                Named::Recursive(ref closures) => {
                    merge_iter(
                        closures,
                        |closure| {
                            walk_expr_alloc(visitor, closure.expr).map(|new_expr| {
                                Closure {
                                    name: closure.name.clone(),
                                    args: closure.args.clone(),
                                    expr: new_expr,
                                }
                            })
                        },
                        Closure::clone,
                    ).map(Named::Recursive)
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
                    &*visitor
                        .allocator()
                        .alternative_arena
                        .alloc_extend(alts.into_iter())
                });
            merge(&expr, new_expr, &alts, new_alts, Expr::Match)
        }
    }
}

fn walk_alt<'a, V>(visitor: &mut V, alt: &'a Alternative<'a>) -> Option<Alternative<'a>>
where
    V: ?Sized + Visitor<'a>,
{
    let new_expr = walk_expr_alloc(visitor, alt.expr);
    new_expr.map(|expr| {
        Alternative {
            pattern: alt.pattern.clone(),
            expr: expr,
        }
    })
}


#[cfg(test)]
mod tests {
    use super::*;

    use base::symbol::Symbols;

    use core;
    use core::grammar::parse_Expr as parse_core_expr;

    #[test]
    fn unnecessary_allocation() {
        let mut symbols = Symbols::new();
        let allocator = core::Allocator::new();

        let initial_str = r#"
            match { l, r } with
            | { l, r } -> l
            end
            "#;
        let initial_expr = allocator.arena.alloc(
            parse_core_expr(&mut symbols, &allocator, initial_str).unwrap(),
        );

        let optimized_expr = optimize(&allocator, initial_expr);

        let expected_str = r#"
            let l = l
            in
            let r = r
            in
            l
            "#;
        let expected_expr = parse_core_expr(&mut symbols, &allocator, expected_str).unwrap();
        assert_deq!(*optimized_expr, expected_expr);
    }
}
