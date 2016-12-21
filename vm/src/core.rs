extern crate typed_arena;
extern crate smallvec;

use std::iter::{once, repeat};

use self::typed_arena::Arena;

use self::smallvec::SmallVec;

use base::ast::{self, Literal, SpannedExpr, TypedIdent, Typed};
use base::symbol::Symbol;
use base::types::{ArcType, Type, TypeEnv};

#[derive(Clone, Debug)]
pub struct Closure<'a> {
    pub args: Vec<TypedIdent<Symbol>>,
    pub expr: &'a Expr<'a>,
}

#[derive(Clone, Debug)]
pub enum Named<'a> {
    // TODO Merge Closure and Recursive
    Closure(Vec<TypedIdent<Symbol>>, &'a Expr<'a>),
    Recursive(Vec<Closure<'a>>),
    Expr(&'a Expr<'a>),
}

#[derive(Clone, Debug)]
pub struct LetBinding<'a> {
    pub name: TypedIdent<Symbol>,
    pub expr: Named<'a>,
}

#[derive(Clone, Debug)]
pub enum Pattern {
    Constructor(TypedIdent<Symbol>, Vec<TypedIdent<Symbol>>),
    Record(Vec<(Symbol, Option<Symbol>)>),
    Ident(TypedIdent<Symbol>),
}

#[derive(Clone, Debug)]
pub struct Alternative<'a> {
    pub pattern: Pattern,
    pub expr: Expr<'a>,
}

#[derive(Clone, Debug)]
pub enum Expr<'a> {
    Const(Literal),
    Ident(TypedIdent<Symbol>),
    Call(&'a Expr<'a>, &'a [Expr<'a>]),
    Data(ArcType<Symbol>, &'a [Expr<'a>]),
    Let(LetBinding<'a>, &'a Expr<'a>),
    Match(&'a Expr<'a>, &'a [Alternative<'a>]),
}

pub struct Allocator<'a> {
    arena: Arena<Expr<'a>>,
    alternative_arena: Arena<Alternative<'a>>,
    true_constructor: TypedIdent<Symbol>,
    false_constructor: TypedIdent<Symbol>,
    dummy_symbol: TypedIdent<Symbol>,
}

impl<'a> Allocator<'a> {
    pub fn new() -> Allocator<'a> {
        Allocator {
            arena: Arena::new(),
            alternative_arena: Arena::new(),
            // TODO
            true_constructor: TypedIdent::new(Symbol::from("true")),
            false_constructor: TypedIdent::new(Symbol::from("false")),
            dummy_symbol: TypedIdent::new(Symbol::from("")),
        }
    }
    pub fn translate_alloc(&'a self, expr: &SpannedExpr<Symbol>) -> &'a Expr<'a> {
        self.arena.alloc(self.translate(expr))
    }

    pub fn translate(&'a self, expr: &SpannedExpr<Symbol>) -> Expr<'a> {
        let arena = &self.arena;
        match expr.value {
            ast::Expr::App(ref function, ref args) => {
                let new_args: SmallVec<[_; 16]> =
                    args.iter().map(|arg| self.translate(arg)).collect();
                Expr::Call(self.translate_alloc(function),
                           arena.alloc_extend(new_args.into_iter()))
            }
            ast::Expr::Array(ref array) => {
                let exprs: SmallVec<[_; 16]> =
                    array.exprs.iter().map(|expr| self.translate(expr)).collect();
                Expr::Data(array.typ.clone(), arena.alloc_extend(exprs.into_iter()))
            }
            ast::Expr::Block(ref exprs) => {
                let (last, prefix) = exprs.split_last().unwrap();
                let result = self.translate(last);
                prefix.iter().rev().fold(result, |result, expr| {
                    Expr::Let(LetBinding {
                                  name: self.dummy_symbol.clone(),
                                  expr: Named::Expr(self.translate_alloc(expr)),
                              },
                              arena.alloc(result))
                })
            }
            ast::Expr::Ident(ref id) => Expr::Ident(id.clone()),
            ast::Expr::IfElse(ref pred, ref if_true, ref if_false) => {
                let alts: SmallVec<[_; 2]> = collect![Alternative {
                                 pattern: Pattern::Constructor(self.true_constructor.clone(),
                                                               vec![]),
                                 expr: self.translate(if_true),
                             },
                             Alternative {
                                 pattern: Pattern::Constructor(self.false_constructor.clone(),
                                                               vec![]),
                                 expr: self.translate(if_false),
                             }];
                Expr::Match(self.translate_alloc(pred),
                            self.alternative_arena.alloc_extend(alts.into_iter()))
            }
            ast::Expr::Infix(ref l, ref op, ref r) => {
                let args: SmallVec<[_; 2]> = collect![self.translate(l), self.translate(r)];
                Expr::Call(arena.alloc(Expr::Ident(op.value.clone())),
                           arena.alloc_extend(args.into_iter()))
            }
            ast::Expr::Lambda(ref lambda) => {
                Expr::Let(LetBinding {
                              name: lambda.id.clone(),
                              expr: Named::Closure(lambda.args.clone(),
                                                   self.translate_alloc(&lambda.body)),
                          },
                          arena.alloc(Expr::Ident(lambda.id.clone())))
            }
            ast::Expr::LetBindings(ref binds, ref expr) => {
                let tail = self.translate(expr);
                let is_recursive = binds.iter().all(|bind| bind.args.len() > 0);
                if is_recursive {
                    let closures = binds.iter()
                        .map(|bind| {
                            Closure {
                                args: bind.args.clone(),
                                expr: self.translate_alloc(&bind.expr),
                            }
                        })
                        .collect();
                    Expr::Let(LetBinding {
                                  // TODO
                                  name: self.dummy_symbol.clone(),
                                  expr: Named::Recursive(closures),
                              },
                              arena.alloc(tail))
                } else {
                    binds.iter().rev().fold(tail, |tail, bind| {
                        let name = match bind.name.value {
                            ast::Pattern::Ident(ref id) => id.clone(),
                            _ => {
                                let alt = Alternative {
                                    pattern: self.translate_pattern(&bind.name.value),
                                    expr: tail,
                                };
                                return Expr::Match(self.translate_alloc(&bind.expr),
                                                   self.alternative_arena.alloc_extend(once(alt)));
                            }
                        };
                        let expr = if bind.args.is_empty() {
                            Named::Expr(self.translate_alloc(&bind.expr))
                        } else {
                            Named::Closure(bind.args.clone(), self.translate_alloc(&bind.expr))
                        };
                        Expr::Let(LetBinding {
                                      name: name,
                                      expr: expr,
                                  },
                                  arena.alloc(tail))
                    })
                }
            }
            ast::Expr::Literal(ref literal) => Expr::Const(literal.clone()),
            ast::Expr::Match(ref expr, ref alts) => {
                let new_alts: SmallVec<[_; 16]> = alts.iter()
                    .map(|alt| {
                        Alternative {
                            pattern: self.translate_pattern(&alt.pattern.value),
                            expr: self.translate(&alt.expr),
                        }
                    })
                    .collect();
                Expr::Match(self.translate_alloc(expr),
                            self.alternative_arena.alloc_extend(new_alts.into_iter()))
            }
            // expr.projection
            // =>
            // match expr with
            // | { projection } -> projection
            ast::Expr::Projection(ref expr, ref projection, _) => {
                let alt = Alternative {
                    pattern: Pattern::Record(vec![(projection.clone(), None)]),
                    expr: Expr::Ident(TypedIdent::new(projection.clone())),
                };
                Expr::Match(self.translate_alloc(expr),
                            self.alternative_arena.alloc_extend(once(alt)))
            }
            ast::Expr::Record { ref typ, ref exprs, .. } => {
                let args: SmallVec<[_; 16]> = exprs.iter()
                    .map(|&(ref field, ref expr)| match *expr {
                        Some(ref expr) => self.translate(expr),
                        None => Expr::Ident(TypedIdent::new(field.clone())),
                    })
                    .collect();
                Expr::Data(typ.clone(), arena.alloc_extend(args.into_iter()))
            }
            ast::Expr::Tuple(ref exprs) => {
                assert!(exprs.len() == 0, "Only unit is handled at the moment");
                let args: SmallVec<[_; 16]> = exprs.iter()
                    .map(|expr| self.translate(expr))
                    .collect();
                Expr::Data(Type::unit(), arena.alloc_extend(args.into_iter()))
            }
            ast::Expr::TypeBindings(_, ref expr) => self.translate(expr),
            ast::Expr::Error => panic!("ICE: Error expression found in the compiler"),
        }
    }

    fn translate_pattern(&self, pattern: &ast::Pattern<Symbol>) -> Pattern {
        match *pattern {
            ast::Pattern::Constructor(ref ctor, ref args) => {
                Pattern::Constructor(ctor.clone(), args.clone())
            }
            ast::Pattern::Ident(ref id) => Pattern::Ident(id.clone()),
            ast::Pattern::Record { ref fields, .. } => Pattern::Record(fields.clone()),
        }
    }
}

impl<'a> Typed for Expr<'a> {
    type Ident = Symbol;

    fn env_type_of(&self, env: &TypeEnv) -> ArcType<Self::Ident> {
        match *self {
            Expr::Call(expr, args) => get_return_type(env, &expr.env_type_of(env), args.len()),
            Expr::Const(ref literal) => literal.env_type_of(env),
            Expr::Data(ref typ, args) => get_return_type(env, typ, args.len()),
            Expr::Ident(ref id) => id.typ.clone(),
            Expr::Let(_, ref body) => body.env_type_of(env),
            Expr::Match(_, alts) => alts[0].expr.env_type_of(env),
        }
    }
}
fn get_return_type(env: &TypeEnv, alias_type: &ArcType, arg_count: usize) -> ArcType {
    use base::resolve::remove_aliases_cow;

    if arg_count == 0 {
        return alias_type.clone();
    }
    let function_type = remove_aliases_cow(env, alias_type);

    let (_, ret) = function_type.as_function().expect("Call expression with a non function type");
    get_return_type(env, ret, arg_count - 1)
}
