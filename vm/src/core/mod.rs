extern crate smallvec;
extern crate typed_arena;

#[macro_export]
#[cfg(test)]
macro_rules! assert_deq {
    ($left:expr, $right:expr) => ({
        match (&$left, &$right) {
            (left_val, right_val) => {
                if !(*left_val == *right_val) {
                    panic!("assertion failed: `(left == right)` \
                        (left: `{}`, right: `{}`)", left_val, right_val)
                }
            }
        }
    });
    ($left:expr, $right:expr, $($arg:tt)+) => ({
        match (&($left), &($right)) {
            (left_val, right_val) => {
                if !(*left_val == *right_val) {
                    panic!("assertion failed: `(left == right)` \
                        (left: `{}`, right: `{}`): {}", left_val, right_val,
                        format_args!($($arg)+))
                }
            }
        }
    });
}

#[cfg(all(test, feature = "test"))]
lalrpop_mod!(
    #[cfg_attr(rustfmt, rustfmt_skip)]
    pub grammar,
    "/core/grammar.rs"
);
pub mod interpreter;
pub mod optimize;
#[cfg(feature = "test")]
mod pretty;

use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt;
use std::iter::once;
use std::mem;

use itertools::Itertools;

use self::typed_arena::Arena;

use self::smallvec::SmallVec;

use base::ast::{self, Literal, SpannedExpr, SpannedPattern, Typed, TypedIdent};
use base::fnv::{FnvMap, FnvSet};
use base::pos::{spanned, BytePos, Span};
use base::resolve::remove_aliases_cow;
use base::symbol::Symbol;
use base::types::{arg_iter, ArcType, PrimitiveEnv, Type, TypeEnv};

#[derive(Clone, Debug, PartialEq)]
pub struct Closure<'a> {
    pub pos: BytePos,
    pub name: TypedIdent<Symbol>,
    pub args: Vec<TypedIdent<Symbol>>,
    pub expr: &'a Expr<'a>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Named<'a> {
    Recursive(Vec<Closure<'a>>),
    Expr(&'a Expr<'a>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct LetBinding<'a> {
    pub name: TypedIdent<Symbol>,
    pub expr: Named<'a>,
    pub span_start: BytePos,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Pattern {
    Constructor(TypedIdent<Symbol>, Vec<TypedIdent<Symbol>>),
    Record(Vec<(TypedIdent<Symbol>, Option<Symbol>)>),
    Ident(TypedIdent<Symbol>),
    Literal(ast::Literal),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Alternative<'a> {
    pub pattern: Pattern,
    pub expr: &'a Expr<'a>,
}

pub type CExpr<'a> = &'a Expr<'a>;

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<'a> {
    Const(Literal, Span<BytePos>),
    Ident(TypedIdent<Symbol>, Span<BytePos>),
    Call(&'a Expr<'a>, &'a [Expr<'a>]),
    Data(TypedIdent<Symbol>, &'a [Expr<'a>], BytePos),
    Let(LetBinding<'a>, &'a Expr<'a>),
    Match(&'a Expr<'a>, &'a [Alternative<'a>]),
}

#[cfg(feature = "test")]
impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use pretty;
        let arena = pretty::Arena::new();
        let mut s = Vec::new();
        self.pretty(&arena).1.render(80, &mut s).unwrap();
        write!(f, "{}", ::std::str::from_utf8(&s).expect("utf-8"))
    }
}
#[cfg(not(feature = "test"))]
impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[cfg(feature = "test")]
impl<'a> fmt::Display for Expr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use core::pretty::Prec;
        use pretty;
        let arena = pretty::Arena::new();
        let mut s = Vec::new();
        self.pretty(&arena, Prec::Top).1.render(80, &mut s).unwrap();
        write!(f, "{}", ::std::str::from_utf8(&s).expect("utf-8"))
    }
}

#[cfg(not(feature = "test"))]
impl<'a> fmt::Display for Expr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Default)]
#[must_use]
struct Binder<'a> {
    bindings: Vec<LetBinding<'a>>,
}

impl<'a> Binder<'a> {
    fn bind(&mut self, expr: CExpr<'a>, typ: ArcType) -> Expr<'a> {
        let name = TypedIdent {
            name: Symbol::from(format!("bind_arg{}", self.bindings.len())),
            typ,
        };
        self.bind_id(name, expr)
    }

    fn bind_id(&mut self, name: TypedIdent<Symbol>, expr: CExpr<'a>) -> Expr<'a> {
        let ident_expr = Expr::Ident(name.clone(), expr.span());
        self.bindings.push(LetBinding {
            name,
            expr: Named::Expr(expr),
            span_start: ident_expr.span().start(),
        });
        ident_expr
    }

    fn into_expr(self, arena: &'a Arena<Expr<'a>>, expr: Expr<'a>) -> Expr<'a> {
        self.bindings
            .into_iter()
            .rev()
            .fold(expr, |expr, bind| Expr::Let(bind, arena.alloc(expr)))
    }

    fn into_expr_ref(self, arena: &'a Arena<Expr<'a>>, expr: &'a Expr<'a>) -> &'a Expr<'a> {
        self.bindings
            .into_iter()
            .rev()
            .fold(expr, |expr, bind| arena.alloc(Expr::Let(bind, expr)))
    }
}

impl<'a> Expr<'a> {
    pub fn span(&self) -> Span<BytePos> {
        match *self {
            Expr::Call(expr, args) => {
                let span = expr.span();
                Span::new(span.start(), args.last().unwrap().span().end())
            }
            Expr::Const(_, span) => span,
            Expr::Data(_, args, span_start) => {
                let span_end = args.last().map_or(span_start, |arg| arg.span().end());
                Span::new(span_start, span_end)
            }
            Expr::Ident(_, span) => span,
            Expr::Let(ref let_binding, ref body) => {
                let span_end = body.span();
                Span::new(let_binding.span_start, span_end.end())
            }
            Expr::Match(expr, alts) => {
                let span_start = expr.span();
                Span::new(span_start.start(), alts.last().unwrap().expr.span().end())
            }
        }
    }
}

fn is_constructor(s: &Symbol) -> bool {
    s.as_ref()
        .rsplit('.')
        .next()
        .unwrap()
        .starts_with(char::is_uppercase)
}

mod internal {
    use super::{Allocator, Expr};

    pub struct CoreExpr {
        allocator: Allocator<'static>,
        expr: Expr<'static>,
    }

    impl CoreExpr {
        pub fn new(allocator: Allocator<'static>, expr: Expr<'static>) -> CoreExpr {
            CoreExpr { allocator, expr }
        }

        // unsafe: The lifetimes of the returned `Expr` must be bound to `&self`
        pub fn expr(&self) -> &Expr {
            &self.expr
        }

        pub fn allocator(&self) -> &Allocator {
            unsafe { ::std::mem::transmute(&self.allocator) }
        }
    }
}

pub use self::internal::CoreExpr;

pub struct Allocator<'a> {
    pub arena: Arena<Expr<'a>>,
    pub alternative_arena: Arena<Alternative<'a>>,
}

impl<'a> Allocator<'a> {
    pub fn new() -> Allocator<'a> {
        Allocator {
            arena: Arena::new(),
            alternative_arena: Arena::new(),
        }
    }
}

pub fn translate(env: &PrimitiveEnv, expr: &SpannedExpr<Symbol>) -> CoreExpr {
    // Here we temporarily forget the lifetime of `translator` so it can be moved into a
    // `CoreExpr`. After we have it in `CoreExpr` the expression is then guaranteed to live as
    // long as the `CoreExpr` making it safe again
    unsafe {
        let translator = Translator::new(env);
        let core_expr = {
            let core_expr = (*(&translator as *const Translator)).translate(expr);
            mem::transmute::<Expr, Expr<'static>>(core_expr)
        };
        CoreExpr::new(
            mem::transmute::<Allocator, Allocator<'static>>(translator.allocator),
            core_expr,
        )
    }
}

pub struct Translator<'a, 'e> {
    pub allocator: Allocator<'a>,
    env: &'e PrimitiveEnv,
    dummy_symbol: TypedIdent<Symbol>,
}

impl<'a, 'e> Translator<'a, 'e> {
    pub fn new(env: &'e PrimitiveEnv) -> Translator<'a, 'e> {
        Translator {
            allocator: Allocator::new(),
            env: env,
            dummy_symbol: TypedIdent::new(Symbol::from("")),
        }
    }

    pub fn translate_alloc(&'a self, expr: &SpannedExpr<Symbol>) -> &'a Expr<'a> {
        self.allocator.arena.alloc(self.translate(expr))
    }

    pub fn translate(&'a self, expr: &SpannedExpr<Symbol>) -> Expr<'a> {
        let mut current = expr;
        let mut lets = Vec::new();
        while let ast::Expr::LetBindings(ref binds, ref tail) = current.value {
            lets.push((current.span.start(), binds));
            current = tail;
        }
        let tail = self.translate_(current);
        lets.iter()
            .rev()
            .fold(tail, |result, &(span_start, ref binds)| {
                self.translate_let(binds, result, span_start)
            })
    }

    fn translate_(&'a self, expr: &SpannedExpr<Symbol>) -> Expr<'a> {
        let arena = &self.allocator.arena;
        match expr.value {
            ast::Expr::App {
                ref implicit_args,
                func: ref function,
                ref args,
            } => {
                let new_args: SmallVec<[_; 16]> = implicit_args
                    .iter()
                    .chain(args)
                    .map(|arg| self.translate(arg))
                    .collect();
                match function.value {
                    ast::Expr::Ident(ref id) if is_constructor(&id.name) => {
                        let typ = expr.env_type_of(&self.env);
                        self.new_data_constructor(typ, id, new_args, expr.span)
                    }
                    _ => Expr::Call(
                        self.translate_alloc(function),
                        arena.alloc_extend(new_args.into_iter()),
                    ),
                }
            }

            ast::Expr::Array(ref array) => {
                let exprs: SmallVec<[_; 16]> = array
                    .exprs
                    .iter()
                    .map(|expr| self.translate(expr))
                    .collect();
                Expr::Data(
                    TypedIdent {
                        name: self.dummy_symbol.name.clone(),
                        typ: array.typ.clone(),
                    },
                    arena.alloc_extend(exprs.into_iter()),
                    expr.span.start(),
                )
            }

            ast::Expr::Block(ref exprs) => {
                let (last, prefix) = exprs.split_last().unwrap();
                let result = self.translate(last);
                prefix.iter().rev().fold(result, |result, expr| {
                    Expr::Let(
                        LetBinding {
                            name: self.dummy_symbol.clone(),
                            expr: Named::Expr(self.translate_alloc(expr)),
                            span_start: expr.span.start(),
                        },
                        arena.alloc(result),
                    )
                })
            }

            ast::Expr::Ident(ref id) => {
                if is_constructor(&id.name) {
                    self.new_data_constructor(id.typ.clone(), id, SmallVec::new(), expr.span)
                } else {
                    Expr::Ident(id.clone(), expr.span)
                }
            }

            ast::Expr::IfElse(ref pred, ref if_true, ref if_false) => {
                let alts: SmallVec<[_; 2]> = collect![
                    Alternative {
                        pattern: Pattern::Constructor(self.bool_constructor(true), vec![]),
                        expr: self.translate_alloc(if_true),
                    },
                    Alternative {
                        pattern: Pattern::Constructor(self.bool_constructor(false), vec![]),
                        expr: self.translate_alloc(if_false),
                    },
                ];
                Expr::Match(
                    self.translate_alloc(pred),
                    self.allocator
                        .alternative_arena
                        .alloc_extend(alts.into_iter()),
                )
            }

            ast::Expr::Infix {
                ref lhs,
                ref op,
                ref rhs,
                ref implicit_args,
            } => {
                let args: SmallVec<[_; 2]> = implicit_args
                    .iter()
                    .chain(Some(&**lhs))
                    .chain(Some(&**rhs))
                    .map(|e| self.translate(e))
                    .collect();

                Expr::Call(
                    arena.alloc(Expr::Ident(op.value.clone(), op.span)),
                    arena.alloc_extend(args.into_iter()),
                )
            }

            ast::Expr::Lambda(ref lambda) => self.new_lambda(
                expr.span.start(),
                lambda.id.clone(),
                lambda
                    .args
                    .iter()
                    .map(|arg| arg.name.value.clone())
                    .collect(),
                self.translate_alloc(&lambda.body),
                expr.span,
            ),

            ast::Expr::LetBindings(ref binds, ref tail) => {
                self.translate_let(binds, self.translate(tail), expr.span.start())
            }

            ast::Expr::Literal(ref literal) => Expr::Const(literal.clone(), expr.span),

            ast::Expr::Match(ref expr, ref alts) => {
                let expr = self.translate_alloc(expr);
                let alts: Vec<_> = alts
                    .iter()
                    .map(|alt| Equation {
                        patterns: vec![&alt.pattern],
                        result: self.translate_alloc(&alt.expr),
                    })
                    .collect();
                PatternTranslator(self).translate_top(expr, &alts).clone()
            }
            // expr.projection
            // =>
            // match expr with
            // | { projection } -> projection
            ast::Expr::Projection(ref projected_expr, ref projection, ref projected_type) => {
                let projected_expr = self.translate_alloc(projected_expr);
                self.project_expr(expr.span, projected_expr, projection, projected_type)
            }

            ast::Expr::Record {
                ref typ,
                ref exprs,
                ref base,
                ..
            } => {
                let mut binder = Binder::default();

                // If `base` exists and is non-trivial we need to introduce bindings for each
                // value to ensure that the expressions are evaluated in the correct order
                let needs_bindings = base.as_ref().map_or(false, |base| match base.value {
                    ast::Expr::Ident(_) => false,
                    _ => true,
                });

                let mut last_span = expr.span;
                let mut args = SmallVec::<[_; 16]>::new();
                args.extend(exprs.iter().map(|field| {
                    let expr = match field.value {
                        Some(ref expr) => {
                            last_span = expr.span;
                            self.translate(expr)
                        }
                        None => Expr::Ident(TypedIdent::new(field.name.value.clone()), last_span),
                    };
                    if needs_bindings {
                        let typ = expr.env_type_of(&self.env);
                        binder.bind(arena.alloc(expr), typ)
                    } else {
                        expr
                    }
                }));

                let base_binding = base.as_ref().map(|base_expr| {
                    let core_base = self.translate_alloc(base_expr);
                    let typ = remove_aliases_cow(&self.env, &base_expr.env_type_of(&self.env))
                        .into_owned();

                    let core_base = if needs_bindings {
                        &*arena.alloc(binder.bind(core_base, base_expr.env_type_of(&self.env)))
                    } else {
                        core_base
                    };
                    (core_base, typ)
                });

                if let Some((ref base_ident_expr, ref base_type)) = base_binding {
                    let base_fields: FnvSet<&str> = base_type
                        .row_iter()
                        .map(|field| field.name.declared_name())
                        .collect();

                    let mut reordered_args = SmallVec::<[_; 16]>::new();

                    let mut overridden_fields = FnvMap::default();
                    for (field, arg) in exprs.iter().zip(args.drain()) {
                        let field_name = field.name.value.declared_name();
                        if base_fields.contains(field_name) {
                            overridden_fields.insert(field_name, arg);
                        } else {
                            reordered_args.push(arg);
                        }
                    }

                    args.extend(reordered_args);

                    args.extend(base_type.row_iter().map(move |field| {
                        match overridden_fields.remove(field.name.declared_name()) {
                            Some(e) => e,
                            None => self.project_expr(
                                base_ident_expr.span(),
                                base_ident_expr,
                                &field.name,
                                &field.typ,
                            ),
                        }
                    }));
                }

                let record_constructor = Expr::Data(
                    TypedIdent {
                        name: self.dummy_symbol.name.clone(),
                        typ: typ.clone(),
                    },
                    arena.alloc_extend(args),
                    expr.span.start(),
                );
                binder.into_expr(arena, record_constructor)
            }

            ast::Expr::Tuple { ref elems, .. } => {
                if elems.len() == 1 {
                    self.translate(&elems[0])
                } else {
                    let args: SmallVec<[_; 16]> =
                        elems.iter().map(|expr| self.translate(expr)).collect();
                    Expr::Data(
                        TypedIdent {
                            name: self.dummy_symbol.name.clone(),
                            typ: expr.env_type_of(&self.env),
                        },
                        arena.alloc_extend(args.into_iter()),
                        expr.span.start(),
                    )
                }
            }

            ast::Expr::TypeBindings(_, ref expr) => self.translate(expr),

            ast::Expr::Do(ast::Do {
                ref id,
                ref bound,
                ref body,
                ref flat_map_id,
            }) => {
                let flat_map_id = flat_map_id
                    .as_ref()
                    .unwrap_or_else(|| ice!("flat_map_id must be set when translating to core"));

                let mut binder = Binder::default();
                let bound_ident =
                    binder.bind(self.translate_alloc(bound), bound.env_type_of(&self.env));

                let lambda = self.new_lambda(
                    expr.span.start(),
                    id.value.clone(),
                    vec![id.value.clone()],
                    self.translate_alloc(body),
                    body.span,
                );

                let f = self.translate_alloc(flat_map_id);
                binder.into_expr(
                    arena,
                    Expr::Call(
                        f,
                        arena.alloc_extend(Some(lambda).into_iter().chain(Some(bound_ident))),
                    ),
                )
            }

            ast::Expr::MacroExpansion {
                replacement: ref expr,
                ..
            }
            | ast::Expr::Annotated(ref expr, _) => self.translate_(expr),

            ast::Expr::Error(_) => ice!("ICE: Error expression found in the compiler"),
        }
    }

    fn project_expr(
        &'a self,
        span: Span<BytePos>,
        projected_expr: CExpr<'a>,
        projection: &Symbol,
        projected_type: &ArcType,
    ) -> Expr<'a> {
        let arena = &self.allocator.arena;
        let alt = Alternative {
            pattern: Pattern::Record(vec![(
                TypedIdent {
                    name: projection.clone(),
                    typ: projected_type.clone(),
                },
                None,
            )]),
            expr: arena.alloc(Expr::Ident(
                TypedIdent {
                    name: projection.clone(),
                    typ: projected_type.clone(),
                },
                span,
            )),
        };
        Expr::Match(
            projected_expr,
            self.allocator.alternative_arena.alloc_extend(once(alt)),
        )
    }

    fn translate_let(
        &'a self,
        binds: &ast::ValueBindings<Symbol>,
        tail: Expr<'a>,
        span_start: BytePos,
    ) -> Expr<'a> {
        let arena = &self.allocator.arena;

        if binds.is_recursive() {
            let closures = binds
                .iter()
                .map(|bind| Closure {
                    pos: bind.name.span.start(),
                    name: match bind.name.value {
                        ast::Pattern::Ident(ref id) => id.clone(),
                        _ => unreachable!(),
                    },
                    args: bind.args.iter().map(|arg| arg.name.value.clone()).collect(),
                    expr: self.translate_alloc(&bind.expr),
                })
                .collect();
            Expr::Let(
                LetBinding {
                    // TODO
                    name: self.dummy_symbol.clone(),
                    expr: Named::Recursive(closures),
                    span_start: span_start,
                },
                arena.alloc(tail),
            )
        } else {
            binds.iter().rev().fold(tail, |tail, bind| {
                let name = match bind.name.value {
                    ast::Pattern::Ident(ref id) => id.clone(),
                    _ => {
                        let bind_expr = self.translate_alloc(&bind.expr);
                        let tail = &*arena.alloc(tail);
                        return PatternTranslator(self).translate_top(
                            bind_expr,
                            &[Equation {
                                patterns: vec![&bind.name],
                                result: tail,
                            }],
                        );
                    }
                };
                let named = if bind.args.is_empty() {
                    Named::Expr(self.translate_alloc(&bind.expr))
                } else {
                    Named::Recursive(vec![Closure {
                        pos: bind.name.span.start(),
                        name: name.clone(),
                        args: bind.args.iter().map(|arg| arg.name.value.clone()).collect(),
                        expr: self.translate_alloc(&bind.expr),
                    }])
                };
                Expr::Let(
                    LetBinding {
                        name: name,
                        expr: named,
                        span_start: bind.expr.span.start(),
                    },
                    arena.alloc(tail),
                )
            })
        }
    }

    fn bool_constructor(&self, variant: bool) -> TypedIdent<Symbol> {
        let b = self.env.get_bool();
        match **b {
            Type::Alias(ref alias) => match **alias.typ() {
                Type::Variant(ref variants) => TypedIdent {
                    name: variants
                        .row_iter()
                        .nth(variant as usize)
                        .unwrap()
                        .name
                        .clone(),
                    typ: b.clone(),
                },
                _ => ice!(),
            },
            _ => ice!(),
        }
    }

    fn new_data_constructor(
        &'a self,
        expr_type: ArcType,
        id: &TypedIdent<Symbol>,
        mut new_args: SmallVec<[Expr<'a>; 16]>,
        span: Span<BytePos>,
    ) -> Expr<'a> {
        let arena = &self.allocator.arena;
        let typ = expr_type;
        let unapplied_args: Vec<_>;
        // If the constructor is not fully applied we retrieve the type of the data
        // by iterating through the arguments. If it is fully applied the arg_iter
        // has no effect and `typ` itself will be used
        let data_type;
        {
            let mut args = arg_iter(typ.remove_forall());
            unapplied_args = args
                .by_ref()
                .enumerate()
                .map(|(i, arg)| TypedIdent {
                    name: Symbol::from(format!("#{}", i)),
                    typ: arg.clone(),
                })
                .collect();
            data_type = args.typ.clone();
        }
        new_args.extend(
            unapplied_args
                .iter()
                .map(|arg| Expr::Ident(arg.clone(), span)),
        );
        let data = Expr::Data(
            TypedIdent {
                name: id.name.clone(),
                typ: data_type,
            },
            arena.alloc_extend(new_args.into_iter()),
            span.start(),
        );
        if unapplied_args.is_empty() {
            data
        } else {
            self.new_lambda(
                span.start(),
                TypedIdent {
                    name: Symbol::from(format!("${}", id.name)),
                    typ: typ,
                },
                unapplied_args,
                arena.alloc(data),
                span,
            )
        }
    }

    fn new_lambda(
        &'a self,
        pos: BytePos,
        name: TypedIdent<Symbol>,
        args: Vec<TypedIdent<Symbol>>,
        body: &'a Expr<'a>,
        span: Span<BytePos>,
    ) -> Expr<'a> {
        let arena = &self.allocator.arena;
        Expr::Let(
            LetBinding {
                name: name.clone(),
                expr: Named::Recursive(vec![Closure {
                    pos,
                    name: name.clone(),
                    args: args,
                    expr: body,
                }]),
                span_start: span.start(),
            },
            arena.alloc(Expr::Ident(name, span)),
        )
    }
}

impl<'a> Typed for Expr<'a> {
    type Ident = Symbol;

    fn try_type_of(&self, env: &TypeEnv) -> Result<ArcType<Self::Ident>, String> {
        match *self {
            Expr::Call(expr, args) => get_return_type(env, &expr.try_type_of(env)?, args.len()),
            Expr::Const(ref literal, _) => literal.try_type_of(env),
            Expr::Data(ref id, ..) => Ok(id.typ.clone()),
            Expr::Ident(ref id, _) => Ok(id.typ.clone()),
            Expr::Let(_, ref body) => body.try_type_of(env),
            Expr::Match(_, alts) => alts[0].expr.try_type_of(env),
        }
    }
}

fn get_return_type(
    env: &TypeEnv,
    alias_type: &ArcType,
    arg_count: usize,
) -> Result<ArcType, String> {
    if arg_count == 0 || **alias_type == Type::Hole {
        return Ok(alias_type.clone());
    }
    let function_type = remove_aliases_cow(env, alias_type);

    let ret = function_type
        .remove_forall()
        .as_function()
        .map(|t| Cow::Borrowed(t.1))
        .unwrap_or_else(|| {
            panic!("Unexpected type {} is not a function", function_type);
        });

    get_return_type(env, &ret, arg_count - 1)
}

pub struct PatternTranslator<'a, 'e: 'a>(&'a Translator<'a, 'e>);

#[derive(Clone, PartialEq, Debug)]
struct Equation<'a, 'p> {
    patterns: Vec<&'p SpannedPattern<Symbol>>,
    result: &'a Expr<'a>,
}

impl<'a, 'p> fmt::Display for Equation<'a, 'p> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "[({:?},{})]",
            self.patterns.iter().format(", "),
            self.result
        )
    }
}

#[derive(PartialEq)]
enum CType {
    Constructor,
    Record,
    Variable,
    Literal,
}

use self::optimize::*;
struct ReplaceVariables<'a, 'b> {
    replacements: &'b HashMap<Symbol, Symbol>,
    allocator: &'a Allocator<'a>,
}

impl<'a, 'b> Visitor<'a, 'a> for ReplaceVariables<'a, 'b> {
    type Producer = SameLifetime<'a>;

    fn visit_expr(&mut self, expr: &'a Expr<'a>) -> Option<&'a Expr<'a>> {
        match *expr {
            Expr::Ident(ref id, span) => self.replacements.get(&id.name).map(|new_name| {
                &*self.allocator.arena.alloc(Expr::Ident(
                    TypedIdent {
                        name: new_name.clone(),
                        typ: id.typ.clone(),
                    },
                    span,
                ))
            }),
            _ => walk_expr_alloc(self, expr),
        }
    }
    fn detach_allocator(&self) -> Option<&'a Allocator<'a>> {
        Some(self.allocator)
    }
}

fn replace_variables<'a, 'b>(
    allocator: &'a Allocator<'a>,
    replacements: &'b HashMap<Symbol, Symbol>,
    expr: &'a Expr<'a>,
) -> &'a Expr<'a> {
    if replacements.is_empty() {
        expr
    } else {
        ReplaceVariables {
            replacements,
            allocator,
        }
        .visit_expr(expr)
        .unwrap_or(expr)
    }
}

/// `PatternTranslator` translated nested (AST) patterns into non-nested (core) patterns.
///
/// It does this this by looking at each nested pattern as part of an `Equation` to be solved.
/// Each step of the algorithm looks at the first pattern in each equation, translates it into a
/// a non-nested match and then for each alternative in this created `match` it recursively calls
/// itself with the rest of the equations plus any nested patterns from the pattern that was
/// just translated to the non-nested form.
///
/// For a more comprehensive explanation the following links are recommended
///
/// The implementation of Hob
/// http://marijnhaverbeke.nl/hob/saga/pattern_matching.html
///
/// Derivation of a Pattern-Matching Compiler
/// Geoff Barrett and Philip Wadler
/// Oxford University Computing Laboratory, Programming Research Group
/// 1986
/// http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.257.6166&rep=rep1&type=pdf
impl<'a, 'e> PatternTranslator<'a, 'e> {
    fn varcons_compile<'p>(
        &mut self,
        default: &'a Expr<'a>,
        variables: &[&'a Expr<'a>],
        varcon: CType,
        equations: &[Equation<'a, 'p>],
    ) -> &'a Expr<'a> {
        match varcon {
            CType::Constructor => self.compile_constructor(default, variables, equations),
            CType::Record => self.compile_record(default, variables, equations),
            CType::Variable => self.compile_variable(default, variables, equations),
            CType::Literal => self.compile_literal(default, variables, equations),
        }
    }

    fn compile_record<'p>(
        &mut self,
        default: &'a Expr<'a>,
        variables: &[&'a Expr<'a>],
        equations: &[Equation<'a, 'p>],
    ) -> &'a Expr<'a> {
        use std::borrow::Cow;

        let new_alt = {
            // Inspect the first pattern of each equation
            // (the rest of the equations are checked recursively)
            let first_iter = || {
                equations
                    .iter()
                    .map(|equation| *equation.patterns.first().unwrap())
            };

            let (pattern, replacements) = self.pattern_identifiers(first_iter());

            // Gather the inner patterns so we can prepend them to equations
            let temp = first_iter()
                .map(|pattern| match *unwrap_as(&pattern.value) {
                    ast::Pattern::Record {
                        ref typ,
                        ref fields,
                        ..
                    } => {
                        let record_type = remove_aliases_cow(&self.0.env, typ);

                        fields
                            .iter()
                            .map(|field| {
                                field.value.as_ref().map(Cow::Borrowed).unwrap_or_else(|| {
                                    let field_type = record_type
                                        .row_iter()
                                        .find(|f| f.name.name_eq(&field.name.value))
                                        .map(|f| f.typ.clone())
                                        .unwrap_or_else(|| Type::hole());
                                    Cow::Owned(spanned(
                                        Span::default(),
                                        ast::Pattern::Ident(TypedIdent {
                                            name: field.name.value.clone(),
                                            typ: field_type,
                                        }),
                                    ))
                                })
                            })
                            .collect::<Vec<_>>()
                    }
                    ast::Pattern::Tuple { ref elems, .. } => {
                        elems.iter().map(Cow::Borrowed).collect::<Vec<_>>()
                    }
                    _ => unreachable!(),
                })
                .collect::<Vec<_>>();

            // The first pattern of each equation has been processed, prepend the inner patterns
            // (since those need to be solved first) and then the remaining_patterns
            let new_equations = equations
                .iter()
                .map(|equation| (&equation.patterns[1..], equation.result))
                .zip(&temp)
                .map(|((remaining_equations, result), first)| Equation {
                    patterns: first
                        .iter()
                        .map(|pattern| &**pattern)
                        .chain(remaining_equations.iter().cloned())
                        .collect(),
                    result,
                })
                .collect::<Vec<_>>();

            let new_variables = self.insert_new_variables(&pattern, variables);

            let expr = self.translate(default, &new_variables, &new_equations);
            let expr = replace_variables(&self.0.allocator, &replacements, expr);

            Alternative {
                pattern: pattern,
                expr: expr,
            }
        };
        let expr = Expr::Match(
            variables[0],
            self.0
                .allocator
                .alternative_arena
                .alloc_extend(Some(new_alt).into_iter()),
        );
        self.0.allocator.arena.alloc(expr)
    }

    fn compile_constructor<'p>(
        &mut self,
        default: &'a Expr<'a>,
        variables: &[&'a Expr<'a>],
        equations: &[Equation<'a, 'p>],
    ) -> &'a Expr<'a> {
        let mut group_order = Vec::new();
        let mut groups = HashMap::new();

        for equation in equations {
            match *unwrap_as(&equation.patterns.first().unwrap().value) {
                ast::Pattern::Constructor(ref id, _) => {
                    groups
                        .entry(&id.name)
                        .or_insert_with(|| {
                            group_order.push(&id.name);
                            Vec::new()
                        })
                        .push(equation);
                }
                ast::Pattern::As(_, _)
                | ast::Pattern::Tuple { .. }
                | ast::Pattern::Record { .. }
                | ast::Pattern::Ident(_)
                | ast::Pattern::Literal(_)
                | ast::Pattern::Error => unreachable!(),
            }
        }

        // Check if all the constructors of the variant are matched on

        let complete = {
            let t = variables[0].env_type_of(&self.0.env);
            let t = remove_aliases_cow(&self.0.env, &t);
            let mut iter = t.remove_forall().row_iter();
            groups.len() == iter.by_ref().count() && **iter.current_type() == Type::EmptyRow
        };

        let new_alts = group_order
            .into_iter()
            .map(|key| {
                let equations = &groups[key];
                let (pattern, replacements) = self.pattern_identifiers(
                    equations
                        .iter()
                        .map(|equation| *equation.patterns.first().unwrap()),
                );

                // Add new patterns for each equation from the nested patterns
                let new_equations = equations
                    .iter()
                    .map(|equation| {
                        let first = match *unwrap_as(&equation.patterns.first().unwrap().value) {
                            ast::Pattern::Constructor(_, ref patterns) => patterns,
                            _ => unreachable!(),
                        };
                        Equation {
                            patterns: first
                                .iter()
                                .chain(equation.patterns.iter().cloned().skip(1))
                                .collect(),
                            result: equation.result,
                        }
                    })
                    .collect::<Vec<_>>();

                let new_variables = self.insert_new_variables(&pattern, variables);

                let expr = self.translate(default, &new_variables, &new_equations);
                let expr = replace_variables(&self.0.allocator, &replacements, expr);

                Alternative {
                    pattern: pattern,
                    expr: expr,
                }
            })
            .chain(if complete {
                None
            } else {
                Some(match *default {
                    // HACK We remove a redundant nested match by identifying that it
                    // matches on the same thing as the curret match
                    //
                    // match p1 with
                    // | ...
                    // | _ ->
                    //     match p1 with
                    //     | x -> <expr>
                    //
                    // to
                    //
                    // match p1 with
                    // | ...
                    // | x -> <expr>
                    Expr::Match(e, alts) if e == variables[0] && alts.len() == 1 => alts[0].clone(),
                    _ => Alternative {
                        pattern: Pattern::Ident(TypedIdent::new(Symbol::from("_"))),
                        expr: default,
                    },
                })
            })
            .collect::<Vec<_>>();
        let expr = Expr::Match(
            variables[0],
            self.0
                .allocator
                .alternative_arena
                .alloc_extend(new_alts.into_iter()),
        );
        self.0.allocator.arena.alloc(expr)
    }

    fn compile_variable<'p>(
        &mut self,
        default: &'a Expr<'a>,
        variables: &[&'a Expr<'a>],
        equations: &[Equation<'a, 'p>],
    ) -> &'a Expr<'a> {
        let expr = self.translate(
            default,
            &variables[1..],
            &equations
                .iter()
                .map(|equation| Equation {
                    patterns: equation.patterns[1..].to_owned(),
                    result: equation.result,
                })
                .collect::<Vec<_>>(),
        );
        let (pattern, replacements) = self.pattern_identifiers(
            equations
                .iter()
                .map(|equation| *equation.patterns.first().unwrap()),
        );
        let expr = replace_variables(&self.0.allocator, &replacements, expr);

        let alt = Alternative {
            pattern: pattern,
            expr: expr,
        };

        // match x with
        // | y -> EXPR
        // // ==>
        // EXPR // with `y`s replaced by `x`
        match (&alt.pattern, variables[0]) {
            (&Pattern::Ident(ref id), &Expr::Ident(ref expr_id, _)) => {
                return replace_variables(
                    &self.0.allocator,
                    &collect![(id.name.clone(), expr_id.name.clone())],
                    expr,
                );
            }
            _ => (),
        }

        let expr = Expr::Match(
            variables[0],
            self.0
                .allocator
                .alternative_arena
                .alloc_extend(Some(alt).into_iter()),
        );
        self.0.allocator.arena.alloc(expr)
    }

    fn compile_literal<'p>(
        &mut self,
        default: &'a Expr<'a>,
        variables: &[&'a Expr<'a>],
        equations: &[Equation<'a, 'p>],
    ) -> &'a Expr<'a> {
        let mut group_order = Vec::new();
        let mut groups = HashMap::new();

        for equation in equations {
            match *unwrap_as(&equation.patterns.first().unwrap().value) {
                ast::Pattern::Literal(ref literal) => {
                    groups
                        .entry(literal)
                        .or_insert_with(|| {
                            group_order.push(literal);
                            Vec::new()
                        })
                        .push(equation.clone());
                }
                ast::Pattern::Constructor(_, _)
                | ast::Pattern::As(_, _)
                | ast::Pattern::Tuple { .. }
                | ast::Pattern::Record { .. }
                | ast::Pattern::Ident(_)
                | ast::Pattern::Error => unreachable!(),
            }
        }

        let new_alts = group_order
            .into_iter()
            .map(|key| {
                let equations = &groups[key];
                let pattern = Pattern::Literal(key.clone());

                let new_equations = equations
                    .iter()
                    .map(|equation| Equation {
                        patterns: equation.patterns.iter().cloned().skip(1).collect(),
                        result: equation.result,
                    })
                    .collect::<Vec<_>>();

                let new_variables = self.insert_new_variables(&pattern, variables);
                let expr = self.translate(default, &new_variables, &new_equations);
                Alternative {
                    pattern: pattern,
                    expr: expr,
                }
            })
            .chain(Some(Alternative {
                pattern: Pattern::Ident(TypedIdent::new(Symbol::from("_"))),
                expr: default,
            }))
            .collect::<Vec<_>>();

        let expr = Expr::Match(
            variables[0],
            self.0
                .allocator
                .alternative_arena
                .alloc_extend(new_alts.into_iter()),
        );
        self.0.allocator.arena.alloc(expr)
    }

    // Generates a variable for each of the new equations we inserted
    // This variable is what we `match` the expression(s) on
    fn insert_new_variables(
        &self,
        pattern: &Pattern,
        variables: &[&'a Expr<'a>],
    ) -> Vec<&'a Expr<'a>> {
        PatternIdentifiers::new(pattern)
            .map(|id| {
                &*self
                    .0
                    .allocator
                    .arena
                    .alloc(Expr::Ident(id, Span::default()))
            })
            .chain(variables[1..].iter().cloned())
            .collect::<Vec<_>>()
    }

    fn translate_top<'p>(
        &mut self,
        expr: &'a Expr<'a>,
        equations: &[Equation<'a, 'p>],
    ) -> Expr<'a> {
        let arena = &self.0.allocator.arena;
        let error = arena.alloc(Expr::Ident(
            TypedIdent::new(Symbol::from("@error")),
            Span::default(),
        ));
        let args = arena.alloc_extend(
            Some(Expr::Const(
                Literal::String("Unmatched pattern".into()),
                Span::default(),
            ))
            .into_iter(),
        );
        let default = arena.alloc(Expr::Call(error, args));
        match *expr {
            Expr::Ident(..) => self.translate(default, &[expr], equations).clone(),
            _ => {
                let name = TypedIdent {
                    name: Symbol::from("match_pattern"),
                    typ: expr.env_type_of(&self.0.env),
                };
                let id_expr = self
                    .0
                    .allocator
                    .arena
                    .alloc(Expr::Ident(name.clone(), expr.span()));
                Expr::Let(
                    LetBinding {
                        name: name,
                        expr: Named::Expr(expr),
                        span_start: expr.span().start(),
                    },
                    self.translate(default, &[id_expr], equations),
                )
            }
        }
    }

    fn translate<'p>(
        &mut self,
        default: &'a Expr<'a>,
        variables: &[&'a Expr<'a>],
        equations: &[Equation<'a, 'p>],
    ) -> &'a Expr<'a> {
        fn varcon(pattern: &ast::Pattern<Symbol>) -> CType {
            match *pattern {
                ast::Pattern::As(_, ref pattern) => varcon(&pattern.value),
                ast::Pattern::Ident(_) => CType::Variable,
                ast::Pattern::Record { .. } | ast::Pattern::Tuple { .. } => CType::Record,
                ast::Pattern::Constructor(_, _) => CType::Constructor,
                ast::Pattern::Literal(_) => CType::Literal,
                ast::Pattern::Error => ice!("ICE: Error pattern survived typechecking"),
            }
        }

        let mut binder = Binder::default();

        // The equations must be processed by group
        //
        // | Some (Some x) ->
        // | Some None ->
        // | x ->
        let groups = equations
            .iter()
            .group_by(|equation| varcon(&equation.patterns.first().expect("Pattern").value));

        let expr = match variables.first() {
            None => equations
                .first()
                .map(|equation| equation.result)
                .unwrap_or(default),
            Some(_) => {
                fn bind_variables<'b>(
                    env: &PrimitiveEnv,
                    pat: &ast::SpannedPattern<Symbol>,
                    variable: CExpr<'b>,
                    binder: &mut Binder<'b>,
                ) {
                    match pat.value {
                        ast::Pattern::As(ref id, ref pat) => {
                            binder.bind_id(
                                TypedIdent {
                                    name: id.value.clone(),
                                    typ: pat.env_type_of(&env),
                                },
                                variable,
                            );
                            bind_variables(env, pat, variable, binder);
                        }
                        ast::Pattern::Record {
                            implicit_import: Some(ref implicit_import),
                            ..
                        } => {
                            binder.bind_id(
                                TypedIdent {
                                    name: implicit_import.value.clone(),
                                    typ: pat.env_type_of(&env),
                                },
                                variable,
                            );
                        }
                        _ => (),
                    }
                }
                // Extract the identifier from each `id@PATTERN` and bind it with `let` before this match
                {
                    for equation in equations {
                        let pat = equation.patterns.first().expect("Pattern");
                        bind_variables(
                            self.0.env,
                            pat,
                            variables.first().expect("Variable"),
                            &mut binder,
                        );
                    }
                }

                let groups = (&groups).into_iter().collect::<Vec<_>>();
                groups
                    .into_iter()
                    .rev()
                    .fold(default, |expr, (key, group)| {
                        let equation_group = group.cloned().collect::<Vec<_>>();
                        self.varcons_compile(expr, variables, key, &equation_group)
                    })
            }
        };
        debug!(
            "Translated: [{}]\n[{}]\nInto: {}",
            variables.iter().format(",\n"),
            equations.iter().format(",\n"),
            expr
        );
        let arena = &self.0.allocator.arena;
        binder.into_expr_ref(arena, expr)
    }

    fn extract_ident(&self, index: usize, pattern: &ast::Pattern<Symbol>) -> TypedIdent<Symbol> {
        get_ident(pattern).unwrap_or_else(|| TypedIdent {
            name: Symbol::from(format!("pattern_{}", index)),
            typ: pattern.env_type_of(&self.0.env),
        })
    }

    // Gather all the identifiers of top level pattern of each of the `patterns` and create a core
    // pattern.
    // Nested patterns are ignored here.
    fn pattern_identifiers<'b, 'p: 'b, I>(&self, patterns: I) -> (Pattern, HashMap<Symbol, Symbol>)
    where
        I: IntoIterator<Item = &'b SpannedPattern<Symbol>>,
    {
        self.pattern_identifiers_(&mut patterns.into_iter())
    }

    fn pattern_identifiers_<'b, 'p: 'b>(
        &self,
        patterns: &mut Iterator<Item = &'b SpannedPattern<Symbol>>,
    ) -> (Pattern, HashMap<Symbol, Symbol>) {
        let mut identifiers: Vec<TypedIdent<Symbol>> = Vec::new();
        let mut record_fields: Vec<(TypedIdent<Symbol>, _)> = Vec::new();
        let mut core_pattern = None;

        // Since we merge all patterns that match on the same thing (variants with the same tag,
        // any record or tuple ...), tuple patterns
        // If a field has already been seen in an earlier pattern we must make sure
        // that the variable bound in this pattern/field gets replaced with the
        // symbol from the earlier pattern
        let mut replacements = HashMap::default();

        fn add_duplicate_ident(
            replacements: &mut HashMap<Symbol, Symbol>,
            record_fields: &mut Vec<(TypedIdent<Symbol>, Option<Symbol>)>,
            field: &Symbol,
            pattern: Option<&SpannedPattern<Symbol>>,
        ) -> bool {
            match record_fields.iter().find(|id| id.0.name == *field).cloned() {
                Some(earlier_var) => {
                    let duplicate = match pattern {
                        Some(ref pattern) => get_ident(&pattern.value).map(|id| id.name),
                        None => Some(field.clone()),
                    };
                    if let Some(duplicate) = duplicate {
                        replacements.insert(duplicate, earlier_var.1.unwrap_or(earlier_var.0.name));
                    }
                    true
                }
                None => false,
            }
        }

        for pattern in patterns {
            match *unwrap_as(&pattern.value) {
                ast::Pattern::Constructor(ref id, ref patterns) => {
                    core_pattern = Some(Pattern::Constructor(id.clone(), Vec::new()));

                    for (i, pattern) in patterns.iter().enumerate() {
                        match identifiers.get(i).map(|i| i.name.clone()) {
                            Some(earlier_var) => {
                                if let Some(duplicate) = get_ident(&pattern.value).map(|id| id.name)
                                {
                                    replacements.insert(duplicate, earlier_var);
                                }
                            }
                            None => identifiers.push(self.extract_ident(i, &pattern.value)),
                        }
                    }
                }
                ast::Pattern::As(..) => unreachable!(),
                ast::Pattern::Ident(ref id) => {
                    if core_pattern.is_none() {
                        core_pattern = Some(Pattern::Ident(id.clone()));
                    }
                }
                ast::Pattern::Tuple { ref typ, ref elems } => {
                    for (i, (elem, field_type)) in elems.iter().zip(typ.row_iter()).enumerate() {
                        if !add_duplicate_ident(
                            &mut replacements,
                            &mut record_fields,
                            &field_type.name,
                            Some(elem),
                        ) {
                            record_fields.push((
                                TypedIdent {
                                    name: field_type.name.clone(),
                                    typ: field_type.typ.clone(),
                                },
                                Some(self.extract_ident(i, &elem.value).name),
                            ));
                        }
                    }
                }
                // Records need to merge the bindings of each of the patterns as we want the core
                // `match` expression to just have one alternative
                //
                // | { x, y = a } -> ..
                // | { z = Some w } -> ...
                // // Binds [x, a, z] as we need to turn this into
                // | { x = x, y = a, z = z } -> match z with ...
                // ```
                ast::Pattern::Record {
                    ref typ,
                    ref fields,
                    ..
                } => {
                    for (i, field) in fields.iter().enumerate() {
                        if !add_duplicate_ident(
                            &mut replacements,
                            &mut record_fields,
                            &field.name.value,
                            field.value.as_ref(),
                        ) {
                            let x = field
                                .value
                                .as_ref()
                                .map(|pattern| self.extract_ident(i, &pattern.value).name);
                            let field_type = remove_aliases_cow(&self.0.env, typ)
                                .row_iter()
                                .find(|f| f.name.name_eq(&field.name.value))
                                .map(|f| f.typ.clone())
                                .unwrap_or_else(|| Type::hole());
                            record_fields.push((
                                TypedIdent {
                                    name: field.name.value.clone(),
                                    typ: field_type,
                                },
                                x,
                            ));
                        }
                    }
                }
                ast::Pattern::Literal(_) | ast::Pattern::Error => (),
            }
        }
        let pattern = match core_pattern {
            Some(mut p) => {
                if let Pattern::Constructor(_, ref mut ids) = p {
                    *ids = identifiers
                }
                p
            }
            None => Pattern::Record(record_fields),
        };
        (pattern, replacements)
    }
}

fn get_ident(pattern: &ast::Pattern<Symbol>) -> Option<TypedIdent<Symbol>> {
    match *pattern {
        ast::Pattern::Ident(ref id) => Some(id.clone()),
        ast::Pattern::As(_, ref pat) => get_ident(&pat.value),
        _ => None,
    }
}

fn unwrap_as(pattern: &ast::Pattern<Symbol>) -> &ast::Pattern<Symbol> {
    match *pattern {
        ast::Pattern::As(_, ref pattern) => unwrap_as(&pattern.value),
        _ => pattern,
    }
}

struct PatternIdentifiers<'a> {
    pattern: &'a Pattern,
    start: usize,
    end: usize,
}

impl<'a> PatternIdentifiers<'a> {
    pub fn new(pattern: &'a Pattern) -> PatternIdentifiers<'a> {
        PatternIdentifiers {
            pattern: pattern,
            start: 0,
            end: match *pattern {
                Pattern::Constructor(_, ref patterns) => patterns.len(),
                Pattern::Record(ref fields) => fields.len(),
                Pattern::Ident(_) | Pattern::Literal(_) => 0,
            },
        }
    }
}

impl<'a> Iterator for PatternIdentifiers<'a> {
    type Item = TypedIdent<Symbol>;

    fn next(&mut self) -> Option<Self::Item> {
        match *self.pattern {
            Pattern::Constructor(_, ref patterns) => {
                if self.start < self.end {
                    let i = self.start;
                    self.start += 1;
                    Some(patterns[i].clone())
                } else {
                    None
                }
            }
            Pattern::Record(ref fields) => {
                if self.start < fields.len() {
                    let field = &fields[self.start];
                    self.start += 1;
                    Some(
                        field
                            .1
                            .as_ref()
                            .map(|name| TypedIdent {
                                name: name.clone(),
                                typ: field.0.typ.clone(),
                            })
                            .unwrap_or_else(|| field.0.clone()),
                    )
                } else {
                    None
                }
            }
            Pattern::Ident(_) | Pattern::Literal(_) => None,
        }
    }
}

impl<'a> DoubleEndedIterator for PatternIdentifiers<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match *self.pattern {
            Pattern::Constructor(_, ref patterns) => {
                if self.start != self.end {
                    self.end -= 1;
                    Some(patterns[self.end].clone())
                } else {
                    None
                }
            }
            Pattern::Record(ref fields) => {
                if self.start != self.end {
                    self.end -= 1;
                    let field = &fields[self.end];
                    Some(
                        field
                            .1
                            .as_ref()
                            .map(|name| TypedIdent {
                                name: name.clone(),
                                typ: field.0.typ.clone(),
                            })
                            .unwrap_or_else(|| field.0.clone()),
                    )
                } else {
                    None
                }
            }
            Pattern::Ident(_) | Pattern::Literal(_) => None,
        }
    }
}

impl<'a> ExactSizeIterator for PatternIdentifiers<'a> {
    fn len(&self) -> usize {
        self.end - self.start
    }
}

#[cfg(all(test, feature = "test"))]
mod tests {
    extern crate gluon_parser as parser;

    use super::*;

    use std::collections::HashMap;

    use base::ast;
    use base::symbol::{Symbol, SymbolModule, Symbols};
    use base::types::TypeCache;

    use core::grammar::ExprParser;

    use vm::RootedThread;

    fn parse_expr(symbols: &mut Symbols, expr_str: &str) -> ast::SpannedExpr<Symbol> {
        self::parser::parse_expr(
            &mut SymbolModule::new("".into(), symbols),
            &TypeCache::new(),
            expr_str,
        )
        .unwrap()
    }

    #[derive(Debug)]
    struct PatternEq<'a>(&'a Expr<'a>);

    impl<'a> fmt::Display for PatternEq<'a> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.0)
        }
    }

    impl<'a> PartialEq<Expr<'a>> for PatternEq<'a> {
        fn eq(&self, other: &Expr<'a>) -> bool {
            let mut map = HashMap::new();
            expr_eq(&mut map, self.0, other)
        }
    }

    fn check(map: &mut HashMap<Symbol, Symbol>, l: &Symbol, r: &Symbol) -> bool {
        map.entry(l.clone()).or_insert_with(|| r.clone()) == r
    }

    fn expr_eq(map: &mut HashMap<Symbol, Symbol>, l: &Expr, r: &Expr) -> bool {
        match (l, r) {
            (&Expr::Match(_, l_alts), &Expr::Match(_, r_alts)) => {
                for (l, r) in l_alts.iter().zip(r_alts) {
                    let eq = match (&l.pattern, &r.pattern) {
                        (
                            &Pattern::Constructor(ref l, ref l_ids),
                            &Pattern::Constructor(ref r, ref r_ids),
                        ) => {
                            check(map, &l.name, &r.name)
                                && l_ids
                                    .iter()
                                    .zip(r_ids)
                                    .all(|(l, r)| check(map, &l.name, &r.name))
                        }
                        (&Pattern::Ident(ref l), &Pattern::Ident(ref r)) => {
                            check(map, &l.name, &r.name)
                        }
                        (&Pattern::Record(ref l), &Pattern::Record(ref r)) => {
                            l.iter().zip(r).all(|(l, r)| {
                                check(map, &l.0.name, &r.0.name)
                                    && match (&l.1, &r.1) {
                                        (&Some(ref l), &Some(ref r)) => check(map, l, r),
                                        (&None, &None) => true,
                                        _ => false,
                                    }
                            })
                        }
                        (&Pattern::Literal(ref l_literal), &Pattern::Literal(ref r_literal)) => {
                            l_literal == r_literal
                        }
                        _ => false,
                    };
                    if !eq || !expr_eq(map, &l.expr, &r.expr) {
                        return false;
                    }
                }
                true
            }
            (&Expr::Const(ref l, _), &Expr::Const(ref r, _)) => l == r,
            (&Expr::Ident(ref l, _), &Expr::Ident(ref r, _)) => check(map, &l.name, &r.name),
            (&Expr::Let(ref lb, l), &Expr::Let(ref rb, r)) => {
                let b = match (&lb.expr, &rb.expr) {
                    (&Named::Expr(le), &Named::Expr(re)) => expr_eq(map, le, re),
                    _ => false,
                };
                check(map, &lb.name.name, &rb.name.name) && b && expr_eq(map, l, r)
            }
            (&Expr::Call(lf, l_args), &Expr::Call(rf, r_args)) => {
                expr_eq(map, lf, rf)
                    && l_args.len() == r_args.len()
                    && l_args.iter().zip(r_args).all(|(l, r)| expr_eq(map, l, r))
            }
            (&Expr::Data(ref l, l_args, ..), &Expr::Data(ref r, r_args, ..)) => {
                check(map, &l.name, &r.name)
                    && l_args.len() == r_args.len()
                    && l_args.iter().zip(r_args).all(|(l, r)| expr_eq(map, l, r))
            }
            _ => false,
        }
    }

    fn check_translation(expr_str: &str, expected_str: &str) {
        let _ = ::env_logger::try_init();

        let mut symbols = Symbols::new();

        let vm = RootedThread::new();
        let env = vm.get_env();
        let translator = Translator::new(&*env);

        let expr = parse_expr(&mut symbols, expr_str);
        let core_expr = translator.translate(&expr);

        let expected_expr = ExprParser::new()
            .parse(&mut symbols, &translator.allocator, expected_str)
            .unwrap();
        assert_deq!(PatternEq(&core_expr), expected_expr);
    }

    #[test]
    fn match_expr() {
        let expr_str = r#"
            let test = 1
            in
            match test with
            | x -> x
        "#;

        let expected_str = " let y = 1 in y ";
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn nested_match_expr() {
        let expr_str = r#"
            match test with
            | Ctor (Ctor x) -> x
        "#;

        let expected_str = r#"
            match test with
            | Ctor p1 ->
                match p1 with
                | Ctor x -> x
                end
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn multiple_alternatives_nested_match_expr() {
        let expr_str = r#"
            match test with
            | Ctor (Ctor x) -> 1
            | Ctor y -> 2
            | z -> 3
        "#;

        let expected_str = r#"
            match test with
            | Ctor p1 ->
                match p1 with
                | Ctor x -> 1
                | y -> 2
                end
            | z -> 3
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn translate_equality_match() {
        let expr_str = r#"
            match m with
            | { l = Some l_val, r = Some r_val } -> eq l_val r_val
            | { l = None, r = None } -> True
            | _ -> False
        "#;

        let expected_str = r#"
            match m with
            | { l = l1, r = r1 } ->
                match l1 with
                | Some l_val ->
                    match r1 with
                    | Some r_val -> eq l_val r_val
                    | _1 -> False
                    end
                | None ->
                    match r1 with
                    | None -> True
                    | _2 -> False
                    end
                | _3 -> False
                end
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_as_pattern() {
        let expr_str = r#"
            match test with
            | x@Test -> x
            | y -> y
        "#;

        let expected_str = "
            let x = test in
            match x with
            | Test -> x
            | _ -> test
            end
        ";
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_as_pattern_on_non_identifier() {
        let expr_str = r#"
            match 1 with
            | x@Test -> x
            | y -> y
        "#;

        let expected_str = "
            let match_pattern = 1 in
            let x = match_pattern in
            match x with
            | Test -> x
            | _ -> match_pattern
            end
        ";
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_as_pattern_multiple() {
        let expr_str = r#"
            match test with
            | x@Test -> x
            | y@Test2 -> y
            | z -> z
        "#;

        let expected_str = "
            let x = test in
            let y = test in
            match test with
            | Test -> x
            | Test2 -> y
            | _ -> test
            end
        ";
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_as_pattern_nested() {
        let expr_str = r#"
            match test with
            | { z = x@Test } -> x
        "#;

        let expected_str = "
            match test with
            | { z = z } ->
                let x = z in
                match z with
                | Test -> x
                end
            end
        ";
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn let_as_pattern_record() {
        let expr_str = r#"
            let x@{ y } = test
            x
        "#;

        let expected_str = "
            let x = test in
            match x with
            | { y } -> x
            end
        ";
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn let_as_pattern_identifier() {
        let expr_str = r#"
            let x@y = 1
            y
        "#;

        let expected_str = "
            let match_pattern = 1 in
            let x = match_pattern in
            match_pattern
        ";
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_int_literal() {
        let expr_str = r#"
            match 2 with
            | 1 -> "one"
            | _ -> "any"
        "#;

        let expected_str = r#"
            let match_pattern = 2 in
            match match_pattern with
            | 1 -> "one"
            | _ -> "any"
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_string_literal() {
        let expr_str = r#"
            let x = "zero" in
            match x with
            | "one" -> 1
            | _ -> 0
        "#;

        let expected_str = r#"
            let x = "zero" in
            match x with
            | "one" -> 1
            | _ -> 0
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_as_literal_pattern() {
        let expr_str = r#"
            match 2 with
            | x@2 -> x
            | _ -> 0
        "#;

        let expected_str = r#"
            let p = 2 in
            let x = p in
            match p with
            | 2 -> x
            | _ -> 0
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn multiple_alternatives_nested_match_expr_with_literal() {
        let expr_str = r#"
            match test with
            | Ctor (Ctor 4) -> 1
            | Ctor y -> 2
            | z -> 3
        "#;

        let expected_str = r#"
            match test with
            | Ctor p1 ->
                match p1 with
                | Ctor p2 ->
                    match p2 with
                    | 4 -> 1
                    end
                | y -> 2
                end
            | z -> 3
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_record_with_literal() {
        let expr_str = r#"
            match { x = 2, y = 3 } with
            | { x = 2, y = 3 } -> "4"
            | _ -> "6"
        "#;

        let expected_str = r#"
            let p = { x = 2, y = 3 } in
            match p with
            | { x = x, y = y } ->
                match x with
                | 2 ->
                    match y with
                    | 3 -> "4"
                    | _ -> "6"
                    end
                | _ -> "6"
                end
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_constructor_with_literal() {
        let expr_str = r#"
            match Test 2 with
            | Other -> 0
            | _ -> 2
        "#;

        let expected_str = r#"
            let p = Test 2 in
            match p with
            | Other -> 0
            | _ -> 2
            end
        "#;
        check_translation(expr_str, expected_str);
    }

    #[test]
    fn match_constructor_with_mutliple_literals() {
        let expr_str = r#"
            type Test = | Test Int String
            match Test 2 "hello" with
            | Test 2 "hello" -> 0
            | _ -> 2
        "#;

        let expected_str = r#"
            let p = Test 2 "hello" in
            match p with
            | Test p0 p1 ->
                match p0 with
                | 2 ->
                    match p1 with
                    | "hello" -> 0
                    | _ -> 2
                    end
                | _ -> 2
                end
            | _ -> 2
            end
        "#;
        check_translation(expr_str, expected_str);
    }
}
