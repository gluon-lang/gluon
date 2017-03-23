extern crate typed_arena;
extern crate smallvec;

use std::fmt;
use std::iter::once;

use itertools::Itertools;

use self::typed_arena::Arena;

use self::smallvec::SmallVec;

use pretty::{self, DocAllocator};

use base::ast::{self, Literal, SpannedExpr, SpannedPattern, TypedIdent, Typed};
use base::pos::{BytePos, ExpansionId, Span};
use base::symbol::Symbol;
use base::types::{ArcType, Type, TypeEnv, PrimitiveEnv, arg_iter};

#[derive(Clone, Debug, PartialEq)]
pub struct Closure<'a> {
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
    Record(Vec<(Symbol, Option<Symbol>)>),
    Ident(TypedIdent<Symbol>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Alternative<'a> {
    pub pattern: Pattern,
    // FIXME hold a &'a Expr<'a>
    pub expr: Expr<'a>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expr<'a> {
    Const(Literal, Span<BytePos>),
    Ident(TypedIdent<Symbol>, Span<BytePos>),
    Call(&'a Expr<'a>, &'a [Expr<'a>]),
    Data(TypedIdent<Symbol>, &'a [Expr<'a>], BytePos, ExpansionId),
    Let(LetBinding<'a>, &'a Expr<'a>),
    Match(&'a Expr<'a>, &'a [Alternative<'a>]),
}

impl<'a> fmt::Display for Expr<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let arena = pretty::Arena::new();
        let mut s = Vec::new();
        self.pretty(&arena).1.render(80, &mut s).unwrap();
        write!(f, "{}", ::std::str::from_utf8(&s).expect("utf-8"))
    }
}

const INDENT: usize = 4;

impl<'a> Expr<'a> {
    pub fn pretty(&'a self,
                  arena: &'a pretty::Arena<'a>)
                  -> pretty::DocBuilder<'a, pretty::Arena<'a>> {
        match *self {
            Expr::Call(f, args) => {
                chain![arena;
                    f.pretty(arena),
                    arena.concat(args.iter().map(|arg| {
                        arena.space().append(arg.pretty(arena))
                    }))
                ]
                    .group()
            }
            Expr::Const(ref literal, _) => {
                match *literal {
                    Literal::Byte(b) => arena.text(format!("b{}", b)),
                    Literal::Char(c) => arena.text(format!("{:?}", c)),
                    Literal::Float(f) => arena.text(format!("{}", f)),
                    Literal::Int(i) => arena.text(format!("{}", i)),
                    Literal::String(ref s) => arena.text(format!("{:?}", s)),
                }
            }
            Expr::Data(ref ctor, ref args, _, _) => {
                chain![arena;
                    ctor.as_ref(),
                    arena.concat(args.iter().map(|arg| {
                        arena.space().append(arg.pretty(arena))
                    }))
                ]
                    .group()
            }
            Expr::Ident(ref id, _) => arena.text(id.as_ref()),
            Expr::Let(ref bind, ref expr) => {
                chain![arena;
                    "let ",
                    match bind.expr {
                        Named::Expr(ref expr) => {
                            chain![arena;
                                bind.name.as_ref(),
                                arena.space(),
                                "=",
                                arena.space(),
                                chain![arena;
                                    expr.pretty(arena),
                                    arena.space()
                                ].nest(INDENT).group()
                            ].group().nest(INDENT)
                        }
                        Named::Recursive(ref closures) => {
                            arena.concat(closures.iter().map(|closure| {
                                chain![arena;
                                    closure.name.as_ref(),
                                    arena.concat(closure.args.iter()
                                        .map(|arg| arena.space().append(arena.text(arg.as_ref())))),
                                    arena.space(),
                                    "=",
                                    arena.space(),
                                    chain![arena;
                                        closure.expr.pretty(arena),
                                        arena.space()
                                    ].nest(INDENT).group()
                                ].group()
                            }))
                        }
                    },
                    arena.newline(),
                    expr.pretty(arena)
                ]
            }
            Expr::Match(expr, alts) => {
                chain![arena;
                    "match ",
                    expr.pretty(arena),
                    " with",
                    arena.newline(),
                    arena.concat(alts.iter().map(|alt| {
                        chain![arena;
                            alt.pattern.pretty(arena),
                            " ->",
                            arena.space(),
                            alt.expr.pretty(arena).nest(INDENT).group()
                        ].nest(INDENT)
                    }).intersperse(arena.newline()))
                ]
                    .group()
            }
        }
    }

    pub fn span(&self) -> Span<BytePos> {
        match *self {
            Expr::Call(expr, args) => {
                let span = expr.span();
                Span::with_id(span.start,
                              args.last().unwrap().span().end,
                              span.expansion_id)
            }
            Expr::Const(_, span) => span,
            Expr::Data(_, args, span_start, expansion_id) => {
                let span_end = args.last()
                    .map_or(span_start, |arg| arg.span().end);
                Span::with_id(span_start, span_end, expansion_id)
            }
            Expr::Ident(_, span) => span,
            Expr::Let(ref let_binding, ref body) => {
                let span_end = body.span();
                Span::with_id(let_binding.span_start, span_end.end, span_end.expansion_id)
            }
            Expr::Match(expr, alts) => {
                let span_start = expr.span();
                Span::with_id(span_start.start,
                              alts.last().unwrap().expr.span().end,
                              span_start.expansion_id)
            }
        }
    }
}

impl Pattern {
    pub fn pretty<'a>(&'a self,
                      arena: &'a pretty::Arena<'a>)
                      -> pretty::DocBuilder<'a, pretty::Arena<'a>> {
        match *self {
            Pattern::Constructor(ref ctor, ref args) => {
                chain![arena;
                    ctor.as_ref(),
                    arena.concat(args.iter().map(|arg| {
                        arena.space().append(arg.as_ref())
                    }))
                ]
            }
            Pattern::Ident(ref id) => arena.text(id.as_ref()),
            Pattern::Record(ref fields) => {
                chain![arena;
                    "{",
                    arena.concat(fields.iter().map(|&(ref field, ref value)| {
                        chain![arena;
                            arena.space(),
                            arena.text(field.as_ref()),
                            match *value {
                                Some(ref value) => {
                                    chain![arena;
                                        "=",
                                        arena.space(),
                                        value.as_ref()
                                    ]
                                }
                                None => arena.nil(),
                            }
                        ]
                    }).intersperse(arena.text(","))).nest(INDENT),
                    arena.space(),
                    "}"
                ]
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

pub struct Allocator<'a, 'e> {
    arena: Arena<Expr<'a>>,
    alternative_arena: Arena<Alternative<'a>>,
    env: &'e PrimitiveEnv,
    dummy_symbol: TypedIdent<Symbol>,
}

impl<'a, 'e> Allocator<'a, 'e> {
    pub fn new(env: &'e PrimitiveEnv) -> Allocator<'a, 'e> {
        Allocator {
            arena: Arena::new(),
            alternative_arena: Arena::new(),
            env: env,
            dummy_symbol: TypedIdent::new(Symbol::from("")),
        }
    }

    pub fn translate_alloc(&'a self, expr: &SpannedExpr<Symbol>) -> &'a Expr<'a> {
        self.arena.alloc(self.translate(expr))
    }

    pub fn translate(&'a self, expr: &SpannedExpr<Symbol>) -> Expr<'a> {
        let mut current = expr;
        let mut lets = Vec::new();
        while let ast::Expr::LetBindings(ref binds, ref tail) = current.value {
            lets.push((current.span.start, binds));
            current = tail;
        }
        let tail = self.translate_(current);
        lets.iter().rev().fold(tail, |result, &(span_start, ref binds)| {
            self.translate_let(binds, result, span_start)
        })
    }

    fn translate_(&'a self, expr: &SpannedExpr<Symbol>) -> Expr<'a> {
        let arena = &self.arena;
        match expr.value {
            ast::Expr::App(ref function, ref args) => {
                let new_args: SmallVec<[_; 16]> =
                    args.iter().map(|arg| self.translate(arg)).collect();
                match function.value {
                    ast::Expr::Ident(ref id) if is_constructor(&id.name) => {
                        let typ = expr.env_type_of(&self.env);
                        self.new_data_constructor(typ, id, new_args, expr.span)
                    }
                    _ => {
                        Expr::Call(self.translate_alloc(function),
                                   arena.alloc_extend(new_args.into_iter()))
                    }
                }
            }
            ast::Expr::Array(ref array) => {
                let exprs: SmallVec<[_; 16]> =
                    array.exprs.iter().map(|expr| self.translate(expr)).collect();
                Expr::Data(TypedIdent {
                               name: self.dummy_symbol.name.clone(),
                               typ: array.typ.clone(),
                           },
                           arena.alloc_extend(exprs.into_iter()),
                           expr.span.start,
                           expr.span.expansion_id)
            }
            ast::Expr::Block(ref exprs) => {
                let (last, prefix) = exprs.split_last().unwrap();
                let result = self.translate(last);
                prefix.iter().rev().fold(result, |result, expr| {
                    Expr::Let(LetBinding {
                                  name: self.dummy_symbol.clone(),
                                  expr: Named::Expr(self.translate_alloc(expr)),
                                  span_start: expr.span.start,
                              },
                              arena.alloc(result))
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
                let alts: SmallVec<[_; 2]> = collect![Alternative {
                                 pattern: Pattern::Constructor(self.bool_constructor(true),
                                                               vec![]),
                                 expr: self.translate(if_true),
                             },
                             Alternative {
                                 pattern: Pattern::Constructor(self.bool_constructor(false),
                                                               vec![]),
                                 expr: self.translate(if_false),
                             }];
                Expr::Match(self.translate_alloc(pred),
                            self.alternative_arena.alloc_extend(alts.into_iter()))
            }
            ast::Expr::Infix(ref l, ref op, ref r) => {
                let args: SmallVec<[_; 2]> = collect![self.translate(l), self.translate(r)];
                Expr::Call(arena.alloc(Expr::Ident(op.value.clone(), op.span)),
                           arena.alloc_extend(args.into_iter()))
            }
            ast::Expr::Lambda(ref lambda) => {
                self.new_lambda(lambda.id.clone(),
                                lambda.args.clone(),
                                self.translate_alloc(&lambda.body),
                                expr.span)
            }
            ast::Expr::LetBindings(ref binds, ref tail) => {
                self.translate_let(binds, self.translate(tail), expr.span.start)
            }
            ast::Expr::Literal(ref literal) => Expr::Const(literal.clone(), expr.span),
            ast::Expr::Match(ref expr, ref alts) => {
                let expr = self.translate(expr);
                let alts: Vec<_> = alts.iter()
                    .map(|alt| {
                        (MatchPattern::Pattern(&alt.pattern), self.translate_alloc(&alt.expr))
                    })
                    .collect();
                PatternTranslator(self).translate(expr, &alts)
            }
            // expr.projection
            // =>
            // match expr with
            // | { projection } -> projection
            ast::Expr::Projection(ref projected_expr, ref projection, ref projected_type) => {
                let alt = Alternative {
                    pattern: Pattern::Record(vec![(projection.clone(), None)]),
                    expr: Expr::Ident(TypedIdent {
                                          name: projection.clone(),
                                          typ: projected_type.clone(),
                                      },
                                      expr.span),
                };
                Expr::Match(self.translate_alloc(projected_expr),
                            self.alternative_arena.alloc_extend(once(alt)))
            }
            ast::Expr::Record { ref typ, ref exprs, .. } => {
                let mut last_span = expr.span;
                let args: SmallVec<[_; 16]> = exprs.iter()
                    .map(|field| match field.value {
                        Some(ref expr) => {
                            last_span = expr.span;
                            self.translate(expr)
                        }
                        None => Expr::Ident(TypedIdent::new(field.name.clone()), last_span),
                    })
                    .collect();
                Expr::Data(TypedIdent {
                               name: self.dummy_symbol.name.clone(),
                               typ: typ.clone(),
                           },
                           arena.alloc_extend(args.into_iter()),
                           expr.span.start,
                           expr.span.expansion_id)
            }
            ast::Expr::Tuple(ref exprs) => {
                assert!(exprs.len() == 0, "Only unit is handled at the moment");
                let args: SmallVec<[_; 16]> = exprs.iter()
                    .map(|expr| self.translate(expr))
                    .collect();
                Expr::Data(TypedIdent {
                               name: self.dummy_symbol.name.clone(),
                               typ: Type::unit(),
                           },
                           arena.alloc_extend(args.into_iter()),
                           expr.span.start,
                           expr.span.expansion_id)
            }
            ast::Expr::TypeBindings(_, ref expr) => self.translate(expr),
            ast::Expr::Error => panic!("ICE: Error expression found in the compiler"),
        }
    }

    fn translate_let(&'a self,
                     binds: &[ast::ValueBinding<Symbol>],
                     tail: Expr<'a>,
                     span_start: BytePos)
                     -> Expr<'a> {
        let arena = &self.arena;
        let is_recursive = binds.iter().all(|bind| bind.args.len() > 0);
        if is_recursive {
            let closures = binds.iter()
                .map(|bind| {
                    Closure {
                        name: match bind.name.value {
                            ast::Pattern::Ident(ref id) => id.clone(),
                            _ => unreachable!(),
                        },
                        args: bind.args.clone(),
                        expr: self.translate_alloc(&bind.expr),
                    }
                })
                .collect();
            Expr::Let(LetBinding {
                          // TODO
                          name: self.dummy_symbol.clone(),
                          expr: Named::Recursive(closures),
                          span_start: span_start,
                      },
                      arena.alloc(tail))
        } else {
            binds.iter().rev().fold(tail, |tail, bind| {
                let name = match bind.name.value {
                    ast::Pattern::Ident(ref id) => id.clone(),
                    _ => {
                        let bind_expr = self.translate(&bind.expr);
                        let tail = &*arena.alloc(tail);
                        return PatternTranslator(self)
                            .translate(bind_expr, &[(MatchPattern::Pattern(&bind.name), tail)]);
                    }
                };
                let named = if bind.args.is_empty() {
                    Named::Expr(self.translate_alloc(&bind.expr))
                } else {
                    Named::Recursive(vec![Closure {
                                              name: name.clone(),
                                              args: bind.args.clone(),
                                              expr: self.translate_alloc(&bind.expr),
                                          }])
                };
                Expr::Let(LetBinding {
                              name: name,
                              expr: named,
                              span_start: bind.expr.span.start,
                          },
                          arena.alloc(tail))
            })
        }
    }

    fn bool_constructor(&self, variant: bool) -> TypedIdent<Symbol> {
        let b = self.env.get_bool();
        match **b {
            Type::Alias(ref alias) => {
                match **alias.typ() {
                    Type::Variant(ref variants) => {
                        TypedIdent {
                            name: variants.row_iter().nth(variant as usize).unwrap().name.clone(),
                            typ: b.clone(),
                        }
                    }
                    _ => panic!(),
                }
            }
            _ => panic!(),
        }
    }

    fn new_data_constructor(&'a self,
                            expr_type: ArcType,
                            id: &TypedIdent<Symbol>,
                            mut new_args: SmallVec<[Expr<'a>; 16]>,
                            span: Span<BytePos>)
                            -> Expr<'a> {
        let arena = &self.arena;
        let typ = expr_type;
        let unapplied_args: Vec<_>;
        // If the constructor is not fully applied we retrieve the type of the data
        // by iterating through the arguments. If it is fully applied the arg_iter
        // has no effect and `typ` itself will be used
        let data_type;
        {
            let mut args = arg_iter(&typ);
            unapplied_args = args.by_ref()
                .enumerate()
                .map(|(i, arg)| {
                    TypedIdent {
                        name: Symbol::from(format!("#{}", i)),
                        typ: arg.clone(),
                    }
                })
                .collect();
            data_type = args.typ.clone();
        }
        new_args.extend(unapplied_args.iter()
            .map(|arg| Expr::Ident(arg.clone(), span)));
        let data = Expr::Data(TypedIdent {
                                  name: id.name.clone(),
                                  typ: data_type,
                              },
                              arena.alloc_extend(new_args.into_iter()),
                              span.start,
                              span.expansion_id);
        if unapplied_args.is_empty() {
            data
        } else {
            self.new_lambda(TypedIdent {
                                name: Symbol::from(format!("${}", id.name)),
                                typ: typ,
                            },
                            unapplied_args,
                            arena.alloc(data),
                            span)
        }
    }

    fn new_lambda(&'a self,
                  name: TypedIdent<Symbol>,
                  args: Vec<TypedIdent<Symbol>>,
                  body: &'a Expr<'a>,
                  span: Span<BytePos>)
                  -> Expr<'a> {
        let arena = &self.arena;
        Expr::Let(LetBinding {
                      name: name.clone(),
                      expr: Named::Recursive(vec![Closure {
                                                      name: name.clone(),
                                                      args: args,
                                                      expr: body,
                                                  }]),
                      span_start: span.start,
                  },
                  arena.alloc(Expr::Ident(name, span)))
    }
}

impl<'a> Typed for Expr<'a> {
    type Ident = Symbol;

    fn env_type_of(&self, env: &TypeEnv) -> ArcType<Self::Ident> {
        match *self {
            Expr::Call(expr, args) => get_return_type(env, &expr.env_type_of(env), args.len()),
            Expr::Const(ref literal, _) => literal.env_type_of(env),
            Expr::Data(ref id, _, _, _) => id.typ.clone(),
            Expr::Ident(ref id, _) => id.typ.clone(),
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

    let (_, ret) = function_type.as_function().unwrap_or_else(|| {
        panic!("Call expression with a non function type `{}`",
               function_type)
    });
    get_return_type(env, ret, arg_count - 1)
}

pub struct PatternTranslator<'a, 'e: 'a>(&'a Allocator<'a, 'e>);

#[derive(Clone)]
enum MatchPattern<'p> {
    Pattern(&'p SpannedPattern<Symbol>),
    Wildcard(TypedIdent<Symbol>),
}

impl<'a, 'e> PatternTranslator<'a, 'e> {
    fn translate<'p>(&mut self,
                     matched_expr: Expr<'a>,
                     alts: &[(MatchPattern<'p>, &'a Expr<'a>)])
                     -> Expr<'a> {
        use std::collections::BTreeMap;

        #[derive(Ord, PartialOrd, Eq, PartialEq)]
        enum Matcher<'s, Id: 's> {
            Tag(&'s Id),
            Wildcard,
        }

        let mut groups = BTreeMap::new();
        for alt in alts {
            match alt.0 {
                MatchPattern::Pattern(ref first) => {
                    match first.value {
                        ast::Pattern::Constructor(ref id, _) => {
                            groups.entry(Matcher::Tag(&id.name)).or_insert(Vec::new()).push(alt);
                        }
                        ast::Pattern::Record { .. } |
                        ast::Pattern::Ident(_) => {
                            groups.entry(Matcher::Wildcard).or_insert(Vec::new());
                            for (_, group) in &mut groups {
                                group.push(alt);
                            }
                        }
                    }
                }
                MatchPattern::Wildcard(_) => {
                    groups.entry(Matcher::Wildcard).or_insert(Vec::new());
                    for (_, group) in &mut groups {
                        group.push(alt);
                    }
                }
            }
        }

        let new_alts = groups.into_iter()
            .map(|(_, alts)| {
                let pattern = pattern_identifiers(alts.iter()
                    .filter_map(|alt| match alt.0 {
                        MatchPattern::Pattern(pattern) => Some(&pattern.value),
                        MatchPattern::Wildcard(_) => None,
                    }));

                let mut expr: Option<&'a Expr<'a>> = None;
                for (i, expr_ident) in PatternIdentifiers(&pattern, 0).enumerate() {
                    let mut nest_expr = expr.take();
                    let patterns: Vec<_> = alts.iter()
                        .map(|alt| {
                            let pattern = match alt.0 {
                                MatchPattern::Pattern(ref pattern) => {
                                    match pattern.value { 
                                        ast::Pattern::Constructor(_, ref patterns) => {
                                            MatchPattern::Pattern(&patterns[i])
                                        }
                                        ast::Pattern::Record { ref fields, .. } => {
                                            match fields[i].1 {
                                                Some(ref pattern) => MatchPattern::Pattern(pattern),
                                                None => {
                                                    MatchPattern::Wildcard(TypedIdent {
                                                        name: fields[i].0.clone(),
                                                        // FIXME
                                                        typ: Type::hole(),
                                                    })
                                                }
                                            }
                                        }
                                        ast::Pattern::Ident(..) => panic!(),
                                    }
                                }
                                MatchPattern::Wildcard(_) => panic!(),
                            };
                            (pattern, nest_expr.take().unwrap_or(alt.1))
                        })
                        .collect();
                    let next_expr =
                        self.translate(Expr::Ident(expr_ident.clone(),
                                                   Span::new(0.into(), 0.into())),
                                       &patterns);
                    expr = Some(self.0.arena.alloc(next_expr));
                }
                Alternative {
                    pattern: pattern,
                    expr: expr.unwrap_or(alts[0].1).clone(),
                }
            })
            .collect::<Vec<_>>();

        Expr::Match(self.0.arena.alloc(matched_expr),
                    self.0.alternative_arena.alloc_extend(new_alts.into_iter()))
    }
}

struct PatternIdentifiers<'a>(&'a Pattern, usize);

impl<'a> Iterator for PatternIdentifiers<'a> {
    type Item = TypedIdent<Symbol>;

    fn next(&mut self) -> Option<Self::Item> {
        match *self.0 {
            Pattern::Constructor(_, ref patterns) => {
                if self.1 < patterns.len() {
                    let i = self.1;
                    self.1 += 1;
                    Some(patterns[i].clone())
                } else {
                    None
                }
            }
            Pattern::Record(ref fields) => {
                if self.1 < fields.len() {
                    let field = &fields[self.1];
                    self.1 += 1;
                    Some(TypedIdent::new(field.1.as_ref().unwrap_or(&field.0).clone()))
                } else {
                    None
                }
            }
            Pattern::Ident(_) => None,
        }
    }
}

fn pattern_identifiers<'a, I>(patterns: I) -> Pattern
    where I: IntoIterator<Item = &'a ast::Pattern<Symbol>>,
{
    fn extract_ident(index: usize, pattern: &ast::Pattern<Symbol>) -> TypedIdent<Symbol> {
        match *pattern {
            ast::Pattern::Ident(ref id) => id.clone(),
            _ => TypedIdent::new(Symbol::from(format!("pattern_{}", index))),
        }
    }

    let mut identifiers = Vec::new();
    let mut record_fields: Vec<(Symbol, Option<Symbol>)> = Vec::new();
    let mut ident = None;

    for pattern in patterns {
        match *pattern {
            ast::Pattern::Constructor(ref id, ref patterns) => {
                identifiers.extend(patterns.iter()
                    .enumerate()
                    .map(|(i, pattern)| extract_ident(i, &pattern.value)));
                // Just extract the patterns of the first constructor found
                return Pattern::Constructor(id.clone(), identifiers);
            }
            ast::Pattern::Ident(ref id) => ident = Some(id.clone()),
            ast::Pattern::Record { ref fields, .. } => {
                for (i, field) in fields.iter().enumerate() {
                    // Don't add one field twice
                    if identifiers.iter().all(|id| id.name != field.0) {
                        let x = field.1
                            .as_ref()
                            .map(|pattern| extract_ident(i, &pattern.value).name);
                        record_fields.push((field.0.clone(), x));
                    }
                }
            }
        }
    }
    match ident {
        Some(ident) => Pattern::Ident(ident),
        None => Pattern::Record(record_fields),
    }
}

#[cfg(test)]
mod tests {
    extern crate gluon_parser as parser;

    use super::*;

    use std::collections::HashMap;

    use base::pos::{self, Span, Spanned};
    use base::symbol::{SymbolModule, Symbols};

    use self::parser::parse_expr;

    use vm::RootedThread;

    type SpExpr = ast::SpannedExpr<Symbol>;

    pub fn no_loc<T>(value: T) -> Spanned<T, BytePos> {
        pos::spanned(Span::default(), value)
    }

    pub fn int(i: i64) -> SpExpr {
        no_loc(ast::Expr::Literal(ast::Literal::Int(i)))
    }

    pub fn id(s: Symbol) -> SpExpr {
        no_loc(ast::Expr::Ident(ast::TypedIdent::new(s)))
    }

    pub fn match_(e: SpExpr, alts: Vec<(ast::Pattern<Symbol>, SpExpr)>) -> SpExpr {
        no_loc(ast::Expr::Match(Box::new(e),
                                alts.into_iter()
                                    .map(|(p, e)| {
                                        ast::Alternative {
                                            pattern: no_loc(p),
                                            expr: e,
                                        }
                                    })
                                    .collect()))
    }

    struct CoreArena<'a, 'e: 'a, 'c>(&'a Allocator<'a, 'e>, &'c mut Symbols);

    impl<'a, 'e, 'c> CoreArena<'a, 'e, 'c> {
        fn id(&mut self, s: &str) -> &'a Expr<'a> {
            self.0.arena.alloc(Expr::Ident(ast::TypedIdent::new(self.1.symbol(s)), Span::default()))
        }

        fn match_(&mut self, e: &'a Expr<'a>, alts: Vec<Alternative<'a>>) -> &'a Expr<'a> {
            self.0
                .arena
                .alloc(Expr::Match(e, self.0.alternative_arena.alloc_extend(alts.into_iter())))
        }

        fn int(&mut self, i: i64) -> &'a Expr<'a> {
            self.0.arena.alloc(Expr::Const(ast::Literal::Int(i), Span::default()))
        }
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
                        (&Pattern::Constructor(ref l, ref l_ids),
                         &Pattern::Constructor(ref r, ref r_ids)) => {
                            check(map, &l.name, &r.name) &&
                            l_ids.iter().zip(r_ids).all(|(l, r)| check(map, &l.name, &r.name))
                        }
                        (&Pattern::Ident(ref l), &Pattern::Ident(ref r)) => {
                            check(map, &l.name, &r.name)
                        }
                        (&Pattern::Record(ref l), &Pattern::Record(ref r)) => {
                            l.iter()
                                .zip(r)
                                .all(|(l, r)| {
                                    check(map, &l.0, &r.0) &&
                                    match (&l.1, &r.1) {
                                        (&Some(ref l), &Some(ref r)) => check(map, l, r),
                                        (&None, &None) => true,
                                        _ => false,
                                    }
                                })
                        }
                        _ => false,
                    };
                    if !eq || !expr_eq(map, &l.expr, &r.expr) {
                        return false;
                    }
                }
                true
            }
            (&Expr::Ident(ref l, _), &Expr::Ident(ref r, _)) => check(map, &l.name, &r.name),
            _ => false,
        }
    }

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

    #[test]
    fn match_expr() {
        let _ = ::env_logger::init();

        let mut symbols = Symbols::new();

        let vm = RootedThread::new();
        let env = vm.get_env();
        let arena = Allocator::new(&*env);

        let x = symbols.symbol("x");
        let expr = match_(id(symbols.symbol("test")),
                          vec![(ast::Pattern::Ident(TypedIdent::new(x.clone())), int(1))]);
        let core_expr = arena.translate(&expr);

        let mut arena = CoreArena(&arena, &mut symbols);

        let test = arena.id("test");
        let one = arena.int(1);
        let expected_expr = arena.match_(test,
                                         vec![Alternative {
                                                  pattern: Pattern::Ident(TypedIdent::new(x)),
                                                  expr: one.clone(),
                                              }]);
        assert_deq!(core_expr, *expected_expr);
    }

    #[test]
    fn nested_match_expr() {
        let _ = ::env_logger::init();

        let mut symbols = Symbols::new();

        let vm = RootedThread::new();
        let env = vm.get_env();
        let arena = Allocator::new(&*env);

        let expr_str = r#"
            match test with
            | Ctor (Ctor x) -> x
        "#;
        let expr = parse_expr(&mut SymbolModule::new("".into(), &mut symbols), expr_str).unwrap();
        let core_expr = arena.translate(&expr);

        let x = symbols.symbol("x");
        let ctor = symbols.symbol("Ctor");

        let mut arena = CoreArena(&arena, &mut symbols);

        let test = arena.id("test");
        let one = arena.int(1);
        let expected_expr = arena.match_(test,
                                         vec![Alternative {
                                                  pattern: Pattern::Ident(TypedIdent::new(x)),
                                                  expr: one.clone(),
                                              }]);
        assert_deq!(PatternEq(&core_expr), *expected_expr);
    }
}
