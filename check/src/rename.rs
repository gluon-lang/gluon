use std::fmt;
use std::mem;

use itertools::Itertools;

use base::ast::{self, DisplayEnv, Do, Expr, Literal, MutVisitor, Pattern, SpannedExpr, Typed,
                TypedIdent};
use base::error::Errors;
use base::fnv::FnvMap;
use base::kind::{ArcKind, Kind, KindEnv};
use base::metadata::{Metadata, MetadataEnv};
use base::pos::{self, BytePos, Span, Spanned};
use base::scoped_map::ScopedMap;
use base::symbol::{Symbol, SymbolModule, SymbolRef};
use base::types::{self, Alias, ArcType, ArgType, RecordSelector, Type, TypeEnv};
use unify_type::{State, TypeError};
use unify::{Error as UnifyError, Unifiable, Unifier, UnifierState};
use substitution::Substitution;

pub type Error = Errors<Spanned<RenameError, BytePos>>;

#[derive(Clone, Debug, PartialEq)]
pub enum RenameError {
    NoMatchingType {
        symbol: String,
        expected: ArcType,
        possible_types: Vec<(Option<Span<BytePos>>, ArcType)>,
    },
    /// An implicit paramter were not possible to resolve
    UnableToResolveImplicit(ArcType<Symbol>),
}

impl fmt::Display for RenameError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            RenameError::NoMatchingType {
                ref symbol,
                ref expected,
                ref possible_types,
            } => {
                writeln!(
                    f,
                    "Could not resolve a binding for `{}` with type `{}`",
                    symbol, expected
                )?;
                writeln!(f, "Possibilities:")?;
                for &(ref span, ref typ) in possible_types {
                    match *span {
                        Some(ref span) => writeln!(f, "{} at {}", typ, span.start)?,
                        None => writeln!(f, "{} at 'global'", typ)?,
                    }
                }
                Ok(())
            }
            RenameError::UnableToResolveImplicit(ref typ) => write!(
                f,
                "Implicit parameter with type `{}` could not be resolved",
                typ
            ),
        }
    }
}

trait RenameEnv: MetadataEnv + TypeEnv {}

impl<T> RenameEnv for T
where
    T: ?Sized + MetadataEnv + TypeEnv,
{
}

struct Environment<'b> {
    env: &'b RenameEnv,
    stack: ScopedMap<Symbol, (Symbol, Span<BytePos>, ArcType)>,
    stack_types: ScopedMap<Symbol, Alias<Symbol, ArcType>>,
}

impl<'a> KindEnv for Environment<'a> {
    fn find_kind(&self, _type_name: &SymbolRef) -> Option<ArcKind> {
        None
    }
}

impl<'a> TypeEnv for Environment<'a> {
    fn find_type(&self, id: &SymbolRef) -> Option<&ArcType> {
        self.stack
            .get(id)
            .map(|t| &t.2)
            .or_else(|| self.env.find_type(id))
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>> {
        self.stack_types
            .get(id)
            .or_else(|| self.env.find_type_info(id))
    }

    fn find_record(
        &self,
        _fields: &[Symbol],
        _selector: RecordSelector,
    ) -> Option<(ArcType, ArcType)> {
        None
    }
}

pub fn rename<E>(
    symbols: &mut SymbolModule,
    env: &E,
    expr: &mut SpannedExpr<Symbol>,
) -> Result<(), Error>
where
    E: MetadataEnv + TypeEnv,
{
    use base::resolve;

    enum TailCall {
        TailCall,
        Return,
    }

    #[derive(Clone, Copy, Debug)]
    enum ImplicitKind<'a> {
        Always,
        Binding(&'a Metadata),
    }

    struct RenameVisitor<'a: 'b, 'b> {
        symbols: &'b mut SymbolModule<'a>,
        metadata: FnvMap<Symbol, Metadata>,
        env: Environment<'b>,
        errors: Error,
        subs: Substitution<ArcType>,
    }

    impl<'a, 'b> RenameVisitor<'a, 'b> {
        fn find_fields(&self, typ: &ArcType) -> Vec<types::Field<Symbol, ArcType>> {
            // Walk through all type aliases
            let record = resolve::remove_aliases(&self.env, typ.remove_forall().clone());
            record.row_iter().cloned().collect()
        }

        fn new_pattern(&mut self, pattern: &mut ast::SpannedPattern<Symbol>) {
            match pattern.value {
                Pattern::Record {
                    ref mut fields,
                    ref types,
                    ref typ,
                } => {
                    let field_types = self.find_fields(typ);
                    for field in fields {
                        match field.value {
                            Some(ref mut pat) => self.new_pattern(pat),
                            None => {
                                if let Some(field_type) = field_types
                                    .iter()
                                    .find(|field_type| field_type.name.name_eq(&field.name.value))
                                {
                                    let id = field.name.value.clone();
                                    let pat = Pattern::Ident(TypedIdent {
                                        name: self.stack_var(
                                            id,
                                            pattern.span,
                                            field_type.typ.clone(),
                                        ),
                                        typ: field_type.typ.clone(),
                                    });
                                    field.value = Some(pos::spanned(field.name.span, pat));
                                }
                            }
                        }
                    }

                    let record_type = resolve::remove_aliases(&self.env, typ.clone()).clone();
                    for ast_field in types {
                        let field_type = record_type
                            .remove_forall()
                            .type_field_iter()
                            .find(|field| field.name.name_eq(&ast_field.name.value))
                            .unwrap_or_else(|| {
                                panic!(
                                    "ICE: Type `{}` does not have type field `{}`",
                                    record_type, ast_field.name.value
                                )
                            });
                        self.stack_type(
                            ast_field.name.value.clone(),
                            pattern.span,
                            &field_type.typ,
                        );
                    }
                }
                Pattern::Ident(ref mut id) => {
                    let new_name = self.stack_var(id.name.clone(), pattern.span, id.typ.clone());
                    id.name = new_name;
                }
                Pattern::As(ref mut id, ref mut pat) => {
                    let typ = pat.env_type_of(&self.env);
                    let new_name = self.stack_var(id.clone(), pattern.span, typ);
                    *id = new_name;
                    self.new_pattern(pat)
                }
                Pattern::Tuple { ref mut elems, .. } => for elem in elems {
                    self.new_pattern(elem);
                },
                Pattern::Constructor(_, ref mut args) => for arg in args {
                    self.new_pattern(arg);
                },
                Pattern::Literal(_) | Pattern::Error => (),
            }
        }

        fn stack_var(&mut self, id: Symbol, span: Span<BytePos>, typ: ArcType) -> Symbol {
            let old_id = id.clone();
            let name = self.symbols.string(&id).to_owned();
            let new_id = self.symbols.symbol(format!("{}:{}", name, span.start));
            debug!(
                "Rename binding `{}` = `{}` `{}`",
                self.symbols.string(&old_id),
                self.symbols.string(&new_id),
                typ
            );
            self.env.stack.insert(old_id, (new_id.clone(), span, typ));
            new_id
        }

        fn stack_type(&mut self, id: Symbol, span: Span<BytePos>, alias: &Alias<Symbol, ArcType>) {
            // Insert variant constructors into the local scope
            let aliased_type = alias.typ();
            if let Type::Variant(ref row) = **aliased_type.remove_forall() {
                for field in row.row_iter().cloned() {
                    self.env
                        .stack
                        .insert(field.name.clone(), (field.name, span, field.typ));
                }
            }

            // FIXME: Workaround so that both the types name in this module and its global
            // name are imported. Without this aliases may not be traversed properly
            self.env
                .stack_types
                .insert(alias.name.clone(), alias.clone());
            self.env.stack_types.insert(id, alias.clone());
        }

        /// Renames `id` to the unique identifier which have the type `expected`
        /// Returns `Some(new_id)` if renaming was necessary or `None` if no renaming was necessary
        /// as `id` was currently unique (#Int+, #Float*, etc)
        fn rename(&self, id: &Symbol, expected: &ArcType) -> Result<Option<Symbol>, RenameError> {
            let locals = self.env.stack.get_all(id);
            let candidates = || {
                locals.iter().flat_map(|bindings| {
                    bindings
                        .iter()
                        .rev()
                        .map(|bind| (&bind.0, Some(&bind.1), &bind.2))
                })
            };
            // If there is a single binding (or no binding in case of primitives such as #Int+)
            // there is no need to check for equivalency as typechecker couldnt have infered a
            // different binding
            if candidates().count() <= 1 {
                return Ok(candidates().next().map(|tup| tup.0.clone()));
            }
            candidates()
                .find(|tup| equivalent(&self.env, tup.2.remove_forall(), expected.remove_forall()))
                .map(|tup| Some(tup.0.clone()))
                .ok_or_else(|| RenameError::NoMatchingType {
                    symbol: String::from(self.symbols.string(id)),
                    expected: expected.clone(),
                    possible_types: candidates()
                        .map(|tup| (tup.1.cloned(), tup.2.clone()))
                        .collect(),
                })
        }

        fn rename_expr(&mut self, expr: &mut SpannedExpr<Symbol>) -> Result<TailCall, RenameError> {
            match expr.value {
                Expr::Ident(ref mut id) => if let Some(new_id) = self.rename(&id.name, &id.typ)? {
                    debug!("Rename identifier {} = {}", id.name, new_id);
                    id.name = new_id;
                },
                Expr::Record {
                    ref mut typ,
                    ref mut exprs,
                    ref mut base,
                    ..
                } => {
                    let field_types = self.find_fields(typ);
                    for (field, expr_field) in field_types.iter().zip(exprs) {
                        match expr_field.value {
                            Some(ref mut expr) => self.visit_expr(expr),
                            None => if let Some(new_id) =
                                self.rename(&expr_field.name.value, &field.typ)?
                            {
                                debug!("Rename record field {} = {}", expr_field.name, new_id);
                                expr_field.value = Some(pos::spanned(
                                    expr_field.name.span,
                                    Expr::Ident(TypedIdent {
                                        name: new_id,
                                        typ: field.typ.clone(),
                                    }),
                                ));
                            },
                        }
                    }

                    if let Some(ref mut base) = *base {
                        self.visit_expr(base);
                    }
                }
                Expr::Infix(ref mut lhs, ref mut op, ref mut rhs) => {
                    if let Some(new_id) = self.rename(&op.value.name, &op.value.typ)? {
                        debug!(
                            "Rename {} = {}",
                            self.symbols.string(&op.value.name),
                            self.symbols.string(&new_id)
                        );
                        op.value.name = new_id;
                    }
                    self.visit_expr(lhs);
                    self.visit_expr(rhs);
                }
                Expr::Match(ref mut expr, ref mut alts) => {
                    self.visit_expr(expr);
                    for alt in alts {
                        self.env.stack_types.enter_scope();
                        self.env.stack.enter_scope();
                        self.new_pattern(&mut alt.pattern);
                        self.visit_expr(&mut alt.expr);
                        self.env.stack.exit_scope();
                        self.env.stack_types.exit_scope();
                    }
                }
                Expr::LetBindings(ref mut bindings, ref mut expr) => {
                    self.env.stack_types.enter_scope();
                    self.env.stack.enter_scope();
                    let is_recursive = bindings.iter().all(|bind| !bind.args.is_empty());
                    for bind in bindings.iter_mut() {
                        if !is_recursive {
                            self.visit_expr(&mut bind.expr);
                        }
                        self.new_pattern(&mut bind.name);
                    }
                    if is_recursive {
                        for bind in bindings {
                            self.env.stack.enter_scope();
                            for (typ, arg) in types::arg_iter(bind.resolved_type.remove_forall())
                                .zip(&mut bind.args)
                            {
                                arg.value.name =
                                    self.stack_var(arg.value.name.clone(), expr.span, typ.clone());
                            }
                            self.visit_expr(&mut bind.expr);
                            self.env.stack.exit_scope();
                        }
                    }
                    return Ok(TailCall::TailCall);
                }
                Expr::Lambda(ref mut lambda) => {
                    self.env.stack.enter_scope();

                    let mut iter = types::implicit_arg_iter(lambda.id.typ.remove_forall());
                    let mut implicit_arg_count = 0;
                    for typ in iter.by_ref() {
                        let name = Symbol::from("implicit_arg");
                        let arg = pos::spanned(
                            expr.span,
                            TypedIdent {
                                name: self.stack_var(name, expr.span, typ.clone()),
                                typ: typ.clone(),
                            },
                        );
                        lambda.args.insert(implicit_arg_count, arg);
                        implicit_arg_count += 1;
                    }
                    for (typ, arg) in
                        types::arg_iter(iter.typ).zip(&mut lambda.args[implicit_arg_count..])
                    {
                        arg.value.name =
                            self.stack_var(arg.value.name.clone(), expr.span, typ.clone());
                    }

                    self.visit_expr(&mut lambda.body);

                    self.env.stack.exit_scope();
                }
                Expr::TypeBindings(ref bindings, _) => {
                    self.env.stack.enter_scope();
                    self.env.stack_types.enter_scope();
                    for bind in bindings {
                        self.stack_type(
                            bind.name.value.clone(),
                            expr.span,
                            bind.finalized_alias.as_ref().expect(
                                "ICE: Alias should have been finalized \
                                 before renaming",
                            ),
                        );
                    }

                    return Ok(TailCall::TailCall);
                }
                Expr::Do(Do {
                    ref mut id,
                    ref mut bound,
                    ref mut flat_map_id,
                    ..
                }) => {
                    let flat_map_id = flat_map_id
                        .as_mut()
                        .unwrap_or_else(|| ice!("flat_map_id not set before renaming"));
                    if let Some(new_id) = self.rename(&flat_map_id.name, &flat_map_id.typ)? {
                        debug!("Rename identifier {} = {}", flat_map_id.name, new_id);
                        flat_map_id.name = new_id;
                    }

                    self.visit_expr(bound);

                    self.env.stack.enter_scope();
                    self.env.stack_types.enter_scope();

                    id.value.name =
                        self.stack_var(id.value.name.clone(), id.span, id.value.typ.clone());

                    return Ok(TailCall::TailCall);
                }

                _ => ast::walk_mut_expr(self, expr),
            }
            Ok(TailCall::Return)
        }

        fn find_implicit(
            &self,
            span: Span<BytePos>,
            implicit_type: &ArcType,
        ) -> Result<SpannedExpr<Symbol>, RenameError> {
            info!("Trying to resolve implicit {}", implicit_type);

            // FIXME HACK
            {
                let mut has_variable = false;
                ::base::types::walk_type(implicit_type, |typ: &ArcType| {
                    if let Type::Variable(_) = **typ {
                        has_variable = true;
                    }
                });
                if has_variable {
                    return Err(::rename::RenameError::UnableToResolveImplicit(
                        implicit_type.clone(),
                    ));
                }
            }

            let is_implicit_type = implicit_type
                .name()
                .and_then(|typename| {
                    self.metadata
                        .get(typename)
                        .or_else(|| self.env.env.get_metadata(typename))
                        .and_then(|metadata| {
                            metadata.comment.as_ref().map(|comment| {
                                ::metadata::attributes(&comment).any(|(key, _)| key == "implicit")
                            })
                        })
                })
                .unwrap_or(false);

            let found = self.env
                .stack
                .iter()
                .filter_map(|(prev_id, &(ref id, _, ref typ))| {
                    let implicit_kind_opt = if is_implicit_type {
                        Some(ImplicitKind::Always)
                    } else {
                        self.metadata.get(prev_id).map(ImplicitKind::Binding)
                    };
                    implicit_kind_opt.and_then(|implicit_kind| {
                        self.find_implicit_of(span, id, implicit_kind, typ, implicit_type)
                    })
                })
                .next();

            match found {
                Some(mut path) => {
                    debug!(
                        "Found implicit `{}`",
                        path.iter().map(|id| &id.name).format(".")
                    );

                    let base_ident = path.pop().unwrap();
                    Ok(path.into_iter().rev().fold(
                        pos::spanned(span, Expr::Ident(base_ident)),
                        |expr, ident| {
                            pos::spanned(
                                span,
                                Expr::Projection(Box::new(expr), ident.name, ident.typ),
                            )
                        },
                    ))
                }
                None => {
                    debug!("Unable to resolve implicit for `{}`", implicit_type);
                    Err(RenameError::UnableToResolveImplicit(implicit_type.clone()))
                }
            }
        }

        fn find_implicit_of(
            &self,
            span: Span<BytePos>,
            id: &Symbol,
            implicit_kind: ImplicitKind,
            typ: &ArcType,
            implicit_type: &ArcType,
        ) -> Option<Vec<TypedIdent<Symbol>>> {
            let is_implicit = match implicit_kind {
                ImplicitKind::Always => true,
                ImplicitKind::Binding(metadata) => {
                    metadata.comment.as_ref().map_or(false, |comment| {
                        ::metadata::attributes(&comment).any(|(key, _)| key == "implicit")
                    })
                }
            };

            if is_implicit {
                trace!("Testing {}: {}", id, typ);
            }

            let state = ::unify_type::State::new(&self.env, &self.subs);
            if is_implicit
                && ::unify_type::subsumes(
                    &self.subs,
                    &mut ScopedMap::new(),
                    0,
                    state,
                    implicit_type,
                    typ,
                ).is_ok()
            {
                Some(vec![
                    TypedIdent {
                        name: id.clone(),
                        typ: implicit_type.clone(),
                    },
                ])
            } else {
                let typ = ::unify_type::new_skolem_scope(&self.subs, &FnvMap::default(), typ);
                let ref typ = typ.instantiate_generics(&mut FnvMap::default());
                let raw_type = resolve::remove_aliases(&self.env, typ.clone());
                match *raw_type {
                    Type::Record(_) => raw_type
                        .row_iter()
                        .filter_map(|field| {
                            let field_implicit_kind_opt = match implicit_kind {
                                ImplicitKind::Always => Some(ImplicitKind::Always),
                                ImplicitKind::Binding(metadata) => metadata
                                    .module
                                    .get(field.name.declared_name())
                                    .map(ImplicitKind::Binding),
                            };
                            field_implicit_kind_opt.and_then(|field_implicit_kind| {
                                self.find_implicit_of(
                                    span,
                                    &field.name,
                                    field_implicit_kind,
                                    &field.typ,
                                    implicit_type,
                                ).map(|mut path| {
                                    path.push(TypedIdent {
                                        name: id.clone(),
                                        typ: typ.clone(),
                                    });
                                    path
                                })
                            })
                        })
                        .next(),
                    _ => None,
                }
            }
        }

        fn make_implicit_args(
            &mut self,
            span: Span<BytePos>,
            mut typ: ArcType,
        ) -> Vec<SpannedExpr<Symbol>> {
            let mut args = Vec::new();
            loop {
                typ = match *typ {
                    Type::Function(arg_type, ref arg, ref ret) if arg_type == ArgType::Implicit => {
                        match self.find_implicit(span, arg) {
                            Ok(implicit_id) => {
                                args.push(implicit_id);
                                ret.clone()
                            }
                            Err(err) => {
                                self.errors.push(pos::spanned(span, err));
                                break;
                            }
                        }
                    }
                    _ => break,
                };
            }
            args
        }
    }

    impl<'a, 'b> MutVisitor for RenameVisitor<'a, 'b> {
        type Ident = Symbol;

        fn visit_expr(&mut self, mut expr: &mut SpannedExpr<Self::Ident>) {
            let mut i = 0;
            loop {
                match self.rename_expr(expr) {
                    Ok(TailCall::Return) => break,
                    Ok(TailCall::TailCall) => {
                        expr = match { expr }.value {
                            Expr::LetBindings(_, ref mut new_expr)
                            | Expr::TypeBindings(_, ref mut new_expr)
                            | Expr::Do(Do {
                                body: ref mut new_expr,
                                ..
                            }) => new_expr,
                            _ => ice!("Only Let and Type expressions can tailcall"),
                        };
                        i += 1;
                    }
                    Err(err) => {
                        self.errors.push(Spanned {
                            span: expr.span,
                            value: err,
                        });
                    }
                }
            }

            if let Expr::Infix(..) = expr.value {
                let typ = if let Expr::Infix(_, ref id, _) = expr.value {
                    id.value.typ.clone()
                } else {
                    unreachable!()
                };
                let dummy = Expr::Literal(Literal::Int(0));
                let func = mem::replace(&mut expr.value, dummy);
                match func {
                    Expr::Infix(l, id, r) => {
                        let mut args = self.make_implicit_args(id.span, typ);
                        args.push(*l);
                        args.push(*r);

                        expr.value = Expr::App {
                            func: Box::new(pos::spanned(id.span, Expr::Ident(id.value))),
                            implicit_args: Vec::new(),
                            args,
                        };
                    }
                    _ => unreachable!(),
                }
            }

            // Resolve implicit arguments
            if let Ok(typ) = expr.try_type_of(&self.env) {
                let args = self.make_implicit_args(Span::new(expr.span.end, expr.span.end), typ);
                if !args.is_empty() {
                    let dummy = Expr::Literal(Literal::Int(0));
                    let func = mem::replace(&mut expr.value, dummy);
                    expr.value = Expr::App {
                        func: Box::new(pos::spanned(expr.span, func)),
                        implicit_args: Vec::new(),
                        args,
                    }
                }
            }

            for _ in 0..i {
                self.env.stack.exit_scope();
                self.env.stack_types.exit_scope();
            }
        }
    }

    let (_, metadata) = ::metadata::metadata(env, expr);

    let mut visitor = RenameVisitor {
        symbols: symbols,
        errors: Errors::new(),
        metadata,
        env: Environment {
            env: env,
            stack: ScopedMap::new(),
            stack_types: ScopedMap::new(),
        },
        subs: Substitution::new(Kind::typ()),
    };
    visitor.visit_expr(expr);
    if visitor.errors.has_errors() {
        Err(visitor.errors)
    } else {
        Ok(())
    }
}

pub fn equivalent(env: &TypeEnv, actual: &ArcType, inferred: &ArcType) -> bool {
    debug!("Equivalent {} <=> {}", actual, inferred);
    use substitution::Substitution;
    // FIXME This Substitution is unnecessary for equivalence unification
    let subs = Substitution::new(Kind::typ());
    let mut unifier = UnifierState {
        state: State::new(env, &subs),
        unifier: Equivalent {
            map: FnvMap::default(),
            equiv: true,
        },
    };
    unifier.try_match(actual, inferred);
    unifier.unifier.equiv
}

struct Equivalent {
    map: FnvMap<Symbol, ArcType>,
    equiv: bool,
}

impl<'a> Unifier<State<'a>, ArcType> for UnifierState<State<'a>, Equivalent> {
    fn report_error(&mut self, _error: UnifyError<ArcType, TypeError<Symbol>>) {
        self.unifier.equiv = false;
    }

    fn try_match_res(
        &mut self,
        l: &ArcType,
        r: &ArcType,
    ) -> Result<Option<ArcType>, UnifyError<ArcType, TypeError<Symbol>>> {
        debug!("{} ====> {}", l, r);
        match (&**l, &**r) {
            (&Type::Generic(ref gl), &Type::Generic(ref gr)) if gl == gr => Ok(None),
            (&Type::Skolem(ref gl), &Type::Skolem(ref gr)) if gl == gr => Ok(None),
            (&Type::Generic(ref gl), _) => match self.unifier.map.get(&gl.id).cloned() {
                Some(ref typ) => self.try_match_res(typ, r),
                None => {
                    self.unifier.map.insert(gl.id.clone(), r.clone());
                    Ok(None)
                }
            },
            (&Type::Skolem(ref gl), _) => match self.unifier.map.get(&gl.name).cloned() {
                Some(ref typ) => self.try_match_res(typ, r),
                None => {
                    self.unifier.map.insert(gl.name.clone(), r.clone());
                    Ok(None)
                }
            },
            _ => l.zip_match(r, self),
        }
    }

    fn error_type(&mut self) -> Option<ArcType> {
        None
    }
}
