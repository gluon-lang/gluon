//! The main typechecking interface which is responsible for typechecking expressions, patterns,
//! etc. Only checks which need to be aware of expressions are handled here the actual unifying and
//! checking of types are done in the `unify_type` and `kindcheck` modules.
use std::{
    borrow::{BorrowMut, Cow},
    mem,
    sync::Arc,
};

use crate::base::{
    ast::{
        self, Argument, AstType, DisplayEnv, Do, Expr, IdentEnv, KindedIdent, Literal, MutVisitor,
        Pattern, PatternField, SpannedExpr, SpannedIdent, SpannedPattern, TypeBinding, Typed,
        TypedIdent, ValueBinding, ValueBindings,
    },
    error::Errors,
    fnv::{FnvMap, FnvSet},
    kind::{ArcKind, Kind, KindCache, KindEnv},
    merge,
    metadata::{Metadata, MetadataEnv},
    pos::{self, BytePos, Span, Spanned},
    resolve,
    scoped_map::{self, ScopedMap},
    symbol::{Symbol, SymbolModule, SymbolRef, Symbols},
    types::{
        self, Alias, AliasRef, AppVec, ArcType, ArgType, Field, Flags, Generic, PrimitiveEnv, Type,
        TypeCache, TypeContext, TypeEnv, TypeExt, TypePtr, Walker,
    },
};

use crate::{
    implicits,
    kindcheck::KindCheck,
    substitution::{self, Substitution},
    typ::RcType,
    unify, unify_type, TypecheckEnv,
};

use self::{
    generalize::TypeGeneralizer,
    mod_type::{ModType, ModTypeRef, TypeModifier},
};

pub use self::error::{Help, HelpError, SpannedTypeError, TypeError};

mod error;
mod generalize;
mod mod_type;

pub(crate) type TcResult<T> = Result<T, TypeError<Symbol, RcType<Symbol>>>;

enum ErrorOrder {
    ExpectedActual,
    ActualExpected,
}

#[derive(Clone, Debug)]
struct StackBinding {
    typ: ModType,
}

pub(crate) struct Environment<'a> {
    /// The global environment which the typechecker extracts types from
    environment: &'a (dyn TypecheckEnv<Type = RcType> + 'a),
    /// Stack allocated variables
    stack: ScopedMap<Symbol, StackBinding>,
    /// Types which exist in some scope (`type Test = ... in ...`)
    stack_types: ScopedMap<Symbol, (RcType, Alias<Symbol, RcType>)>,
    kind_cache: KindCache,
    type_variables: ScopedMap<Symbol, RcType>,
    skolem_variables: ScopedMap<Symbol, RcType>,
}

impl<'a> KindEnv for Environment<'a> {
    fn find_kind(&self, type_name: &SymbolRef) -> Option<ArcKind> {
        self.stack_types
            .get(type_name)
            .map(|&(_, ref alias)| alias.kind(&self.kind_cache).into_owned())
            .or_else(|| {
                self.type_variables
                    .get(type_name)
                    .map(|t| t.kind(&self.kind_cache).into_owned())
            })
            .or_else(|| self.environment.find_kind(type_name))
    }
}

impl<'a> TypeEnv for Environment<'a> {
    type Type = RcType;

    fn find_type(&self, id: &SymbolRef) -> Option<RcType> {
        self.stack
            .get(id)
            .map(|bind| bind.typ.concrete.clone())
            .or_else(|| self.environment.find_type(id))
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<Alias<Symbol, RcType>> {
        self.stack_types
            .get(id)
            .map(|&(_, ref alias)| alias.clone())
            .or_else(|| self.environment.find_type_info(id))
    }
}

impl<'a> PrimitiveEnv for Environment<'a> {
    fn get_bool(&self) -> ArcType {
        self.environment.get_bool()
    }
}

impl<'a> MetadataEnv for Environment<'a> {
    fn get_metadata(&self, id: &SymbolRef) -> Option<Arc<Metadata>> {
        self.environment.get_metadata(id)
    }
}

impl Environment<'_> {
    fn find_mod_type(&self, id: &SymbolRef) -> Option<ModType> {
        self.stack
            .get(id)
            .map(|bind| bind.typ.clone())
            .or_else(|| self.environment.find_type(id).map(ModType::rigid))
    }
}

/// Struct which provides methods to typecheck expressions.
pub struct Typecheck<'a, 'ast> {
    pub(crate) environment: Environment<'a>,
    symbols: SymbolModule<'a>,
    pub(crate) subs: Substitution<RcType>,
    named_variables: FnvMap<Symbol, RcType>,
    pub(crate) errors: Errors<SpannedTypeError<Symbol, RcType<Symbol>>>,
    /// Type variables `let test: a -> b` (`a` and `b`)
    kind_cache: KindCache,

    pub(crate) implicit_resolver: implicits::ImplicitResolver<'a>,
    unbound_variables: ScopedMap<Symbol, ArcKind>,
    refined_variables: ScopedMap<u32, ()>,
    pub(crate) ast_arena: ast::ArenaRef<'a, 'ast, Symbol>,
}

impl<'a> TypeContext<Symbol, RcType> for Typecheck<'a, '_> {
    gluon_base::forward_type_interner_methods!(Symbol, RcType, self_, &self_.subs);
}

/// Error returned when unsuccessfully typechecking an expression
pub type Error = Errors<SpannedTypeError<Symbol>>;

pub use implicits::{Error as ImplicitError, ErrorKind as ImplicitErrorKind};

impl<'a, 'ast> Typecheck<'a, 'ast> {
    /// Create a new typechecker which typechecks expressions in `module`
    pub fn new(
        module: String,
        symbols: &'a mut Symbols,
        environment: &'a (dyn TypecheckEnv<Type = ArcType> + 'a),
        interner: &TypeCache<Symbol, ArcType>,
        metadata: &'a mut FnvMap<Symbol, Arc<Metadata>>,
        ast_arena: ast::ArenaRef<'a, 'ast, Symbol>,
    ) -> Self {
        let symbols = SymbolModule::new(module, symbols);
        let subs = Substitution::new(interner.kind_cache.typ(), interner.clone());
        Typecheck {
            environment: Environment {
                environment,
                stack: ScopedMap::new(),
                stack_types: ScopedMap::new(),
                kind_cache: interner.kind_cache.clone(),
                skolem_variables: ScopedMap::new(),
                type_variables: ScopedMap::new(),
            },
            symbols: symbols,
            named_variables: FnvMap::default(),
            errors: Errors::new(),
            kind_cache: interner.kind_cache.clone(),
            implicit_resolver: crate::implicits::ImplicitResolver::new(environment, metadata),
            unbound_variables: ScopedMap::new(),
            refined_variables: ScopedMap::new(),
            subs,
            ast_arena,
        }
    }

    pub(crate) fn error<E>(&mut self, span: Span<BytePos>, error: E) -> RcType
    where
        E: Into<HelpError<Symbol, RcType>>,
    {
        let error = error.into();
        debug!("Error: {}", error);
        self.errors.push(Spanned {
            span: span,
            value: error,
        });
        self.subs.error()
    }

    fn bool(&mut self) -> RcType {
        let typ = self.environment.get_bool().clone();
        self.translate_arc_type(&typ)
    }

    fn find_at(&mut self, span: Span<BytePos>, id: &Symbol) -> ModType {
        match self.find(id) {
            Ok(typ) => typ,
            Err(err) => ModType::wobbly(self.error(span, err)),
        }
    }

    fn find(&mut self, id: &Symbol) -> TcResult<ModType> {
        match self.environment.find_mod_type(id).map(|t| t.to_owned()) {
            Some(typ) => {
                self.named_variables.clear();
                debug!("Find {} : {}", self.symbols.string(id), typ);
                Ok(typ)
            }
            None => {
                // Don't report global variables inserted by the `import!` macro as undefined
                // (if they don't exist the error will already have been reported by the macro)
                if id.is_global() {
                    Ok(ModType::wobbly(self.subs.new_var()))
                } else {
                    info!("Undefined variable {}", id);
                    Err(TypeError::UndefinedVariable(id.clone()))
                }
            }
        }
    }

    fn find_type_info_at(&mut self, span: Span<BytePos>, id: &Symbol) -> Alias<Symbol, RcType> {
        match self.find_type_info(id).map(|alias| alias.clone()) {
            Ok(alias) => alias,
            Err(err) => {
                self.errors.push(Spanned {
                    span: span,
                    value: err.into(),
                });
                let hole = self.subs.hole();
                self.subs.new_alias(id.clone(), Vec::new(), hole)
            }
        }
    }

    fn find_type_info(&self, id: &Symbol) -> TcResult<Alias<Symbol, RcType>> {
        self.environment
            .find_type_info(id)
            .ok_or_else(|| TypeError::UndefinedType(id.clone()))
    }

    fn stack_var(&mut self, id: Symbol, typ: RcType) {
        let modifier = if typ
            .flags()
            .intersects(Flags::HAS_VARIABLES | Flags::HAS_FORALL)
        {
            TypeModifier::Wobbly
        } else {
            TypeModifier::Rigid
        };
        debug!("Insert {} : {:?} {}", id, modifier, typ);

        self.implicit_resolver.on_stack_var(&self.subs, &id, &typ);

        self.environment.stack.insert(
            id,
            StackBinding {
                typ: ModType::new(modifier, typ),
            },
        );
    }

    fn stack_type(&mut self, id: Symbol, alias: &Alias<Symbol, RcType>) {
        // Insert variant constructors into the local scope
        //

        // We want to prevent the constructors of more specialized aliases from shadowing the more
        // general ones so we get the canonical alias and then take its inner type without applying
        // any types to always get the most general type of the constructors
        //
        // ```
        // type Option a = | None | Some a
        // type OptionInt = Option Int
        // // Should work
        // Some ""
        // ```
        let aliased_type = alias.typ(&mut &self.subs);
        let canonical_alias_type = resolve::AliasRemover::new()
            .canonical_alias(&self.environment, &mut &self.subs, &aliased_type, |alias| {
                match **alias.unresolved_type() {
                    Type::Variant(_) => true,
                    _ => false,
                }
            })
            .unwrap_or_else(|_err| {
                // The error is reported in unification
                aliased_type.clone()
            });

        let (outer_params, canonical_alias, inner_type) =
            alias.unpack_canonical_alias(&canonical_alias_type, |a| a.typ(&mut &self.subs));

        if let Type::Variant(ref variants) = **inner_type {
            for field in variants.row_iter().cloned() {
                let a = self.intern(Type::Alias(canonical_alias.clone()));
                let params = canonical_alias
                    .params()
                    .iter()
                    .map(|g| self.generic(g.clone()))
                    .collect();
                let variant_type = self.app(a.clone(), params);

                let ctor_type =
                    types::walk_move_type(field.typ.clone(), &mut |typ: &ArcType| match &**typ {
                        Type::Function(ArgType::Constructor, arg, ret) => {
                            Some(Type::function(Some(arg.clone()), ret.clone()))
                        }
                        Type::Ident(id) if canonical_alias.name == id.name => Some(a.clone()),
                        Type::Opaque => Some(variant_type.clone()),
                        _ => None,
                    });

                let typ = self.forall(
                    canonical_alias
                        .params()
                        .iter()
                        .chain(outer_params.iter())
                        .cloned()
                        .collect(),
                    ctor_type,
                );

                let symbol = self.symbols.symbols().simple_symbol(field.name.as_str());
                self.stack_var(symbol, typ);
            }
        }

        let generic_args = alias
            .params()
            .iter()
            .cloned()
            .map(|g| self.generic(g))
            .collect();
        let typ = self.subs.app(alias.as_ref().clone(), generic_args);
        {
            // FIXME: Workaround so that both the types name in this module and its global
            // name are imported. Without this aliases may not be traversed properly
            self.environment
                .stack_types
                .insert(alias.name.clone(), (typ.clone(), alias.clone()));
        }
        self.environment
            .stack_types
            .insert(id, (typ, alias.clone()));
    }

    fn enter_scope(&mut self) {
        self.environment.stack.enter_scope();
        self.environment.stack_types.enter_scope();
        self.implicit_resolver.enter_scope();
    }

    fn exit_scope(&mut self) {
        self.environment.stack.exit_scope();
        self.environment.stack_types.exit_scope();
        self.implicit_resolver.exit_scope();
    }

    fn generalize_binding(
        &mut self,
        level: u32,
        resolved_type: &mut RcType,
        binding: &mut ValueBinding<'ast, Symbol>,
    ) {
        let mut generalizer = TypeGeneralizer::new(level, self, resolved_type, binding.name.span);
        generalize_binding(&mut generalizer, resolved_type, binding);
    }

    fn generalize_variables<'i>(
        &mut self,
        level: u32,
        args: &mut dyn Iterator<Item = &'i mut SpannedIdent<Symbol>>,
        expr: &mut SpannedExpr<Symbol>,
    ) {
        let typ = self.subs.hole();
        TypeGeneralizer::new(level, self, &typ, expr.span).generalize_variables(args, expr)
    }

    fn generalize_type_errors(&mut self, errors: &mut Errors<SpannedTypeError<Symbol, RcType>>) {
        self.environment.skolem_variables.enter_scope();

        for err in errors {
            use self::TypeError::*;

            match err.value.error {
                UndefinedVariable(_)
                | UndefinedType(_)
                | DuplicateTypeDefinition(_)
                | DuplicateField(_)
                | UndefinedRecord { .. }
                | EmptyCase
                | KindError(_)
                | RecursionCheck(_)
                | Message(_) => (),
                NotAFunction(ref mut typ)
                | UndefinedField(ref mut typ, _)
                | PatternError {
                    constructor_type: ref mut typ,
                    ..
                }
                | InvalidProjection(ref mut typ)
                | TypeConstructorReturnsWrongType {
                    actual: ref mut typ,
                    ..
                } => self.generalize_type(0, typ, err.span),
                UnableToResolveImplicit(ref mut inner_err) => {
                    use crate::implicits::ErrorKind::*;
                    match inner_err.kind {
                        MissingImplicit(ref mut typ) => {
                            self.generalize_type(0, typ, err.span);
                        }
                        AmbiguousImplicit(ref mut xs) => {
                            for entry in xs {
                                self.generalize_type(0, &mut entry.typ, err.span);
                            }
                        }
                        LoopInImplicitResolution(..) => (),
                    }
                    let err_span = err.span;
                    inner_err.reason = inner_err
                        .reason
                        .iter()
                        .map(|typ| {
                            let mut typ = typ.clone();
                            self.generalize_type(0, &mut typ, err_span);
                            typ
                        })
                        .collect();
                }
                Unification(ref mut expected, ref mut actual, ref mut errors) => {
                    self.generalize_type_without_forall(0, expected, err.span);
                    self.generalize_type_without_forall(0, actual, err.span);
                    for unify_err in errors {
                        match *unify_err {
                            unify::Error::TypeMismatch(ref mut l, ref mut r) => {
                                self.generalize_type_without_forall(0, l, err.span);
                                self.generalize_type_without_forall(0, r, err.span);
                            }
                            unify::Error::Substitution(ref mut occurs_err) => match *occurs_err {
                                substitution::Error::Occurs(_, ref mut typ) => {
                                    self.generalize_type_without_forall(0, typ, err.span);
                                }
                            },
                            unify::Error::Other(ref mut other_err) => {
                                if let unify_type::TypeError::MissingFields(ref mut typ, _) =
                                    *other_err
                                {
                                    self.generalize_type_without_forall(0, typ, err.span);
                                }
                            }
                        }
                    }
                }
            }
        }

        self.environment.skolem_variables.exit_scope();
    }

    /// Typecheck `expr`. If successful the type of the expression will be returned and all
    /// identifiers in `expr` will be filled with the inferred type
    pub fn typecheck_expr(
        &mut self,
        expr: &mut SpannedExpr<'ast, Symbol>,
    ) -> Result<ArcType, Error> {
        self.typecheck_expr_expected(expr, None)
    }

    pub fn typecheck_expr_expected(
        &mut self,
        expr: &mut SpannedExpr<'ast, Symbol>,
        expected_type: Option<&ArcType>,
    ) -> Result<ArcType, Error> {
        let expected_type = expected_type.map(|t| self.translate_arc_type(t));

        self.typecheck_expr_expected_(expr, expected_type.as_ref())
            .map(|t| self.translate_rc_type(&t))
    }

    fn typecheck_expr_expected_(
        &mut self,
        expr: &mut SpannedExpr<'ast, Symbol>,
        expected_type: Option<&RcType>,
    ) -> Result<RcType, Error> {
        fn tail_expr<'e, 'ast>(
            e: &'e mut SpannedExpr<'ast, Symbol>,
        ) -> &'e mut SpannedExpr<'ast, Symbol> {
            match e.value {
                Expr::LetBindings(_, ref mut b) | Expr::TypeBindings(_, ref mut b) => tail_expr(b),
                _ => e,
            }
        }
        info!("Typechecking {}", self.symbols.module());
        // FIXME self.subs.clear();
        self.environment.stack.clear();

        if let Err(err) = crate::recursion_check::check_expr(expr) {
            self.errors.extend(
                err.into_iter()
                    .map(|err| pos::spanned(err.span, TypeError::from(err.value).into())),
            );
        }

        let temp = expected_type.and_then(|expected| self.create_unifiable_signature(expected));
        let expected_type = temp.as_ref().or(expected_type);

        let mut typ = if let Some(expected_type) = expected_type {
            self.skolemize_in(
                expr.span,
                ModType::rigid(&expected_type),
                |self_, expected_type| {
                    self_.typecheck_bindings(true, expr, Some(ModType::rigid(&expected_type)))
                },
            )
        } else {
            self.typecheck_bindings(true, expr, None)
        };

        {
            if let Some(expected_type) = expected_type {
                let mut type_cache = &self.subs;
                self.environment.skolem_variables.extend(
                    expected_type
                        .forall_params()
                        .map(|param| (param.id.clone(), type_cache.hole())),
                );
            }
            // Only the 'tail' expression need to be generalized at this point as all bindings
            // will have already been generalized
            let tail = tail_expr(expr);
            crate::implicits::resolve(self, tail);
            self.generalize_type(0, &mut typ, tail.span);
            self.generalize_variables(0, &mut [].iter_mut(), tail);
        }

        {
            struct ReplaceVisitor<'a: 'b, 'b, 'ast> {
                tc: &'b mut Typecheck<'a, 'ast>,
            }

            impl<'a, 'b, 'd> MutVisitor<'d, '_> for ReplaceVisitor<'a, 'b, '_> {
                type Ident = Symbol;

                fn visit_typ(&mut self, typ: &mut ArcType) {
                    *typ = if let Type::Variable(var) = &**typ {
                        let typ = self
                            .tc
                            .subs
                            .find_type_for_var(var.id)
                            .cloned()
                            .unwrap_or_else(|| self.tc.subs.error());

                        self.tc.translate_rc_type(&typ)
                    } else {
                        return;
                    }
                }
            }

            {
                let mut visitor = ReplaceVisitor { tc: self };
                visitor.visit_expr(expr);
            }
        }

        if self.errors.has_errors() {
            let mut errors = mem::replace(&mut self.errors, Errors::new());
            let l = errors.len();
            debug!("Generalize type errors");
            self.generalize_type_errors(&mut errors);
            // FIXME We shouldn't even generate errors here
            while errors.len() > l {
                errors.pop();
            }

            Err(errors
                .into_iter()
                .map(|spanned| {
                    spanned.map(|err| crate::base::error::Help {
                        error: err.error.map_t(&mut |t| self.translate_rc_type(&t)),
                        help: err.help,
                    })
                })
                .collect())
        } else {
            debug!("Typecheck result: {}", typ);
            Ok(typ.concrete)
        }
    }

    fn infer_expr(&mut self, expr: &mut SpannedExpr<'ast, Symbol>) -> ModType {
        self.typecheck_opt(expr, None)
    }

    fn typecheck(
        &mut self,
        expr: &mut SpannedExpr<'ast, Symbol>,
        expected_type: ModTypeRef,
    ) -> ModType {
        self.typecheck_opt(expr, Some(expected_type))
    }

    /// Main typechecking function. Returns the type of the expression if typechecking was
    /// successful
    fn typecheck_opt(
        &mut self,
        expr: &mut SpannedExpr<'ast, Symbol>,
        mut expected_type: Option<ModTypeRef>,
    ) -> ModType {
        let returned_type;

        match self.typecheck_(expr, &mut expected_type) {
            Ok((typ, args)) => {
                if !args.is_empty() {
                    match expr.value {
                        Expr::App {
                            ref mut implicit_args,
                            ..
                        } => {
                            if implicit_args.is_empty() {
                                *implicit_args = self.ast_arena.alloc_extend(args);
                            } else {
                                *implicit_args = self.ast_arena.alloc_extend(
                                    implicit_args.iter_mut().map(mem::take).chain(args),
                                );
                            }
                        }
                        _ => {
                            let func = mem::take(&mut expr.value);
                            expr.value = Expr::App {
                                func: self.ast_arena.alloc(pos::spanned(expr.span, func)),
                                implicit_args: self.ast_arena.alloc_extend(args),
                                args: &mut [],
                            }
                        }
                    }
                }

                returned_type = match expected_type {
                    Some(expected_type) => ModType::new(
                        expected_type.modifier,
                        self.subsumes_expr(expr.span, &typ, expected_type.concrete.clone(), expr),
                    ),
                    None => typ,
                };
            }
            Err(err) => {
                returned_type = ModType::wobbly(self.subs.error());
                self.errors.push(Spanned {
                    span: expr_check_span(expr),
                    value: err.into(),
                });
            }
        }
        returned_type
    }

    /// `expected_type` should be set to `None` if subsumption is done with it (to prevent us from
    /// doing it twice)
    fn typecheck_(
        &mut self,
        expr: &mut SpannedExpr<'ast, Symbol>,
        expected_type: &mut Option<ModTypeRef>,
    ) -> TcResult<(ModType, Vec<SpannedExpr<'ast, Symbol>>)> {
        if let Some(result) = self.check_macro(expr) {
            return Ok((result?, Vec::new()));
        }
        match expr.value {
            Expr::Ident(ref mut id) => {
                let typ = self.find(&id.name)?;
                let modifier = typ.modifier;
                let (args, typ) = self.instantiate_sigma(
                    expr.span,
                    &typ,
                    &mut expected_type.take().map(|t| t.concrete),
                );
                id.typ = self.subs.bind_arc(&typ);
                Ok((ModType::new(modifier, typ), args))
            }
            Expr::Literal(ref lit) => Ok((
                ModType::rigid(match *lit {
                    Literal::Int(_) => self.subs.int(),
                    Literal::Byte(_) => self.subs.byte(),
                    Literal::Float(_) => self.subs.float(),
                    Literal::String(_) => self.subs.string(),
                    Literal::Char(_) => self.subs.char(),
                }),
                Vec::new(),
            )),
            Expr::App {
                ref mut func,
                ref mut implicit_args,
                ref mut args,
            } => {
                let func_type = self.infer_expr(func);
                let mut implicit_vec = CowVec::Borrowed(implicit_args);
                let typ = self.typecheck_application(
                    expr.span,
                    func_type,
                    &mut implicit_vec,
                    &mut **args,
                );
                if let CowVec::Owned(implicit_vec) = implicit_vec {
                    *implicit_args = self.ast_arena.alloc_extend(implicit_vec);
                }

                typ
            }
            Expr::IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
                let bool_type = self.bool();
                let pred_type = self.typecheck(&mut **pred, ModType::rigid(&bool_type));
                self.unify_span(expr_check_span(pred), &bool_type, pred_type.concrete);

                // Both branches must unify to the same type
                let true_type = self.typecheck_opt(&mut **if_true, expected_type.clone());
                let false_type = self.typecheck_opt(&mut **if_false, expected_type.take());

                let modifier = true_type.modifier | false_type.modifier;

                let true_type = self.instantiate_generics(&true_type);
                let false_type = self.instantiate_generics(&false_type);

                self.unify(&true_type, false_type)
                    .map(|t| (ModType::new(modifier, t), Vec::new()))
            }
            Expr::Infix {
                ref mut lhs,
                ref mut op,
                ref mut rhs,
                ref mut implicit_args,
            } => {
                let op_name = String::from(self.symbols.string(&op.value.name));
                let func_type = if op_name.starts_with('#') {
                    // Handle primitives
                    let op_type = op_name.trim_matches(|c: char| !c.is_alphabetic());
                    let builtin_type = op_type.parse().map_err(|_| {
                        TypeError::Message("Invalid builtin type for operator".to_string())
                    })?;
                    let prim_type = self.subs.builtin_type(builtin_type);
                    let return_type = match &op_name[1 + op_type.len()..] {
                        "+" | "-" | "*" | "/" => prim_type.clone(),
                        "==" | "<" => self.bool(),
                        _ => return Err(TypeError::UndefinedVariable(op.value.name.clone())),
                    };
                    ModType::rigid(self.subs.function(
                        vec![prim_type.clone(), prim_type.clone()],
                        return_type.clone(),
                    ))
                } else {
                    match &*op_name {
                        "&&" | "||" => {
                            let b = self.bool();
                            ModType::rigid(self.subs.function(vec![b.clone(), b.clone()], b))
                        }
                        _ => self.find_at(op.span, &op.value.name),
                    }
                };

                let func_type =
                    ModType::new(func_type.modifier, self.instantiate_generics(&func_type));

                op.value.typ = self.subs.bind_arc(&func_type);

                let mut implicit_vec = CowVec::Borrowed(implicit_args);
                let typ = self.typecheck_application(
                    op.span,
                    func_type,
                    &mut implicit_vec,
                    [&mut **lhs, &mut **rhs].iter_mut().map(|expr| &mut **expr),
                );
                if let CowVec::Owned(implicit_vec) = implicit_vec {
                    *implicit_args = self.ast_arena.alloc_extend(implicit_vec);
                }
                typ
            }
            Expr::Tuple {
                ref mut typ,
                elems: ref mut exprs,
            } => {
                let new_type = match exprs.len() {
                    0 => ModType::rigid(self.unit()),
                    1 => self.typecheck_opt(&mut exprs[0], expected_type.take()),
                    _ => {
                        let mut modifier = TypeModifier::Rigid;
                        let fields = exprs
                            .iter_mut()
                            .enumerate()
                            .map(|(i, expr)| {
                                let typ = self.infer_expr(expr);
                                modifier |= typ.modifier;
                                Field {
                                    name: self.symbols.simple_symbol(format!("_{}", i)),
                                    typ: typ.concrete,
                                }
                            })
                            .collect();
                        ModType::new(modifier, self.record(vec![], fields))
                    }
                };
                *typ = self.subs.bind_arc(&new_type);
                Ok((new_type, Vec::new()))
            }
            Expr::Match(ref mut expr, ref mut alts) => {
                let mut scrutinee_type = self.infer_expr(&mut **expr);
                let modifier = scrutinee_type.modifier;
                let expected_type = expected_type.take().map(|t| t.to_owned());

                let mut unaliased_scrutinee_type = match alts.first().map(|alt| &alt.pattern.value)
                {
                    Some(Pattern::Constructor(..)) => {
                        let typ = self.remove_aliases(scrutinee_type.concrete.clone());
                        ModType::new(modifier, self.instantiate_generics(&typ))
                    }
                    _ => scrutinee_type.clone(),
                };

                let mut expr_type: Option<ModType> = None;

                let original_scrutinee_type = scrutinee_type.clone();

                for alt in alts.iter_mut() {
                    self.enter_scope();
                    self.refined_variables.enter_scope();

                    self.typecheck_pattern(
                        &mut alt.pattern,
                        original_scrutinee_type.clone(),
                        scrutinee_type.concrete.clone(),
                    );

                    let mut alt_type = self
                        .typecheck_opt(&mut alt.expr, expected_type.as_ref().map(|t| t.as_ref()));
                    alt_type.concrete = self.instantiate_generics(&alt_type);
                    match expr_type {
                        Some(ref expr_type) if expected_type.is_none() => {
                            alt_type.concrete =
                                self.unify_span(alt.expr.span, expr_type, alt_type.concrete);
                        }
                        _ => (),
                    }

                    for (var, _) in self.refined_variables.exit_scope() {
                        self.subs.reset(var);
                    }
                    self.exit_scope();

                    // The variant we matched on will not appear in any followup bindings so remove
                    // this variant from the type we are matching on
                    //
                    // TODO Make this more general so it can error when not matching on all the
                    // variants
                    {
                        *unaliased_scrutinee_type = self.subs.zonk(&unaliased_scrutinee_type);
                        let replaced = match (&alt.pattern.value, &**unaliased_scrutinee_type) {
                            (Pattern::Constructor(id, _), Type::Variant(row)) => {
                                let mut variant_iter = row.row_iter();
                                let variants = variant_iter
                                    .by_ref()
                                    .filter(|variant| variant.name != id.name)
                                    .cloned()
                                    .collect();

                                // Don't remove constructors on closed records as they may fail to
                                // unify when checking against the pattern
                                if let Type::EmptyRow = **variant_iter.current_type() {
                                    false
                                } else {
                                    let rest = self.subs.new_var();
                                    scrutinee_type.concrete = self.poly_variant(variants, rest);
                                    true
                                }
                            }
                            _ => false,
                        };
                        if replaced {
                            unaliased_scrutinee_type = scrutinee_type.clone();
                        }
                    }

                    expr_type = Some(alt_type);
                }
                expr_type
                    .ok_or(TypeError::EmptyCase)
                    .map(|typ| (typ, Vec::new()))
            }

            Expr::TypeBindings(..) | Expr::LetBindings(..) => Ok((
                self.typecheck_bindings(false, expr, expected_type.take()),
                Vec::new(),
            )),

            Expr::Projection(ref mut expr, ref field_id, ref mut ast_field_typ) => {
                let mut expr_typ = self.infer_expr(&mut **expr);
                let modifier = expr_typ.modifier;
                debug!(
                    "Projection {} . {:?}",
                    &expr_typ,
                    self.symbols.string(field_id)
                );
                self.subs.make_real(&mut expr_typ);
                expr_typ.concrete = self.instantiate_generics(&expr_typ);
                let record = self.remove_aliases(expr_typ.concrete.clone());
                match *record {
                    Type::Variable(_) | Type::Record(_) => {
                        let field_type = record
                            .row_iter()
                            .find(|field| field.name.name_eq(field_id))
                            .map(|field| field.typ.clone());
                        let mut implicit_args = Vec::new();
                        let new_ast_field_type = match field_type {
                            Some(typ) => {
                                let (args, typ) = self.instantiate_sigma(
                                    expr.span,
                                    &typ,
                                    &mut expected_type.take().map(|t| t.concrete),
                                );
                                implicit_args = args;
                                typ
                            }
                            None => {
                                // FIXME As the polymorphic `record_type` do not have the type
                                // fields which `typ` this unification is only done after we
                                // checked if the field exists which lets field accesses on
                                // types with type fields still work
                                let field_var = self.subs.new_var();
                                let field = Field::new(field_id.clone(), field_var.clone());
                                let record_type =
                                    self.poly_record(vec![], vec![field], self.subs.new_var());
                                self.unify(&record_type, record)?;
                                field_var
                            }
                        };
                        *ast_field_typ = self.subs.bind_arc(&new_ast_field_type);
                        Ok((ModType::new(modifier, new_ast_field_type), implicit_args))
                    }
                    Type::Error => Ok((ModType::new(modifier, record.clone()), Vec::new())),
                    _ => Err(TypeError::InvalidProjection(record)),
                }
            }
            Expr::Array(ref mut array) => {
                let mut expected_element_type = ModType::rigid(self.subs.new_var());

                let array_type = self.subs.array(expected_element_type.concrete.clone());
                array.typ = self.subs.bind_arc(&array_type);
                if let Some(expected_type) = expected_type.take() {
                    self.unify_span(expr.span, &expected_type, array_type.clone());
                }

                for expr in &mut *array.exprs {
                    expected_element_type |=
                        self.typecheck(expr, ModType::wobbly(&expected_element_type));
                }

                Ok((ModType::wobbly(array_type), Vec::new()))
            }
            Expr::Lambda(ref mut lambda) => {
                let level = self.subs.var_id();
                let function_type = expected_type
                    .take()
                    .map(|t| t.to_owned())
                    .unwrap_or_else(|| ModType::wobbly(self.subs.new_var()));

                let start = expr.span.start();
                let mut typ =
                    self.skolemize_in(expr.span, function_type.as_ref(), |self_, function_type| {
                        self_.typecheck_lambda(
                            function_type,
                            start,
                            &mut lambda.args,
                            &mut lambda.body,
                        )
                    });

                self.generalize_type(level, &mut typ, expr.span);
                lambda.id.typ = self.subs.bind_arc(&typ);
                Ok((typ.clone(), Vec::new()))
            }
            Expr::Record {
                ref mut typ,
                ref mut types,
                exprs: ref mut fields,
                ref mut base,
            } => {
                let level = self.subs.var_id();

                let mut modifier = expected_type
                    .as_ref()
                    .map(|t| t.modifier)
                    .unwrap_or_default();

                let expected_record_type = expected_type.and_then(|expected_type| {
                    let expected_type = self.subs.real(&expected_type).clone();
                    let typ = resolve::remove_aliases_cow(
                        &self.environment,
                        &mut &self.subs,
                        &expected_type,
                    );
                    match **typ {
                        Type::Record(_) => Some(typ.into_owned()),
                        _ => None,
                    }
                });

                let expected_type = match &expected_record_type {
                    Some(expected_record_type) => {
                        let mut expected_fields: FnvSet<_> = expected_record_type
                            .row_iter()
                            .map(|f| &f.name)
                            .chain(expected_record_type.type_field_iter().map(|f| &f.name))
                            .collect();

                        let expected_fields_matches = fields
                            .iter()
                            .map(|f| &f.name.value)
                            .chain(types.iter().map(|f| &f.name.value))
                            .all(|name| expected_fields.remove(&name))
                            && expected_fields.is_empty();

                        if expected_fields_matches {
                            // No need to do subsumption checking against the expected type as all the
                            // fields will be matched against anyway
                            expected_type.take();
                        }

                        Some(expected_record_type)
                    }
                    None => None,
                };

                let mut base_record_types = FnvMap::default();
                let mut base_record_fields = FnvMap::default();
                let mut base_types: Vec<Field<_, _>> = Vec::new();
                let mut base_fields: Vec<Field<_, RcType>> = Vec::new();
                if let Some(ref mut base) = *base {
                    let base_type = self.infer_expr(base);
                    let base_type = self.remove_aliases(base_type.concrete);

                    let record_type = self.poly_record(vec![], vec![], self.subs.new_var());
                    let base_type = self.unify_span(base.span, &record_type, base_type);
                    let base_type = self.subs.zonk(&base_type);

                    base_types.extend(base_type.type_field_iter().cloned());
                    base_fields.extend(base_type.row_iter().cloned());

                    base_record_types.extend(
                        base_types
                            .iter()
                            .map(|field| field.name.declared_name().to_string())
                            .enumerate()
                            .map(|(i, n)| (n, i)),
                    );
                    base_record_fields.extend(
                        base_fields
                            .iter()
                            .map(|field| field.name.declared_name().to_string())
                            .enumerate()
                            .map(|(i, n)| (n, i)),
                    );
                }

                let mut duplicated_fields = FnvSet::default();

                let mut new_types: Vec<Field<_, _>> = Vec::with_capacity(types.len());
                for field in &mut **types {
                    if let Some(ref mut typ) = field.value {
                        let rc_type = self.translate_arc_type(typ);
                        if let Some(new_type) = self.create_unifiable_signature(&rc_type) {
                            *typ = self.translate_rc_type(&new_type);
                        }
                    }

                    let alias = self.find_type_info_at(field.name.span, &field.name.value);
                    if self.error_on_duplicated_field(&mut duplicated_fields, &field.name) {
                        match base_record_types.get(field.name.value.declared_name()) {
                            Some(&i) => base_types[i].typ = alias,
                            None => new_types.push(Field::new(field.name.value.clone(), alias)),
                        }
                    }
                }

                let mut new_fields: Vec<Field<_, RcType>> = Vec::with_capacity(fields.len());
                for field in &mut **fields {
                    let name = &field.name.value;
                    let expected_field_type = expected_type
                        .as_ref()
                        .and_then(|expected_type| {
                            expected_type
                                .row_iter()
                                .find(|expected_field| expected_field.name.name_eq(&name))
                        })
                        .map(|field| ModType::new(modifier, &field.typ));

                    let mut typ = match field.value {
                        Some(ref mut expr) => self.typecheck_opt(expr, expected_field_type),
                        None => {
                            let typ = self.find_at(field.name.span, &field.name.value);
                            let modifier = typ.modifier;
                            match expected_field_type {
                                Some(expected_field_type) => {
                                    let mut implicit_args = Vec::new();
                                    let typ = self.subsumes_implicit(
                                        field.name.span,
                                        ErrorOrder::ExpectedActual,
                                        &expected_field_type.concrete,
                                        typ.concrete,
                                        &mut |implicit_arg| {
                                            implicit_args
                                                .push(pos::spanned(field.name.span, implicit_arg));
                                        },
                                    );

                                    if !implicit_args.is_empty() {
                                        field.value = Some(pos::spanned(
                                            field.name.span,
                                            Expr::App {
                                                func: self.ast_arena.alloc(pos::spanned(
                                                    field.name.span,
                                                    Expr::Ident(TypedIdent {
                                                        name: field.name.value.clone(),
                                                        typ: self.subs.bind_arc(&typ),
                                                    }),
                                                )),
                                                implicit_args: self
                                                    .ast_arena
                                                    .alloc_extend(implicit_args),
                                                args: &mut [],
                                            },
                                        ));
                                    }

                                    ModType::new(modifier, typ)
                                }
                                None => typ,
                            }
                        }
                    };
                    self.generalize_type(level, &mut typ, field.name.span);

                    if self.error_on_duplicated_field(&mut duplicated_fields, &field.name) {
                        match base_record_fields.get(field.name.value.declared_name()) {
                            Some(&i) => base_fields[i].typ = typ.concrete,
                            None => {
                                new_fields.push(Field::new(field.name.value.clone(), typ.concrete))
                            }
                        }
                    }

                    modifier |= typ.modifier;
                }

                new_types.extend(base_types);
                new_fields.extend(base_fields);
                let new_type = self.subs.record(new_types, new_fields);
                *typ = self.subs.bind_arc(&new_type);

                Ok((ModType::new(modifier, new_type), Vec::new()))
            }
            Expr::Block(ref mut exprs) => {
                let (last, exprs) = exprs.split_last_mut().expect("Expr in block");
                for expr in exprs {
                    self.infer_expr(expr);
                }
                Ok((self.typecheck_opt(last, expected_type.take()), Vec::new()))
            }
            Expr::Do(Do {
                ref mut id,
                ref mut typ,
                ref mut bound,
                ref mut body,
                ref mut flat_map_id,
            }) => {
                let do_span = expr.span.subspan(0.into(), 2.into());
                let flat_map_type = match flat_map_id
                    .as_mut()
                    .expect("flat_map inserted during renaming")
                    .value
                {
                    Expr::Ident(ref mut flat_map) => match self.find(&flat_map.name) {
                        Ok(x) => x,
                        Err(error) => {
                            self.error(
                                do_span,
                                crate::base::error::Help {
                                    error,
                                    help: Some(Help::UndefinedFlatMapInDo),
                                },
                            );
                            ModType::wobbly(self.subs.error())
                        }
                    },
                    _ => ice!("flat_map_id not inserted during renaming"),
                };

                let flat_map_type = self.instantiate_generics(&flat_map_type);

                let flat_map_type = match *flat_map_type {
                    Type::Function(ArgType::Implicit, ref arg_type, ref r) => {
                        let name = self.implicit_resolver.make_implicit_ident(arg_type);
                        *flat_map_id = Some(self.ast_arena.alloc(pos::spanned(
                            do_span,
                            Expr::App {
                                func: flat_map_id.take().unwrap(),
                                args: self.ast_arena.alloc_extend(Some(pos::spanned(
                                    do_span,
                                    Expr::Ident(TypedIdent {
                                        name,
                                        typ: self.subs.bind_arc(&arg_type),
                                    }),
                                ))),
                                implicit_args: &mut [],
                            },
                        )));
                        r.clone()
                    }
                    _ => flat_map_type.clone(),
                };

                let id_type = self.resolve_type_signature(typ.as_mut());
                let arg1 = self
                    .subs
                    .function(Some(id_type.concrete.clone()), self.subs.new_var());
                let arg2 = self.subs.new_var();

                let ret = expected_type
                    .as_ref()
                    .map(|t| t.to_owned())
                    .unwrap_or_else(|| ModType::wobbly(self.subs.new_var()));
                let func_type = self
                    .subs
                    .function(vec![arg1.clone(), arg2.clone()], ret.concrete.clone());

                self.typecheck(bound, ModType::wobbly(&arg2));

                self.unify_span(do_span, &flat_map_type, func_type);

                if let Some(ref mut id) = *id {
                    self.typecheck_pattern(id, id_type.clone(), id_type.concrete);
                }

                let body_type = self.typecheck(body, ret.as_ref());

                let ret = self.unify_span(body.span, &ret, body_type.concrete.clone());

                Ok((ModType::wobbly(ret), Vec::new()))
            }
            Expr::MacroExpansion {
                ref mut replacement,
                ..
            } => self.typecheck_(replacement, expected_type),

            Expr::Annotated(ref mut expr, ref mut typ) => {
                let mut typ = self.translate_arc_type(typ);
                if let Some(new) = self.create_unifiable_signature(&typ) {
                    typ = new;
                }
                self.typecheck_(expr, &mut Some(ModType::rigid(&typ)))
            }

            Expr::Error(ref typ) => Ok((
                ModType::wobbly(
                    typ.as_ref()
                        .map(|typ| self.translate_arc_type(typ))
                        .unwrap_or_else(|| self.subs.new_var()),
                ),
                Vec::new(),
            )),
        }
    }

    fn typecheck_application<'e, I>(
        &mut self,
        span: Span<BytePos>,
        func_type: ModType,
        implicit_args: &mut CowVec<SpannedExpr<'ast, Symbol>>,
        args: I,
    ) -> TcResult<(ModType, Vec<SpannedExpr<'ast, Symbol>>)>
    where
        I: IntoIterator<Item = &'e mut SpannedExpr<'ast, Symbol>>,
        I::IntoIter: ExactSizeIterator,
        'ast: 'e,
    {
        self.typecheck_application_(span, func_type, implicit_args, &mut args.into_iter())
            .map(|typ| (typ, Vec::new()))
    }

    fn typecheck_application_<'e>(
        &mut self,
        span: Span<BytePos>,
        func_type: ModType,
        implicit_args: &mut CowVec<SpannedExpr<'ast, Symbol>>,
        args: &mut dyn ExactSizeIterator<Item = &'e mut SpannedExpr<'ast, Symbol>>,
    ) -> TcResult<ModType>
    where
        'ast: 'e,
    {
        fn attach_extra_argument_help<F, R>(self_: &mut Typecheck, actual: u32, f: F) -> R
        where
            F: FnOnce(&mut Typecheck) -> R,
        {
            let errors_before = self_.errors.len();
            let t = f(self_);
            if errors_before != self_.errors.len() {
                let len = self_.errors.len();
                let expected_type = match self_.errors[len - 1].value.error {
                    TypeError::Unification(ref expected_type, ..) => expected_type.clone(),
                    _ => return t,
                };
                let extra = function_arg_iter(self_, expected_type).count() as u32;
                self_.errors[len - 1].value.help =
                    Some(Help::ExtraArgument(actual - extra, actual));
            }
            t
        }

        let args_len = args.len() as u32;

        let original_func_type = func_type.concrete.clone();
        let mut func_type = self.instantiate_generics(&func_type);

        let mut return_variables = FnvSet::default();

        for arg in &mut **implicit_args {
            let (arg_typ, ret_typ) = self.subsume_function(
                arg.span.start(),
                arg.span,
                ArgType::Implicit,
                func_type.clone(),
                &mut |_| unreachable!(),
            );

            let arg_typ = self.typecheck(arg, ModType::wobbly(&arg_typ));

            if arg_typ.modifier == TypeModifier::Rigid {
                types::walk_type(&self.subs.zonk(&arg_typ), &mut |typ: &RcType| {
                    if let Type::Variable(var) = &**typ {
                        return_variables.insert(var.id);
                    }
                });
            }

            func_type = ret_typ;
        }

        let mut not_a_function_index = None;

        let mut prev_arg_end = implicit_args.last().map_or(span, |arg| arg.span).end();
        for arg in args.map(|arg| arg.borrow_mut()) {
            let errors_before = self.errors.len();
            let (arg_ty, ret_ty) = self.subsume_function(
                prev_arg_end,
                arg.span,
                ArgType::Explicit,
                func_type.clone(),
                &mut |expr| implicit_args.as_owned().push(expr),
            );

            if errors_before != self.errors.len() {
                self.errors.pop();
                not_a_function_index = Some(arg);
                break;
            }

            let arg_ty = self.typecheck(arg, ModType::wobbly(&arg_ty));

            if arg_ty.modifier == TypeModifier::Rigid {
                types::walk_type(&self.subs.zonk(&arg_ty), &mut |typ: &RcType| {
                    if let Type::Variable(var) = &**typ {
                        return_variables.insert(var.id);
                    }
                });
            }

            func_type = ret_ty;

            prev_arg_end = arg.span.end();
        }

        if let Some(arg) = not_a_function_index {
            let span_start = arg.span.start();

            let extra_args = Some(arg).into_iter().chain(args);

            let mut span_end = BytePos::default();
            let arg_types = extra_args
                .map(|arg| {
                    span_end = arg.span.end();
                    self.infer_expr(arg.borrow_mut()).concrete
                })
                .collect::<Vec<_>>();
            let expected = self.subs.function(arg_types, self.subs.new_var());

            let span = Span::new(span_start, span_end);
            attach_extra_argument_help(self, args_len, |self_| {
                self_.subsumes(
                    span,
                    ErrorOrder::ExpectedActual,
                    &expected,
                    func_type.clone(),
                )
            });

            func_type = expected;
        }

        let mut modifier = TypeModifier::Rigid;
        types::FlagsVisitor(Flags::HAS_VARIABLES, |typ: &RcType| {
            if modifier == TypeModifier::Rigid {
                if let Type::Variable(var) = &**typ {
                    if !return_variables.contains(&var.id) {
                        modifier = TypeModifier::Wobbly;
                    }
                }
            }
        })
        .walk(&self.subs.zonk(&original_func_type));

        Ok(ModType::new(modifier, func_type))
    }

    fn typecheck_lambda(
        &mut self,
        function_type: ModType,
        before_args_pos: BytePos,
        args_ref: &mut &'ast mut [Argument<SpannedIdent<Symbol>>],
        body: &mut SpannedExpr<'ast, Symbol>,
    ) -> ModType {
        debug!("Checking lambda {}", function_type);
        debug!("Checking lambda {:#?}", self.environment.skolem_variables);
        self.enter_scope();

        let mut args = CowVec::Borrowed(*args_ref);

        let mut arg_types = Vec::new();

        let body_type = {
            let mut return_type = function_type.clone();

            let mut i = 0;

            while i < args.len()
                || return_type
                    .as_function_with_type()
                    .map_or(false, |(arg_type, _, _)| arg_type == ArgType::Implicit)
            {
                let span = args
                    .get(i)
                    .map(|a| a.name.span)
                    .unwrap_or_else(|| pos::Span::new(before_args_pos, before_args_pos));
                let (type_implicit, arg_type, ret_type) =
                    self.unify_function(span, return_type.concrete.clone());

                match type_implicit {
                    ArgType::Implicit => {
                        let arg = match args.get(i).map(|t| t.arg_type) {
                            Some(ArgType::Implicit) => {
                                i += 1;
                                &mut args[i - 1].name.value
                            }
                            _ => {
                                let id = Symbol::from("__implicit_arg");
                                let pos = if i == 0 {
                                    before_args_pos
                                } else {
                                    args.get(i - 1)
                                        .map(|arg| arg.name.span.end())
                                        .unwrap_or(before_args_pos)
                                };
                                args.as_owned().insert(
                                    i,
                                    Argument::implicit(pos::spanned2(
                                        pos,
                                        pos,
                                        TypedIdent {
                                            typ: self.subs.bind_arc(&arg_type),
                                            name: id.clone(),
                                        },
                                    )),
                                );
                                i += 1;
                                &mut args[i - 1].name.value
                            }
                        };
                        arg.typ = self.subs.bind_arc(&arg_type);
                        arg_types.push(arg_type.clone());
                        self.stack_var(arg.name.clone(), arg_type.clone());
                    }
                    ArgType::Explicit => match args.get_mut(i) {
                        Some(&mut Argument {
                            arg_type: ArgType::Implicit,
                            name: ref arg,
                        }) => {
                            i += 1;
                            self.error(
                                    arg.span,
                                    TypeError::Message(format!(
                                        "Expected implicit argument but an explicit argument was specified"
                                    )),
                                );
                        }
                        Some(&mut Argument {
                            arg_type: ArgType::Explicit,
                            name: ref mut arg,
                        }) => {
                            i += 1;
                            let arg = &mut arg.value;

                            arg.typ = self.subs.bind_arc(&arg_type);
                            arg_types.push(arg_type.clone());
                            self.stack_var(arg.name.clone(), arg_type);
                        }
                        _ => break,
                    },
                    ArgType::Constructor => unreachable!(),
                }
                return_type = ModType::new(function_type.modifier, ret_type);
            }

            return_type
        };

        if let CowVec::Owned(args) = args {
            *args_ref = self.ast_arena.alloc_extend(args);
        }

        let body_type = self.typecheck(body, body_type.as_ref());
        self.exit_scope();

        let f = self.subs.function(arg_types, body_type.concrete);
        let done = self.with_forall(&function_type, ModType::new(body_type.modifier, f));

        debug!("Checked lambda {}", done);
        done
    }

    fn typecheck_let_pattern(
        &mut self,
        pattern: &mut SpannedPattern<Symbol>,
        match_type: RcType,
    ) -> RcType {
        match pattern.value {
            Pattern::Constructor(ref id, _) | Pattern::Ident(ref id)
                if id.name.declared_name().starts_with(char::is_uppercase) =>
            {
                self.error(
                    pattern.span,
                    TypeError::Message(format!("Unexpected type constructor `{}`", id.name)),
                )
            }
            _ => self.typecheck_pattern(pattern, ModType::wobbly(match_type.clone()), match_type),
        }
    }

    fn typecheck_pattern(
        &mut self,
        pattern: &mut SpannedPattern<Symbol>,
        mut match_type: ModType,
        partial_match_type: RcType,
    ) -> RcType {
        let span = pattern.span;
        match &mut pattern.value {
            Pattern::As(id, pat) => {
                self.stack_var(id.value.clone(), partial_match_type.clone());
                self.typecheck_pattern(pat, match_type.clone(), partial_match_type.clone());
                partial_match_type
            }
            Pattern::Constructor(id, args) => {
                match_type.concrete = self.subs.real(&match_type).clone();
                match_type.concrete = self.instantiate_generics(&match_type);
                match_type.concrete = self.subs.zonk(&match_type);
                // Find the enum constructor and return the types for its arguments
                let ctor_type = self.find_at(span, &id.name);

                id.typ = self.subs.bind_arc(&ctor_type);

                debug!("Wobbly check {:?}: {}", match_type.modifier, match_type);
                let wobbly = match_type.modifier == TypeModifier::Wobbly;
                let ctor_type = if wobbly {
                    self.instantiate_generics(&ctor_type)
                } else {
                    self.skolemize(&ctor_type)
                };

                let return_type = ctor_return_type(&ctor_type);
                if wobbly {
                    self.subsumes(
                        span,
                        ErrorOrder::ExpectedActual,
                        &return_type,
                        match_type.concrete,
                    );
                } else {
                    self.refines(
                        span,
                        ErrorOrder::ExpectedActual,
                        &return_type,
                        match_type.concrete,
                    );
                }

                match self.typecheck_pattern_rec(args, &ctor_type) {
                    Ok(return_type) => return_type,
                    Err(err) => self.error(span, err),
                }
            }
            Pattern::Record {
                typ: curr_typ,
                fields,
                implicit_import,
            } => {
                let uninstantiated_match_type = match_type.clone();
                match_type.concrete = self.instantiate_generics(&match_type);
                *curr_typ = self.subs.bind_arc(&match_type);

                let mut pattern_fields = Vec::with_capacity(fields.len());

                let mut duplicated_fields = FnvSet::default();
                {
                    let all_fields = fields.iter().map(|field| match field {
                        PatternField::Type { name } | PatternField::Value { name, .. } => name,
                    });
                    for field in all_fields {
                        if self.error_on_duplicated_field(&mut duplicated_fields, &field) {
                            pattern_fields.push(field.value.clone());
                        }
                    }
                }

                let record_match_type = self.remove_alias(match_type.concrete.clone());

                let mut missing_fields_from_match_type = Vec::new();

                for (name, value) in ast::pattern_values_mut(fields) {
                    let name = &name.value;
                    // The field should always exist since the type was constructed from the pattern
                    let field_type = record_match_type
                        .row_iter()
                        .find(|f| f.name.name_eq(name))
                        .map(|f| f.typ.clone())
                        .unwrap_or_else(|| {
                            let typ = self.subs.new_var();
                            missing_fields_from_match_type.push(Field {
                                name: name.clone(),
                                typ: typ.clone(),
                            });
                            typ
                        });
                    match value {
                        Some(pattern) => {
                            self.typecheck_pattern(
                                pattern,
                                ModType::new(match_type.modifier, field_type.clone()),
                                field_type,
                            );
                        }
                        None => {
                            self.stack_var(name.clone(), field_type);
                        }
                    }
                }

                // Check that all types declared in the pattern exists
                for name in ast::pattern_types(fields) {
                    let span = name.span;
                    let name = name.value.clone();
                    // The `types` in the record type should have a type matching the
                    // `name`
                    let field_type = record_match_type
                        .type_field_iter()
                        .find(|field| field.name.name_eq(&name));

                    let alias;
                    let alias = match field_type {
                        Some(field_type) => {
                            if let Some(meta) = self.implicit_resolver.metadata.remove(&name) {
                                self.implicit_resolver
                                    .metadata
                                    .insert(field_type.typ.name.clone(), meta);
                            }
                            &field_type.typ
                        }
                        None => {
                            self.error(
                                span,
                                TypeError::UndefinedField(
                                    match_type.concrete.clone(),
                                    name.clone(),
                                ),
                            );
                            // We still define the type so that any uses later on in the program
                            // won't error on UndefinedType
                            let hole = self.subs.error();
                            alias = self.new_alias(name.clone(), Vec::new(), hole);
                            &alias
                        }
                    };

                    self.stack_type(name, &alias);
                }

                if !missing_fields_from_match_type.is_empty() {
                    let expected = self.subs.poly_record(
                        vec![],
                        missing_fields_from_match_type,
                        self.subs.new_var(),
                    );
                    self.unify_span(pattern.span, &expected, match_type.concrete.clone());
                }

                if let Some(ref implicit_import) = *implicit_import {
                    self.implicit_resolver.add_implicits_of_record(
                        &self.subs,
                        &implicit_import.value,
                        &uninstantiated_match_type,
                    );
                }

                match_type.concrete
            }
            Pattern::Tuple { typ, elems } => {
                let tuple_type = {
                    let subs = &mut self.subs;
                    (&*subs).tuple(&mut self.symbols, (0..elems.len()).map(|_| subs.new_var()))
                };
                let new_type = self.unify_span(span, &tuple_type, match_type.concrete);
                *typ = self.subs.bind_arc(&new_type);
                for (elem, field) in elems.iter_mut().zip(tuple_type.row_iter()) {
                    self.typecheck_pattern(
                        elem,
                        ModType::new(match_type.modifier, field.typ.clone()),
                        field.typ.clone(),
                    );
                }
                tuple_type
            }
            Pattern::Ident(id) => {
                self.stack_var(id.name.clone(), partial_match_type.clone());
                id.typ = self.subs.bind_arc(&partial_match_type);
                partial_match_type
            }
            Pattern::Literal(l) => {
                let typ = l.env_type_of(&self.environment);
                let typ = self.translate_arc_type(&typ);
                self.unify_span(span, &match_type, typ);
                match_type.concrete
            }
            Pattern::Error => self.subs.new_var(),
        }
    }

    fn typecheck_pattern_rec(
        &mut self,
        args: &mut [SpannedPattern<Symbol>],
        typ: &RcType,
    ) -> TcResult<RcType> {
        let pattern_args = args.len();
        let mut pattern_iter = args.iter_mut();
        let mut type_iter = typ.arg_iter();
        loop {
            match (pattern_iter.next(), type_iter.next()) {
                (Some(arg_pattern), Some(arg)) => {
                    self.typecheck_pattern(arg_pattern, ModType::wobbly(arg.clone()), arg.clone());
                }
                (None, Some(_)) | (Some(_), None) => {
                    return Err(TypeError::PatternError {
                        constructor_type: typ.clone(),
                        pattern_args,
                    })
                }
                (None, None) => break,
            }
        }
        Ok(typ.clone())
    }

    fn translate_projected_type(&mut self, id: &[Symbol]) -> TcResult<RcType> {
        translate_projected_type(&self.environment, &mut self.symbols, &mut &self.subs, id)
    }

    // Stub kept in case multiple types are attempted again
    fn translate_arc_type(&mut self, arc_type: &ArcType) -> RcType {
        arc_type.clone()
    }

    // Stub kept in case multiple types are attempted again
    fn translate_rc_type(&mut self, rc_type: &RcType) -> ArcType {
        rc_type.clone()
    }

    fn translate_ast_type(&mut self, ast_type: &AstType<Symbol>) -> RcType {
        use crate::base::pos::HasSpan;

        match **ast_type {
            // Undo the hack in kindchecking that inserts a dummy alias wrapping a generic
            Type::Alias(ref alias) => match **alias.unresolved_type() {
                Type::Generic(ref gen) if gen.id == alias.name => self.ident(KindedIdent {
                    name: alias.name.clone(),
                    typ: alias.kind(&self.kind_cache).into_owned(),
                }),
                _ => types::translate_type_with(self, ast_type, |self_, typ| {
                    self_.translate_ast_type(typ)
                }),
            },

            Type::ExtendTypeRow {
                ref types,
                ref rest,
            } => {
                let types = types
                    .iter()
                    .map(|field| Field {
                        name: field.name.value.clone(),
                        typ: if let Type::Hole = **field.typ.unresolved_type() {
                            self.find_type_info_at(
                                field.typ.unresolved_type().span(),
                                &field.name.value,
                            )
                        } else {
                            let alias_data =
                                types::translate_alias(self, &field.typ, |self_, typ| {
                                    self_.translate_ast_type(typ)
                                });
                            self.new_data_alias(alias_data)
                        },
                    })
                    .collect();

                let rest = self.translate_ast_type(rest);

                self.extend_type_row(types, rest)
            }

            Type::Projection(ref ids) => match self.translate_projected_type(ids) {
                Ok(typ) => typ,
                Err(err) => self.error(ast_type.span(), err),
            },

            _ => types::translate_type_with(self, ast_type, |self_, typ| {
                self_.translate_ast_type(typ)
            }),
        }
    }

    fn typecheck_bindings(
        &mut self,
        top_level: bool,
        mut expr: &mut SpannedExpr<'ast, Symbol>,
        expected_type: Option<ModTypeRef>,
    ) -> ModType {
        let mut scope_count = 0;

        let level = self.subs.var_id();

        loop {
            match expr.value {
                Expr::LetBindings(ref mut bindings, ref mut body) => {
                    self.typecheck_let_bindings(bindings);

                    scope_count += 1;

                    if top_level {
                        self.generalize_and_clear_subs(level, bindings);
                    }

                    expr = body
                }
                Expr::TypeBindings(ref mut bindings, ref mut body) => {
                    self.typecheck_type_bindings(bindings, body);

                    scope_count += 1;

                    expr = body;
                }
                _ => {
                    let typ = self.typecheck_opt(expr, expected_type);

                    for _ in 0..scope_count {
                        self.exit_scope();
                    }

                    return typ;
                }
            }
        }
    }

    fn resolve_type_signature(
        &mut self,
        mut signature: Option<&mut AstType<'_, Symbol>>,
    ) -> ModType {
        let mut mod_type = if let Some(ref mut typ) = signature {
            self.kindcheck(typ);
            let rc_type = self.translate_ast_type(typ);

            ModType::rigid(rc_type)
        } else {
            ModType::wobbly(self.subs.hole())
        };

        if let Some(typ) = self.create_unifiable_signature(&mod_type) {
            mod_type.concrete = typ;
        }
        mod_type
    }

    fn typecheck_let_bindings(&mut self, bindings: &mut ValueBindings<'ast, Symbol>) {
        self.enter_scope();
        self.environment.skolem_variables.enter_scope();
        self.environment.type_variables.enter_scope();
        let level = self.subs.var_id();

        let is_recursive = bindings.is_recursive();
        let mut resolved_types = AppVec::new();
        // When the definitions are allowed to be mutually recursive
        if is_recursive {
            for (i, bind) in bindings.iter_mut().enumerate() {
                let typ = {
                    resolved_types.push(self.resolve_type_signature(bind.typ.as_mut()));

                    resolved_types[i].concrete.clone()
                };
                self.typecheck_let_pattern(&mut bind.name, typ);
            }
        }

        let mut types = Vec::new();
        for (i, bind) in bindings.iter_mut().enumerate() {
            // Functions which are declared as `let f x = ...` are allowed to be self
            // recursive
            let typ = if !is_recursive {
                if let Some(ref mut typ) = bind.typ {
                    self.kindcheck(typ);
                    let rc_type = self.translate_ast_type(typ);

                    resolved_types.push(ModType::rigid(rc_type));
                } else {
                    resolved_types.push(ModType::wobbly(self.subs.hole()));
                }

                let typ = self.create_unifiable_signature(&resolved_types[i]);
                if let Some(typ) = typ {
                    resolved_types[i].concrete = typ;
                }

                let typ = resolved_types[i].as_ref();
                self.skolemize_in(bind.expr.span, typ, |self_, typ| {
                    self_
                        .environment
                        .type_variables
                        .extend(self_.named_variables.drain());

                    self_.typecheck_lambda(
                        typ,
                        bind.name.span.end(),
                        &mut bind.args,
                        &mut bind.expr,
                    )
                })
            } else {
                let typ = match bind.name.value {
                    Pattern::Ident(ref id) => {
                        let mut type_cache = &self.subs;
                        self.environment
                            .stack
                            .get(&id.name)
                            .map_or_else(|| ModType::wobbly(type_cache.error()), |b| b.typ.clone())
                    }
                    _ => ModType::wobbly(self.subs.error()),
                };

                self.skolemize_in_no_scope(bind.expr.span, typ.as_ref(), |self_, function_type| {
                    self_
                        .environment
                        .type_variables
                        .extend(self_.named_variables.drain());

                    self_.typecheck_lambda(
                        function_type,
                        bind.name.span.end(),
                        &mut bind.args,
                        &mut bind.expr,
                    )
                })
            };

            debug!("let {:?} : {}", bind.name, typ);

            if !is_recursive {
                let resolved_type = &mut resolved_types[i].concrete;
                bind.resolved_type = self.subs.bind_arc(&resolved_type);
                // Merge the type declaration and the actual type
                debug!("Generalize at {} = {}", level, resolved_type);
                self.generalize_binding(level, resolved_type, bind);
                debug!("Generalized mid {}", resolved_type);
                self.typecheck_let_pattern(&mut bind.name, resolved_type.clone());
                debug!("Generalized to {}", bind.resolved_type);
                self.finish_pattern(level, &mut bind.name, &resolved_type);
            } else {
                types.push(typ);
            }
        }

        if is_recursive {
            let hole = self.subs.hole();
            {
                let mut generalizer =
                    TypeGeneralizer::new(level, self, &hole, bindings[0].name.span);

                // Once all variables inside the let has been unified we can quantify them
                debug!("Generalize recursive at {}", level);
                for (bind, resolved_type) in bindings.iter_mut().zip(&mut resolved_types) {
                    bind.resolved_type = generalizer.tc.subs.bind_arc(&resolved_type);
                    debug!(
                        "Generalize {}: {}",
                        match bind.name.value {
                            ast::Pattern::Ident(ref id) => id.name.declared_name(),
                            _ => "",
                        },
                        resolved_type
                    );
                    generalize_binding(&mut generalizer, resolved_type, bind);
                    debug!("Generalize mid {}", resolved_type);
                    generalizer
                        .tc
                        .finish_pattern(level, &mut bind.name, &resolved_type);
                    debug!("Generalized to {}", resolved_type);
                }
            }

            debug!("End generalize recursive");
        }

        debug!("Typecheck `in`");
        self.environment.type_variables.exit_scope();
        self.environment.skolem_variables.exit_scope();
    }

    fn typecheck_type_bindings(
        &mut self,
        bindings: &mut [TypeBinding<Symbol>],
        expr: &SpannedExpr<'ast, Symbol>,
    ) {
        self.enter_scope();

        // Rename the types so they get a name which is distinct from types from other
        // modules
        for bind in bindings.iter_mut() {
            self.environment.skolem_variables.enter_scope();
            self.environment.type_variables.enter_scope();

            {
                let mut type_cache = &self.subs;
                for (k, v) in bind
                    .alias
                    .value
                    .params()
                    .iter()
                    .map(|param| (param.id.clone(), type_cache.hole()))
                {
                    self.environment
                        .skolem_variables
                        .insert(k.clone(), v.clone());
                    self.environment.type_variables.insert(k, v);
                }
            }
            self.check_type_binding(&bind.alias.value.name, bind.alias.value.unresolved_type());

            self.environment.type_variables.exit_scope();
            self.environment.skolem_variables.exit_scope();
        }

        {
            let mut check = KindCheck::new(
                &self.environment,
                &mut self.symbols,
                self.kind_cache.clone(),
            );

            // Setup kind variables for all holes and insert the types in the
            // the type expression into the kindcheck environment
            for bind in &mut *bindings {
                // Create the kind for this binding
                // Test a b : 2 -> 1 -> Type
                // and bind the same variables to the arguments of the type binding
                // ('a' and 'b' in the example)
                let mut id_kind = check.type_kind();
                for generic in bind.alias.value.params_mut().iter_mut().rev() {
                    check.instantiate_kinds(&mut generic.kind);
                    id_kind = Kind::function(generic.kind.clone(), id_kind);
                }
                check.add_local(bind.alias.value.name.clone(), id_kind);
            }

            // Kindcheck all the types in the environment
            for bind in &mut *bindings {
                check.enter_scope_with(
                    bind.alias
                        .value
                        .params()
                        .iter()
                        .map(|g| (g.id.clone(), g.kind.clone())),
                );

                let typ = bind
                    .alias
                    .value
                    .unresolved_type_mut()
                    .remove_single_forall();
                if let Err(errors) = check.kindcheck_type(typ) {
                    self.errors.extend(
                        errors
                            .into_iter()
                            .map(|err| pos::spanned(err.span, TypeError::from(err.value).into())),
                    );
                }
                check.exit_scope();
            }

            // All kinds are now inferred so replace the kinds store in the AST
            for bind in &mut *bindings {
                {
                    let typ = bind.alias.value.unresolved_type_mut();
                    check.finalize_type(typ);
                }
                for arg in bind.alias.value.params_mut() {
                    *arg = check.finalize_generic(arg);
                }
            }
        }

        let mut resolved_aliases = Vec::new();
        for bind in &mut *bindings {
            self.environment.skolem_variables.enter_scope();
            self.environment.type_variables.enter_scope();

            let mut alias = types::translate_alias(self, &bind.alias.value, |self_, typ| {
                self_.translate_ast_type(typ)
            });

            alias.is_implicit = bind.metadata.get_attribute("implicit").is_some();

            let replacement = self.create_unifiable_signature_with(
                // alias.unresolved_type() is a dummy in this context
                alias
                    .params()
                    .iter()
                    .map(|param| (param.id.clone(), alias.unresolved_type().clone())),
                alias.unresolved_type(),
            );

            if let Some(typ) = replacement {
                *alias.unresolved_type_mut() = typ;
            }
            resolved_aliases.push(alias);

            self.environment.type_variables.exit_scope();
            self.environment.skolem_variables.exit_scope();
        }

        let arc_alias_group = Alias::group(
            resolved_aliases
                .iter()
                .map(|a| types::translate_alias(self, &a, |self_, t| self_.translate_rc_type(t)))
                .collect(),
        );
        let alias_group = self.subs.alias_group(resolved_aliases);
        for (bind, alias) in bindings.iter_mut().zip(arc_alias_group) {
            bind.finalized_alias = Some(alias);
        }

        // Finally insert the declared types into the global scope
        for (bind, alias) in bindings.iter().zip(&alias_group) {
            if self.environment.stack_types.get(&bind.name.value).is_some() {
                self.errors.push(Spanned {
                    span: expr_check_span(expr),
                    // TODO Help to the position of the other field
                    value: TypeError::DuplicateTypeDefinition(bind.name.value.clone()).into(),
                });
            } else {
                self.stack_type(bind.name.value.clone(), alias);
            }
        }
    }

    fn kindcheck(&mut self, typ: &mut AstType<Symbol>) {
        let result = {
            let mut check = KindCheck::new(
                &self.environment,
                &mut self.symbols,
                self.kind_cache.clone(),
            );
            check.kindcheck_type(typ)
        };
        if let Err(errors) = result {
            self.errors.extend(
                errors
                    .into_iter()
                    .map(|err| pos::spanned(err.span, TypeError::from(err.value).into())),
            );
        }
    }

    fn check_type_binding(&mut self, alias_name: &Symbol, typ: &AstType<'_, Symbol>) {
        use crate::base::pos::HasSpan;
        match &**typ {
            Type::Generic(id) => {
                if !self.environment.type_variables.contains_key(&id.id) {
                    info!("Undefined type variable {}", id.id);
                    self.error(typ.span(), TypeError::UndefinedVariable(id.id.clone()));
                }
            }

            Type::Variant(row) => {
                for field in types::row_iter(row) {
                    let spine = ctor_return_type(&field.typ).spine();
                    match &**spine {
                        Type::Ident(id) if id.name == *alias_name => (),
                        Type::Opaque => (),
                        _ => {
                            let actual = self.translate_ast_type(spine);
                            self.error(
                                spine.span(),
                                TypeError::TypeConstructorReturnsWrongType {
                                    expected: alias_name.clone(),
                                    actual,
                                },
                            );
                        }
                    }
                    self.check_type_binding(alias_name, &field.typ);
                }
            }

            Type::Record(_) => {
                // Inside records variables are bound implicitly to the closest field
                // so variables are allowed to be undefined/implicit
            }

            _ => {
                if let Type::Forall(params, ..) = &**typ {
                    let mut type_cache = &self.subs;
                    self.environment
                        .type_variables
                        .extend(params.iter().map(|gen| (gen.id.clone(), type_cache.hole())));
                }
                types::walk_type_(
                    typ,
                    &mut types::ControlVisitation(|typ: &AstType<'_, _>| {
                        self.check_type_binding(alias_name, typ)
                    }),
                );
            }
        }
    }

    fn update_var(&mut self, id: &Symbol, typ: &RcType) {
        if let Some(bind) = self.environment.stack.get_mut(id) {
            if let Type::Variable(_) = **bind.typ {
                self.implicit_resolver.on_stack_var(&self.subs, id, typ);
            }
            bind.typ.concrete = typ.clone();
        }
        // HACK
        // For type projections
        let id = self.symbols.simple_symbol(id.declared_name());
        if let Some(bind) = self.environment.stack.get_mut(&id) {
            bind.typ.concrete = typ.clone();
        }
    }

    fn finish_pattern(
        &mut self,
        level: u32,
        pattern: &mut SpannedPattern<Symbol>,
        final_type: &RcType,
    ) {
        match pattern.value {
            Pattern::As(ref mut id, ref mut pat) => {
                self.finish_pattern(level, pat, &final_type);

                self.update_var(&id.value, &final_type);

                debug!("{}: {}", self.symbols.string(&id.value), final_type);
            }
            Pattern::Ident(ref mut id) => {
                id.typ = self.subs.bind_arc(&final_type);
                self.update_var(&id.name, &final_type);
                debug!("{}: {}", self.symbols.string(&id.name), id.typ);
            }
            Pattern::Record {
                ref mut typ,
                ref mut fields,
                ..
            } => {
                *typ = self.subs.bind_arc(final_type);
                let mut typ = final_type.clone();
                debug!("{{ .. }}: {}", final_type);

                self.generalize_type(level, &mut typ, pattern.span);
                let typ = self.instantiate_generics(&typ);
                let record_type = self.remove_alias(typ.clone());

                for (field_name, binding, field_type) in with_pattern_types(fields, &record_type) {
                    let mut field_type = field_type.cloned().unwrap_or_else(|| self.subs.error());
                    self.generalize_type(level, &mut field_type, field_name.span);
                    match *binding {
                        Some(ref mut pat) => {
                            self.finish_pattern(level, pat, &field_type);
                        }
                        None => {
                            self.update_var(&field_name.value, &field_type);
                            debug!("{}: {}", field_name.value, field_type);
                        }
                    }
                }
            }
            Pattern::Tuple {
                ref mut typ,
                ref mut elems,
            } => {
                *typ = self.subs.bind_arc(final_type);
                let typ = final_type.clone();

                let typ = self.instantiate_generics(&typ);
                for (elem, field) in elems.iter_mut().zip(typ.row_iter()) {
                    let mut field_type = field.typ.clone();
                    self.generalize_type(level, &mut field_type, elem.span);
                    self.finish_pattern(level, elem, &field_type);
                }
            }
            Pattern::Constructor(ref mut id, ref mut args) => {
                debug!("{}: {}", self.symbols.string(&id.name), final_type);
                let len = args.len();
                let iter = args.iter_mut().zip(
                    function_arg_iter(self, final_type.clone())
                        .map(|t| t.1)
                        .take(len)
                        .collect::<Vec<_>>(),
                );
                for (arg, arg_type) in iter {
                    self.finish_pattern(level, arg, &arg_type);
                }
            }
            Pattern::Literal(_) | Pattern::Error => (),
        }
    }

    // At the top level we know we can generalize all variables, letting us clear the substitution
    // and start fresh
    fn generalize_and_clear_subs(&mut self, level: u32, binds: &mut ValueBindings<Symbol>) {
        debug!("Clearing from: {}", level);
        {
            let hole = self.subs.hole();

            let mut generalizer = TypeGeneralizer::new(level, self, &hole, binds[0].span());
            for bind in &mut *binds {
                generalize::ReplaceVisitor {
                    generalizer: &mut generalizer,
                }
                .visit_pattern(&mut bind.name);

                generalizer.generalize_variables(
                    &mut bind.args.iter_mut().map(|arg| &mut arg.name),
                    &mut bind.expr,
                );
                generalizer.generalize_type_mut(&mut bind.resolved_type);
            }
        }

        let mut errors = mem::replace(&mut self.errors, Default::default());
        self.generalize_type_errors(&mut errors);
        self.errors = errors;

        // Clear any location which could have skolems or variables left in them
        self.named_variables.clear();
        self.implicit_resolver.implicit_vars.clear();

        self.subs.clear_from(level);
    }

    fn generalize_type(&mut self, level: u32, typ: &mut RcType, span: Span<BytePos>) {
        debug!("Start generalize {:#?}", self.environment.skolem_variables);
        debug!("Start generalize {} >> {}", level, typ);
        let mut generalizer = TypeGeneralizer::new(level, self, typ, span);
        generalizer.generalize_type_top(typ);
    }

    fn generalize_type_without_forall(
        &mut self,
        level: u32,
        typ: &mut RcType,
        span: Span<BytePos>,
    ) {
        self.environment.skolem_variables.enter_scope();

        let mut generalizer = TypeGeneralizer::new(level, self, typ, span);
        let result_type = generalizer.generalize_type(typ);

        generalizer.environment.skolem_variables.exit_scope();

        if let Some(finished) = result_type {
            *typ = finished;
        }
    }

    // Replaces `Type::Id` types with the actual `Type::Alias` type it refers to
    // Replaces variant names with the actual symbol they should refer to
    // Instantiates Type::Hole with a fresh type variable to ensure the hole only ever refers to a
    // single type variable.
    //
    // Also inserts a `forall` for any implicitly declared variables.
    fn create_unifiable_signature(&mut self, typ: &RcType) -> Option<RcType> {
        self.create_unifiable_signature_with(None, typ)
    }

    fn create_unifiable_signature_with(
        &mut self,
        scope: impl IntoIterator<Item = (Symbol, RcType)>,
        typ: &RcType,
    ) -> Option<RcType> {
        debug!("Creating signature: {:#?}", typ);

        for (k, v) in scope {
            self.environment
                .skolem_variables
                .insert(k.clone(), v.clone());
            self.environment.type_variables.insert(k, v);
        }

        let opt = self.create_unifiable_signature2(typ);
        debug!("Created signature: {:#?}", opt.as_ref().unwrap_or(typ));
        opt
    }

    fn create_unifiable_signature2(&mut self, typ: &RcType) -> Option<RcType> {
        debug!("Signature scope: {}", typ);

        self.unbound_variables.enter_scope();
        let result_type = self.create_unifiable_signature_(typ);

        let mut params = self
            .unbound_variables
            .exit_scope()
            .map(|(id, kind)| Generic::new(id, kind))
            .collect::<Vec<_>>();
        params.retain(|generic| !self.unbound_variables.contains_key(&generic.id));

        if params.is_empty() {
            result_type
        } else {
            let result = self.intern(Type::Forall(
                params,
                result_type.unwrap_or_else(|| typ.clone()),
            ));
            debug!("Signature scope END: {}", result);
            Some(result)
        }
    }

    fn create_unifiable_signature_(&mut self, typ: &RcType) -> Option<RcType> {
        match **typ {
            Type::Ident(ref id) => {
                // Substitute the Id by its alias if possible
                self.environment
                    .find_type_info(&id.name)
                    .map(|alias| alias.clone().into_type())
            }

            // Due to a hack in the kindchecker that inserts a dummy generic we need to replace aliases as well
            Type::Alias(ref alias) => {
                // Substitute the Id by its alias if possible
                self.environment
                    .find_type_info(&alias.name)
                    .map(|alias| alias.clone().into_type())
            }

            Type::Variant(ref row) => {
                let replacement = types::visit_type_opt(
                    row,
                    &mut types::InternerVisitor::control(self, |self_: &mut Self, typ: &RcType| {
                        self_.create_unifiable_signature_(typ)
                    }),
                );
                replacement
                    .clone()
                    .map(|row| self.intern(Type::Variant(row)))
            }

            Type::Hole => Some(self.subs.new_var()),

            Type::ExtendRow {
                ref fields,
                ref rest,
            } => {
                let new_fields = types::walk_move_types(&mut (), fields, |_, field| {
                    self.create_unifiable_signature2(&field.typ)
                        .map(|typ| Field::new(field.name.clone(), typ))
                });
                let new_rest = self.create_unifiable_signature_(rest);
                merge::merge(fields, new_fields, rest, new_rest, |fields, rest| {
                    self.intern(Type::ExtendRow { fields, rest })
                })
            }

            Type::ExtendTypeRow {
                ref types,
                ref rest,
            } => {
                let new_types = types::walk_move_types(&mut (), types, |_, field| {
                    let typ = self
                        .create_unifiable_signature_with(
                            field.typ.params().iter().map(|param| {
                                (param.id.clone(), field.typ.unresolved_type().clone())
                            }),
                            field.typ.unresolved_type(),
                        )
                        .unwrap_or_else(|| field.typ.unresolved_type().clone());
                    Some(Field::new(
                        field.name.clone(),
                        self.new_alias(field.typ.name.clone(), field.typ.params().to_owned(), typ),
                    ))
                });

                let new_rest = self.create_unifiable_signature_(rest);

                merge::merge(types, new_types, rest, new_rest, |types, rest| {
                    self.intern(Type::ExtendTypeRow { types, rest })
                })
            }

            Type::Forall(ref params, ref typ) => {
                self.environment.type_variables.enter_scope();

                let mut subs = &self.subs;
                self.environment
                    .type_variables
                    .extend(params.iter().map(|param| (param.id.clone(), subs.hole())));

                let result = self.create_unifiable_signature_(typ);

                self.environment.type_variables.exit_scope();

                result.map(|typ| self.intern(Type::Forall(params.clone(), typ)))
            }

            Type::Generic(ref generic) => {
                if let Some(typ) = self.environment.type_variables.get(&generic.id) {
                    match **typ {
                        Type::Skolem(_) => Some(typ.clone()),
                        _ => None,
                    }
                } else {
                    self.unbound_variables
                        .entry(generic.id.clone())
                        .or_insert_with(|| generic.kind.clone());
                    None
                }
            }

            _ => types::walk_move_type_opt(
                typ,
                &mut types::InternerVisitor::control(self, |self_: &mut Self, typ: &RcType| {
                    self_.create_unifiable_signature_(typ)
                }),
            ),
        }
    }

    fn subsumes_expr(
        &mut self,
        span: Span<BytePos>,
        l: &RcType,
        r: RcType,
        expr: &mut SpannedExpr<'ast, Symbol>,
    ) -> RcType {
        let mut implicit_args = match &mut expr.value {
            Expr::App { implicit_args, .. } => implicit_args.iter_mut().map(mem::take).collect(),
            _ => Vec::new(),
        };
        let new = self.subsumes_implicit(
            span,
            ErrorOrder::ExpectedActual,
            &r,
            l.clone(),
            &mut |arg| {
                implicit_args.push(pos::spanned(expr.span, arg));
            },
        );

        match &mut expr.value {
            Expr::App {
                implicit_args: current,
                ..
            } => *current = self.ast_arena.alloc_extend(implicit_args),
            _ => {
                if !implicit_args.is_empty() {
                    let func = mem::take(&mut expr.value);
                    expr.value = Expr::App {
                        func: self.ast_arena.alloc(pos::spanned(expr.span, func)),
                        implicit_args: self.ast_arena.alloc_extend(implicit_args),
                        args: &mut [],
                    }
                }
            }
        }

        // We ended up skolemizing r. To prevent the variables from looking like they
        // are escaping we need to bind the forall at this location
        if let Type::Forall(..) = *new {
            let temp = mem::replace(expr, Default::default());
            *expr = Expr::annotated(self.ast_arena, temp, self.subs.bind_arc(&new));
        }
        new
    }

    fn subsumes_implicit(
        &mut self,
        span: Span<BytePos>,
        error_order: ErrorOrder,
        expected: &RcType,
        actual: RcType,
        receiver: &mut dyn FnMut(Expr<'ast, Symbol>),
    ) -> RcType {
        debug!("Subsume expr {} <=> {}", expected, actual);

        self.environment.skolem_variables.enter_scope();

        let state = unify_type::State::new(&self.environment, &self.subs);

        let implicit_resolver = &mut self.implicit_resolver;
        let mut receiver = |implicit_type: &RcType| {
            let name = implicit_resolver.make_implicit_ident(implicit_type);

            receiver(Expr::Ident(TypedIdent {
                name,
                typ: implicit_type.clone(),
            }));
        };
        let typ = match unify_type::subsumes_implicit(
            &self.subs,
            state,
            &expected,
            &actual,
            &mut receiver,
        ) {
            Ok(typ) => typ,
            Err((typ, mut errors)) => {
                let expected = expected.clone();
                debug!(
                    "Error '{}' between:\n>> {}\n>> {}",
                    errors, expected, actual
                );
                let err = match error_order {
                    ErrorOrder::ExpectedActual => {
                        TypeError::Unification(expected, actual, errors.into())
                    }
                    ErrorOrder::ActualExpected => {
                        for err in &mut errors {
                            match err {
                                unify::Error::TypeMismatch(l, r) => mem::swap(l, r),
                                unify::Error::Other(unify_type::TypeError::FieldMismatch(l, r)) => {
                                    mem::swap(l, r)
                                }
                                _ => (),
                            }
                        }
                        TypeError::Unification(actual, expected, errors.into())
                    }
                };
                self.errors.push(Spanned {
                    span: span,
                    // TODO Help what caused this unification failure
                    value: err.into(),
                });
                typ
            }
        };

        self.environment.skolem_variables.exit_scope();

        typ
    }

    fn subsumes(
        &mut self,
        span: Span<BytePos>,
        error_order: ErrorOrder,
        expected: &RcType,
        actual: RcType,
    ) -> RcType {
        debug!("Merge {} : {}", expected, actual);
        let state = unify_type::State::new(&self.environment, &self.subs);
        match unify_type::subsumes(&self.subs, state, &expected, &actual) {
            Ok(typ) => typ,
            Err((typ, mut errors)) => {
                let expected = expected.clone();
                debug!(
                    "Error '{}' between:\n>> {}\n>> {}",
                    errors, expected, actual
                );
                let err = match error_order {
                    ErrorOrder::ExpectedActual => {
                        TypeError::Unification(expected, actual, errors.into())
                    }
                    ErrorOrder::ActualExpected => {
                        for err in &mut errors {
                            match err {
                                unify::Error::TypeMismatch(l, r) => mem::swap(l, r),
                                unify::Error::Other(unify_type::TypeError::FieldMismatch(l, r)) => {
                                    mem::swap(l, r)
                                }
                                _ => (),
                            }
                        }
                        TypeError::Unification(actual, expected, errors.into())
                    }
                };
                self.errors.push(Spanned {
                    span: span,
                    // TODO Help what caused this unification failure
                    value: err.into(),
                });
                typ
            }
        }
    }

    fn refines(
        &mut self,
        span: Span<BytePos>,
        error_order: ErrorOrder,
        expected: &RcType,
        actual: RcType,
    ) -> RcType {
        debug!("Refine {} : {}", expected, actual);
        types::walk_type(&actual, &mut |typ: &RcType| {
            if let Type::Skolem(skolem) = &**self.subs.real(typ) {
                self.refined_variables.entry(skolem.id).or_insert(());
            }
        });
        let state = unify_type::State::with_refinement(&self.environment, &self.subs, true);
        match unify_type::subsumes(&self.subs, state, &expected, &actual) {
            Ok(typ) => typ,
            Err((typ, mut errors)) => {
                let expected = expected.clone();
                debug!(
                    "Error '{}' between:\n>> {}\n>> {}",
                    errors, expected, actual
                );
                let err = match error_order {
                    ErrorOrder::ExpectedActual => {
                        TypeError::Unification(expected, actual, errors.into())
                    }
                    ErrorOrder::ActualExpected => {
                        for err in &mut errors {
                            match err {
                                unify::Error::TypeMismatch(l, r) => mem::swap(l, r),
                                unify::Error::Other(unify_type::TypeError::FieldMismatch(l, r)) => {
                                    mem::swap(l, r)
                                }
                                _ => (),
                            }
                        }
                        TypeError::Unification(actual, expected, errors.into())
                    }
                };
                self.errors.push(Spanned {
                    span: span,
                    // TODO Help what caused this unification failure
                    value: err.into(),
                });
                typ
            }
        }
    }

    fn instantiate_sigma(
        &mut self,
        span: Span<BytePos>,
        typ: &RcType,
        expected_type: &mut Option<&RcType>,
    ) -> (Vec<SpannedExpr<'ast, Symbol>>, RcType) {
        match expected_type.take() {
            Some(expected_type) => {
                debug!("Instantiate sigma: {} <> {}", expected_type, typ);
                let mut implicit_args = Vec::new();
                let t = self.subsumes_implicit(
                    span,
                    ErrorOrder::ExpectedActual,
                    &expected_type,
                    typ.clone(),
                    &mut |implicit_arg| {
                        implicit_args.push(pos::spanned(span, implicit_arg));
                    },
                );
                (implicit_args, t)
            }
            None => {
                debug!("Instantiate sigma: {}", typ);
                (Vec::new(), self.instantiate_generics(typ))
            }
        }
    }

    fn subsume_function(
        &mut self,
        prev_arg_end: BytePos,
        span: Span<BytePos>,
        arg_type: ArgType,
        actual: RcType,
        implicit_args: &mut dyn FnMut(SpannedExpr<'ast, Symbol>),
    ) -> (RcType, RcType) {
        let (_, a, r) = self.merge_function(Some(arg_type), actual, &mut |self_, f, actual| {
            self_.subsumes_implicit(
                span,
                ErrorOrder::ExpectedActual,
                &f,
                actual,
                &mut |implicit_arg| {
                    implicit_args(pos::spanned2(prev_arg_end, span.start(), implicit_arg))
                },
            );
        });
        (a, r)
    }

    fn unify_function(&mut self, span: Span<BytePos>, actual: RcType) -> (ArgType, RcType, RcType) {
        self.merge_function(None, actual, &mut |self_, f, actual| {
            self_.unify_span(span, &f, actual);
        })
    }

    fn merge_function(
        &mut self,
        function_arg_type: Option<ArgType>,
        actual: RcType,
        merge_fn: &mut dyn FnMut(&mut Self, &RcType, RcType),
    ) -> (ArgType, RcType, RcType) {
        let actual = self.remove_aliases(actual);
        match actual.as_function_with_type() {
            Some((found_arg_type, arg, ret))
                if function_arg_type == Some(found_arg_type) || function_arg_type == None =>
            {
                return (found_arg_type, arg.clone(), ret.clone());
            }
            _ => (),
        }
        let arg = self.subs.new_var();
        let ret = self.subs.new_var();
        let arg_type = function_arg_type.unwrap_or(ArgType::Explicit);
        let f = self
            .subs
            .function_type(arg_type, Some(arg.clone()), ret.clone());
        merge_fn(self, &f, actual);
        (arg_type, arg, ret)
    }

    fn unify_span(&mut self, span: Span<BytePos>, expected: &RcType, actual: RcType) -> RcType {
        match self.unify(expected, actual) {
            Ok(typ) => typ,
            Err(err) => {
                self.errors.push(Spanned {
                    span: span,
                    // TODO Help what caused this unification failure
                    value: err.into(),
                });
                self.subs.error()
            }
        }
    }

    fn unify(&self, expected: &RcType, actual: RcType) -> TcResult<RcType> {
        debug!("Unify start {} <=> {}", expected, actual);
        let state = unify_type::State::new(&self.environment, &self.subs);
        match unify::unify(&self.subs, state, expected, &actual) {
            Ok(typ) => Ok(typ),
            Err(errors) => {
                debug!(
                    "Error '{:?}' between:\n>> {}\n>> {}",
                    errors, expected, actual
                );
                Err(TypeError::Unification(
                    expected.clone(),
                    actual,
                    errors.into(),
                ))
            }
        }
    }

    fn remove_alias(&self, typ: RcType) -> RcType {
        resolve::remove_alias(&self.environment, &mut &self.subs, &typ)
            .unwrap_or(None)
            .unwrap_or(typ)
    }

    fn remove_aliases(&self, typ: RcType) -> RcType {
        resolve::remove_aliases(&self.environment, &mut &self.subs, typ)
    }

    fn with_forall(&mut self, from: &RcType, to: ModType) -> ModType {
        let mut params = Vec::new();
        for param in from.forall_params() {
            params.push(param.clone());
        }
        ModType::new(to.modifier, self.forall(params, to.concrete))
    }

    fn skolemize_in(
        &mut self,
        span: Span<BytePos>,
        original_type: ModTypeRef,
        f: impl FnOnce(&mut Self, ModType) -> ModType,
    ) -> ModType {
        self.environment.skolem_variables.enter_scope();
        self.environment.type_variables.enter_scope();
        let t = self.skolemize_in_no_scope(span, original_type, f);

        self.environment.type_variables.exit_scope();
        self.environment.skolem_variables.exit_scope();
        t
    }

    fn skolemize_in_no_scope(
        &mut self,
        span: Span<BytePos>,
        original_type: ModTypeRef,
        f: impl FnOnce(&mut Self, ModType) -> ModType,
    ) -> ModType {
        let skolemized = self.skolemize(&original_type);
        let new_type = f(self, ModType::new(original_type.modifier, skolemized));

        let original_type = self.subs.zonk(&original_type);
        types::FlagsVisitor(Flags::HAS_SKOLEMS, |typ: &RcType| {
            if let Type::Skolem(skolem) = &**typ {
                if !self.environment.skolem_variables.contains_key(&skolem.name) {
                    self.error(
                        span,
                        TypeError::Message(format!(
                            "Skolem variable `{}` would escape as it is not bound in `{}`",
                            skolem.name, original_type
                        )),
                    );
                }
            }
        })
        .walk(&original_type);

        self.with_forall(&original_type, new_type)
    }

    fn skolemize(&mut self, typ: &RcType) -> RcType {
        self.named_variables.clear();
        self.named_variables.extend(
            self.environment
                .skolem_variables
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );
        let new_type = typ.skolemize(&mut &self.subs, &mut self.named_variables);
        for (id, typ) in self.named_variables.iter() {
            match self.environment.skolem_variables.entry(id.clone()) {
                scoped_map::Entry::Vacant(e) => {
                    e.insert(typ.clone());
                }
                scoped_map::Entry::Occupied(mut e) => {
                    if e.get() != typ {
                        e.insert(typ.clone());
                    }
                }
            }
        }
        new_type
    }

    pub(crate) fn instantiate_generics(&mut self, typ: &RcType) -> RcType {
        self.named_variables.clear();
        typ.instantiate_generics(&mut &self.subs, &mut self.named_variables)
    }

    fn error_on_duplicated_field<'s>(
        &mut self,
        duplicated_fields: &mut FnvSet<&'s str>,
        new_name: &'s Spanned<Symbol, BytePos>,
    ) -> bool {
        let span = new_name.span;
        duplicated_fields
            .replace(new_name.value.definition_name())
            .map_or(true, |name| {
                self.errors.push(Spanned {
                    span: span,
                    // TODO Help to the other fields location
                    value: TypeError::DuplicateField(self.symbols.symbols().simple_symbol(name))
                        .into(),
                });
                false
            })
    }

    fn check_macro(&mut self, expr: &mut SpannedExpr<'ast, Symbol>) -> Option<TcResult<ModType>> {
        let (replacement, typ) = match expr.value {
            Expr::App {
                ref mut func,
                ref mut args,
                ..
            } => match func.value {
                Expr::Ident(ref id) => match id.name.declared_name() {
                    "convert_effect!" => {
                        let (name, typ) = match args.len() {
                            1 => (None, self.infer_expr(&mut args[0]).concrete),
                            2 => (
                                Some(match args[0].value {
                                    Expr::Ident(ref id) => id.name.clone(),
                                    _ => unreachable!(),
                                }),
                                self.infer_expr(&mut args[1]).concrete,
                            ),
                            _ => unreachable!(),
                        };

                        let unaliased = self.remove_aliases(typ.clone());
                        let valid_type = match &*unaliased {
                            Type::Variant(variant) => {
                                let mut iter = variant.row_iter();
                                for _ in iter.by_ref() {}
                                match **iter.current_type() {
                                    Type::EmptyRow => false,
                                    _ => true,
                                }
                            }
                            _ => false,
                        };
                        if !valid_type {
                            return Some(Err(TypeError::Message(format!("Invalid form for the type. Expect the type to be of the form `type Effect r a = | Variant X | r` but found `{}`", unaliased))));
                        }

                        let f = self.subs.new_var();
                        let row_arg = self.subs.new_var();
                        let arg = self.subs.new_var();
                        let expected_shape =
                            self.app(f.clone(), collect![row_arg.clone(), arg.clone()]);
                        self.unify_span(expr.span, &expected_shape, typ);

                        let eff = self.poly_effect(
                            name.map(|name| Field {
                                name,
                                typ: self.subs.real(&f).clone(),
                            })
                            .into_iter()
                            .collect(),
                            row_arg,
                        );
                        (
                            mem::take(args.last_mut().unwrap()),
                            self.app(eff, collect![self.subs.real(&arg).clone()]),
                        )
                    }
                    "convert_variant!" => {
                        let typ = self.infer_expr(&mut args[0]).concrete;

                        let unaliased = self.remove_aliases(typ);
                        let variant_type = match *unaliased {
                            Type::App(ref f, ref type_args) if type_args.len() == 1 => {
                                let f = self.subs.real(f).clone();
                                match *f {
                                    Type::Effect(ref row) => {
                                        let variant_type = row.row_iter().fold(
                                            self.poly_variant(vec![], self.subs.new_var()),
                                            |variant, field| {
                                                let typ = self.app(
                                                    field.typ.clone(),
                                                    collect![
                                                        self.subs.new_var(),
                                                        type_args[0].clone()
                                                    ],
                                                );
                                                let typ = self.remove_alias(typ);
                                                let typ = self.instantiate_generics(&typ);

                                                self.subsumes(
                                                    args[0].span,
                                                    ErrorOrder::ActualExpected,
                                                    &variant,
                                                    typ,
                                                )
                                            },
                                        );
                                        let variant_type = self.subs.zonk(&variant_type);

                                        let effect_row_rest = {
                                            let mut iter = row.row_iter();
                                            for _ in &mut iter {}
                                            iter.current_type().clone()
                                        };

                                        let variant_row_rest = {
                                            let mut iter = variant_type.row_iter();
                                            for _ in &mut iter {}
                                            iter.current_type().clone()
                                        };

                                        self.subsumes(
                                            args[0].span,
                                            ErrorOrder::ActualExpected,
                                            &variant_row_rest,
                                            effect_row_rest,
                                        );

                                        variant_type
                                    }
                                    _ => {
                                        return Some(Err(TypeError::Message(format!(
                                            "Expected an effect type, found `{}`",
                                            unaliased
                                        ))));
                                    }
                                }
                            }
                            _ => {
                                return Some(Err(TypeError::Message(format!(
                                    "Expected an effect type, found `{}`",
                                    unaliased
                                ))));
                            }
                        };
                        (mem::take(args.last_mut().unwrap()), variant_type)
                    }

                    _ => return None,
                },

                _ => return None,
            },

            _ => return None,
        };

        *expr = Expr::annotated(self.ast_arena, replacement, self.subs.bind_arc(&typ));

        Some(Ok(ModType::wobbly(typ)))
    }
}

pub fn translate_projected_type(
    env: &dyn TypeEnv<Type = RcType>,
    symbols: &mut dyn IdentEnv<Ident = Symbol>,
    interner: &mut impl TypeContext<Symbol, RcType>,
    ids: &[Symbol],
) -> TcResult<RcType> {
    let mut lookup_type: Option<RcType> = None;
    for symbol in &ids[..ids.len() - 1] {
        lookup_type = match lookup_type {
            Some(typ) => {
                let aliased_type = resolve::remove_aliases(env, interner, typ.clone());
                Some(
                    aliased_type
                        .type_field_iter()
                        .filter_map(|field| {
                            if field.name.name_eq(&symbol) {
                                Some(field.typ.clone().into_type())
                            } else {
                                None
                            }
                        })
                        .chain(aliased_type.row_iter().filter_map(|field| {
                            if field.name.name_eq(&symbol) {
                                Some(field.typ.clone())
                            } else {
                                None
                            }
                        }))
                        .next()
                        .ok_or_else(|| TypeError::UndefinedField(typ, symbol.clone()))?,
                )
            }
            None => Some(
                env.find_type(&symbol)
                    .or_else(|| {
                        env.find_type_info(&symbol)
                            .map(|alias| alias.typ(interner).into_owned())
                    })
                    .ok_or_else(|| TypeError::UndefinedVariable(symbol.clone()))?,
            ),
        };
    }
    let typ = lookup_type.unwrap();
    let type_symbol = symbols.from_str(ids.last().expect("Non-empty ids").name().name().as_str());
    resolve::remove_aliases(env, interner, typ.clone())
        .type_field_iter()
        .find(|field| field.name.name_eq(&type_symbol))
        .map(|field| field.typ.clone().into_type())
        .ok_or_else(|| TypeError::UndefinedField(typ, type_symbol))
}

fn with_pattern_types<'a: 'b, 'b, 'ast>(
    fields: &'a mut [PatternField<'ast, Symbol>],
    typ: &'b RcType,
) -> impl Iterator<
    Item = (
        &'a Spanned<Symbol, BytePos>,
        &'a mut Option<SpannedPattern<'ast, Symbol>>,
        Option<&'b RcType>,
    ),
>
where
    'ast: 'a,
{
    ast::pattern_values_mut(fields).map(move |(name, value)| {
        let opt = typ
            .row_iter()
            .find(|type_field| type_field.name.name_eq(&name.value));
        (
            &*name,
            value,
            opt.map(move |associated_type| &associated_type.typ),
        )
    })
}

pub fn extract_generics(args: &[RcType]) -> Vec<Generic<Symbol>> {
    args.iter()
        .map(|arg| match **arg {
            Type::Generic(ref gen) => gen.clone(),
            _ => ice!("The type on the lhs of a type binding did not have all generic arguments"),
        })
        .collect()
}

fn get_alias_app<'a>(
    env: &'a dyn TypeEnv<Type = RcType>,
    typ: &'a RcType,
) -> Option<(AliasRef<Symbol, RcType>, Cow<'a, [RcType]>)> {
    match **typ {
        Type::Alias(ref alias) => Some((alias.clone(), Cow::Borrowed(&[][..]))),
        Type::App(ref alias, ref args) => match **alias {
            Type::Alias(ref alias) => Some((alias.clone(), Cow::Borrowed(&args[..]))),
            _ => None,
        },
        _ => typ.alias_ident().and_then(|id| {
            env.find_type_info(id)
                .map(|alias| ((*alias).clone(), typ.unapplied_args()))
        }),
    }
}
struct FunctionArgIter<'a, 'b: 'a, 'ast> {
    tc: &'a mut Typecheck<'b, 'ast>,
    typ: RcType,
}

impl<'a, 'b> Iterator for FunctionArgIter<'a, 'b, '_> {
    type Item = (ArgType, RcType);
    fn next(&mut self) -> Option<Self::Item> {
        let mut last_alias = None;
        loop {
            self.typ = self.tc.skolemize(&self.typ);
            let (arg, new) = match self.typ.as_function_with_type() {
                Some((arg_type, arg, ret)) => (Some((arg_type, arg.clone())), ret.clone()),
                None => match get_alias_app(&self.tc.environment, &self.typ) {
                    Some((alias, args)) => {
                        if Some(&alias.name) == last_alias.as_ref() {
                            return None;
                        }
                        last_alias = Some(alias.name.clone());
                        self.tc.named_variables.clear();
                        match alias.typ(&mut &self.tc.subs).apply_args(
                            alias.params(),
                            &args,
                            &mut &self.tc.subs,
                            &mut self.tc.named_variables,
                        ) {
                            Some(typ) => (None, typ.clone()),
                            None => return None,
                        }
                    }
                    None => return None,
                },
            };
            self.typ = new;
            if let Some(arg) = arg {
                return Some(arg);
            }
        }
    }
}

fn function_arg_iter<'a, 'b, 'ast>(
    tc: &'a mut Typecheck<'b, 'ast>,
    typ: RcType,
) -> FunctionArgIter<'a, 'b, 'ast> {
    FunctionArgIter { tc, typ }
}

/// Returns a span of the innermost expression of a group of nested `let` and `type` bindings.
/// This span is useful for more precisely marking the span of a type error.
///
/// ```ignore
/// let x: Int =
///     let y = 1.0
///     ~~~~~~~~~~~
///     y
///     ~
///     ^
/// x
/// ```
fn expr_check_span(e: &SpannedExpr<Symbol>) -> Span<BytePos> {
    match e.value {
        Expr::LetBindings(_, ref b) | Expr::TypeBindings(_, ref b) => expr_check_span(b),
        _ => e.span,
    }
}

fn generalize_binding<'ast>(
    generalizer: &mut TypeGeneralizer<'_, '_, 'ast>,
    resolved_type: &mut RcType,
    binding: &mut ValueBinding<'ast, Symbol>,
) {
    crate::implicits::resolve(generalizer.tc, &mut binding.expr);

    generalizer.generalize_type_top(resolved_type);
}

fn ctor_return_type<'a, Id, T>(typ: &'a T) -> &'a T
where
    T: TypePtr<Id = Id>,
    Id: 'a,
{
    match &**typ {
        Type::Forall(_, typ) | Type::Function(_, _, typ) => ctor_return_type(typ),
        _ => typ,
    }
}

enum CowVec<'a, T> {
    Borrowed(&'a mut [T]),
    Owned(Vec<T>),
}

impl<T> std::ops::Deref for CowVec<'_, T> {
    type Target = [T];
    fn deref(&self) -> &Self::Target {
        match self {
            CowVec::Owned(v) => v,
            CowVec::Borrowed(v) => v,
        }
    }
}

impl<T> std::ops::DerefMut for CowVec<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            CowVec::Owned(v) => v,
            CowVec::Borrowed(v) => v,
        }
    }
}

impl<T> CowVec<'_, T>
where
    T: Default,
{
    fn as_owned(&mut self) -> &mut Vec<T> {
        let v = match self {
            CowVec::Owned(v) => return v,
            CowVec::Borrowed(b) => b.iter_mut().map(mem::take).collect(),
        };
        *self = CowVec::Owned(v);
        self.as_owned()
    }
}
