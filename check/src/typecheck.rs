//! The main typechecking interface which is responsible for typechecking expressions, patterns,
//! etc. Only checks which need to be aware of expressions are handled here the actual unifying and
//! checking of types are done in the `unify_type` and `kindcheck` modules.
use std::{
    borrow::{BorrowMut, Cow},
    cell::RefCell,
    fmt,
    iter::once,
    mem,
    rc::Rc,
};

use codespan_reporting::Diagnostic;

use pretty::Arena;

use crate::base::{
    ast::{
        self, Argument, AstType, DisplayEnv, Do, Expr, IdentEnv, Literal, MutVisitor, Pattern,
        PatternField, SpannedExpr, SpannedIdent, SpannedPattern, TypeBinding, Typed, TypedIdent,
        ValueBinding, ValueBindings,
    },
    error::{AsDiagnostic, Errors},
    fnv::{FnvMap, FnvSet},
    kind::{ArcKind, Kind, KindCache, KindEnv},
    merge,
    metadata::{Metadata, MetadataEnv},
    pos::{self, BytePos, Span, Spanned},
    resolve,
    scoped_map::{self, ScopedMap},
    symbol::{Symbol, SymbolModule, SymbolRef, Symbols},
    types::{
        self, Alias, AliasRef, AppVec, ArcType, ArgType, Field, Filter, Generic, NullInterner,
        PrimitiveEnv, SharedInterner, ToDoc, Type, TypeCache, TypeEnv, TypeExt, TypeFormatter,
        TypeInterner, TypeVariable,
    },
};

use crate::{
    implicits,
    kindcheck::{self, Error as KindCheckError, KindCheck, KindError},
    substitution::{self, Substitution},
    typ::{translate_interned_type, translate_rc_interned_type, PtrEq, RcType},
    unify::{self, Error as UnifyError},
    unify_type::{self, Error as UnifyTypeError},
    ArcTypeCacher, TypecheckEnv,
};

use self::generalize::TypeGeneralizer;

mod generalize;

/// Type representing a single error when checking a type
#[derive(Debug, PartialEq, Functor)]
pub enum TypeError<I, T> {
    /// Variable has not been defined before it was used
    UndefinedVariable(I),
    /// Attempt to call a type which is not a function
    NotAFunction(T),
    /// Type has not been defined before it was used
    UndefinedType(I),
    /// Type were expected to have a certain field
    UndefinedField(T, I),
    /// Constructor type was found in a pattern but did not have the expected number of arguments
    PatternError(T, usize),
    /// Errors found when trying to unify two types
    Unification(T, T, Vec<UnifyTypeError<I, T>>),
    /// Error were found when trying to unify the kinds of two types
    KindError(KindCheckError<I, T>),
    /// Error were found when checking value recursion
    RecursionCheck(crate::recursion_check::Error),
    /// Multiple types were declared with the same name in the same expression
    DuplicateTypeDefinition(I),
    /// A field was defined more than once in a record constructor or pattern match
    DuplicateField(String),
    /// Type is not a type which has any fields
    InvalidProjection(T),
    /// Expected to find a record with the following fields
    UndefinedRecord {
        fields: Vec<I>,
    },
    /// Found a case expression without any alternatives
    EmptyCase,
    Message(String),
    UnableToResolveImplicit(implicits::Error<T>),
}

enum ErrorOrder {
    ExpectedActual,
    ActualExpected,
}

impl<I, T> From<KindCheckError<I, T>> for TypeError<I, T> {
    fn from(e: KindCheckError<I, T>) -> Self {
        match e {
            UnifyError::Other(KindError::UndefinedType(name)) => TypeError::UndefinedType(name),
            UnifyError::Other(KindError::UndefinedField(typ, name)) => {
                TypeError::UndefinedField(typ, name)
            }
            e => TypeError::KindError(e),
        }
    }
}

impl<I, T> From<implicits::Error<T>> for TypeError<I, T> {
    fn from(e: implicits::Error<T>) -> Self {
        TypeError::UnableToResolveImplicit(e)
    }
}

impl<I, T> From<crate::recursion_check::Error> for TypeError<I, T> {
    fn from(e: crate::recursion_check::Error) -> Self {
        TypeError::RecursionCheck(e)
    }
}

impl<I, T> fmt::Display for TypeError<I, T>
where
    I: fmt::Display + AsRef<str> + Clone,
    T: TypeExt<I>
        + fmt::Display
        + ast::Commented
        + pos::HasSpan
        + for<'a> ToDoc<'a, Arena<'a, ()>, (), ()>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::TypeError::*;
        use pretty::{Arena, DocAllocator};
        match *self {
            UndefinedVariable(ref name) => write!(f, "Undefined variable `{}`", name),
            NotAFunction(ref typ) => write!(f, "`{}` is not a function", typ),
            UndefinedType(ref name) => write!(f, "Type `{}` is not defined", name),
            UndefinedField(ref typ, ref field) => {
                let fields = [field.clone()];
                let filter = unify_type::similarity_filter(typ, &fields);
                let arena = Arena::<()>::new();
                write!(
                    f,
                    "Type `{}` does not have the field `{}`",
                    TypeFormatter::new(typ)
                        .filter(&*filter)
                        .pretty(&arena)
                        .1
                        .pretty(80),
                    field
                )?;
                Ok(())
            }
            Unification(ref expected, ref actual, ref errors) => {
                let filters = errors
                    .iter()
                    .filter_map(|err| match *err {
                        UnifyError::Other(ref err) => Some(err.make_filter()),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                let filter = move |field: &I| {
                    if filters.is_empty() {
                        Filter::Retain
                    } else {
                        filters
                            .iter()
                            .fold(Filter::Drop, move |filter, f| match filter {
                                Filter::Retain => filter,
                                _ => match f(field) {
                                    Filter::Drop => filter,
                                    Filter::RetainKey => Filter::RetainKey,
                                    Filter::Retain => Filter::Retain,
                                },
                            })
                    }
                };

                let arena = Arena::<()>::new();
                let types = chain![&arena;
                    "Expected:",
                    chain![&arena;
                        arena.space(),
                        TypeFormatter::new(expected).filter(&filter).pretty(&arena)
                    ].nest(4).group(),
                    arena.newline(),
                    "Found:",
                    chain![&arena;
                        arena.space(),
                        TypeFormatter::new(actual).filter(&filter).pretty(&arena)
                    ].nest(4).group()
                ]
                .group();
                let doc = chain![&arena;
                    "Expected the following types to be equal",
                    arena.newline(),
                    types,
                    arena.newline(),
                    arena.as_string(errors.len()),
                    " errors were found during unification:"
                ];
                writeln!(f, "{}", doc.1.pretty(80))?;
                if errors.is_empty() {
                    return Ok(());
                }
                for error in &errors[..errors.len() - 1] {
                    match *error {
                        UnifyError::Other(ref err) => {
                            err.filter_fmt(&filter, f)?;
                            writeln!(f)?;
                        }
                        _ => writeln!(f, "{}", error)?,
                    }
                }
                write!(f, "{}", errors.last().unwrap())
            }
            PatternError(ref typ, expected_len) => {
                write!(f, "Type {} has {} to few arguments", typ, expected_len)
            }
            KindError(ref err) => kindcheck::fmt_kind_error(err, f),
            RecursionCheck(ref err) => write!(f, "{}", err),
            DuplicateTypeDefinition(ref id) => write!(
                f,
                "Type '{}' has been already been defined in this module",
                id
            ),
            DuplicateField(ref id) => {
                write!(f, "The record has more than one field named '{}'", id)
            }
            InvalidProjection(ref typ) => write!(
                f,
                "Type '{}' is not a type which allows field accesses",
                typ
            ),
            UndefinedRecord { ref fields } => {
                write!(f, "No type found with the following fields: ")?;
                write!(f, "{}", fields[0])?;
                for field in &fields[1..] {
                    write!(f, ", {}", field)?;
                }
                Ok(())
            }
            EmptyCase => write!(f, "`case` expression with no alternatives"),
            Message(ref msg) => write!(f, "{}", msg),
            UnableToResolveImplicit(ref err) => write!(f, "{}", err),
        }
    }
}

impl<I, T> AsDiagnostic for TypeError<I, T>
where
    I: fmt::Display + AsRef<str> + Clone,
    T: TypeExt<I>
        + fmt::Display
        + ast::Commented
        + pos::HasSpan
        + for<'a> ToDoc<'a, Arena<'a, ()>, (), ()>,
{
    fn as_diagnostic(&self) -> Diagnostic {
        use self::TypeError::*;
        match *self {
            UnableToResolveImplicit(ref err) => err.as_diagnostic(),
            _ => Diagnostic::new_error(self.to_string()),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Help {
    UndefinedFlatMapInDo,
    ExtraArgument(u32, u32),
}

impl fmt::Display for Help {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Help::UndefinedFlatMapInDo => write!(
                f,
                "Try bringing the `flat_map` function found in the `Monad`\
                 instance for your type into scope"
            ),
            Help::ExtraArgument(expected, actual) => {
                if expected == 0 {
                    write!(f, "Attempted to call a non-function value")
                } else {
                    write!(
                        f,
                        "Attempted to call function with {} argument{} but its type only has {}",
                        actual,
                        if actual == 1 { "" } else { "s" },
                        expected,
                    )
                }
            }
        }
    }
}

pub type HelpError<Id, T = ArcType<Id>> = crate::base::error::Help<TypeError<Id, T>, Help>;
pub type SpannedTypeError<Id, T = ArcType<Id>> = Spanned<HelpError<Id, T>, BytePos>;

pub(crate) type TcResult<T> = Result<T, TypeError<Symbol, RcType<Symbol>>>;

#[derive(Clone, Debug)]
struct StackBinding {
    typ: RcType,
}

pub(crate) struct Environment<'a> {
    /// The global environment which the typechecker extracts types from
    environment: ArcTypeCacher<'a>,
    /// Stack allocated variables
    stack: ScopedMap<Symbol, StackBinding>,
    /// Types which exist in some scope (`type Test = ... in ...`)
    stack_types: ScopedMap<Symbol, (RcType, Alias<Symbol, RcType>)>,
}

impl<'a> KindEnv for Environment<'a> {
    fn find_kind(&self, type_name: &SymbolRef) -> Option<ArcKind> {
        self.stack_types
            .get(type_name)
            .map(|&(_, ref alias)| alias.kind().into_owned())
            .or_else(|| self.environment.find_kind(type_name))
    }
}

impl<'a> TypeEnv for Environment<'a> {
    type Type = RcType;

    fn find_type(&self, id: &SymbolRef) -> Option<&RcType> {
        self.stack
            .get(id)
            .map(|bind| &bind.typ)
            .or_else(|| self.environment.find_type(id))
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<&Alias<Symbol, RcType>> {
        self.stack_types
            .get(id)
            .map(|&(_, ref alias)| alias)
            .or_else(|| self.environment.find_type_info(id))
    }
}

impl<'a> PrimitiveEnv for Environment<'a> {
    fn get_bool(&self) -> &ArcType {
        self.environment.get_bool()
    }
}

impl<'a> MetadataEnv for Environment<'a> {
    fn get_metadata(&self, id: &SymbolRef) -> Option<&Metadata> {
        self.environment.get_metadata(id)
    }
}

/// Type returned from the main typecheck function to make sure that nested `type` and `let`
/// expressions dont overflow the stack
enum TailCall {
    Type(RcType),
    TypeImplicit(RcType, Vec<SpannedExpr<Symbol>>),
    /// Returned from typechecking a `let` or `type` expresion to indicate that the expression body
    /// should be typechecked now.
    TailCall,
}

/// Struct which provides methods to typecheck expressions.
pub struct Typecheck<'a> {
    pub(crate) environment: Environment<'a>,
    symbols: SymbolModule<'a>,
    pub(crate) subs: Substitution<RcType>,
    named_variables: FnvMap<Symbol, RcType>,
    pub(crate) errors: Errors<SpannedTypeError<Symbol, RcType<Symbol>>>,
    /// Type variables `let test: a -> b` (`a` and `b`)
    type_variables: ScopedMap<Symbol, RcType>,
    pub(crate) type_cache: TypeCache<Symbol, RcType>,
    type_interner: Rc<RefCell<FnvMap<PtrEq<ArcType>, RcType>>>,
    arc_type_cache: TypeCache<Symbol, ArcType>,
    arc_type_interner: FnvMap<RcType, ArcType>,

    kind_cache: KindCache,

    pub(crate) implicit_resolver: crate::implicits::ImplicitResolver<'a>,
    unbound_variables: ScopedMap<Symbol, RcType>,
}

impl<'a> TypeInterner<Symbol, RcType> for Typecheck<'a> {
    fn intern(&mut self, typ: Type<Symbol, RcType>) -> RcType {
        (&self.subs).intern(typ)
    }
}

/// Error returned when unsuccessfully typechecking an expression
pub type Error = Errors<SpannedTypeError<Symbol>>;

pub use crate::implicits::{Error as ImplicitError, ErrorKind as ImplicitErrorKind};

impl<'a> Typecheck<'a> {
    /// Create a new typechecker which typechecks expressions in `module`
    pub fn new(
        module: String,
        symbols: &'a mut Symbols,
        environment: &'a (TypecheckEnv<Type = ArcType> + 'a),
        arc_type_cache: TypeCache<Symbol, ArcType>,
        metadata: &'a mut FnvMap<Symbol, Metadata>,
    ) -> Typecheck<'a> {
        let symbols = SymbolModule::new(module, symbols);
        let kind_cache = KindCache::new();
        let interner = SharedInterner::default();
        let subs = Substitution::new(kind_cache.typ(), interner.clone());
        let type_interner = Rc::new(RefCell::new(FnvMap::default()));
        Typecheck {
            environment: Environment {
                environment: ArcTypeCacher::new(
                    environment,
                    type_interner.clone(),
                    interner.clone(),
                ),
                stack: ScopedMap::new(),
                stack_types: ScopedMap::new(),
            },
            symbols: symbols,
            named_variables: FnvMap::default(),
            errors: Errors::new(),
            type_variables: ScopedMap::new(),
            type_cache: Default::default(),
            arc_type_cache,
            arc_type_interner: Default::default(),
            kind_cache: kind_cache,
            implicit_resolver: crate::implicits::ImplicitResolver::new(
                environment,
                type_interner.clone(),
                interner.clone(),
                metadata,
            ),
            unbound_variables: ScopedMap::new(),
            type_interner,
            subs,
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
        self.type_cache.error()
    }

    // FIXME Cache
    fn bool(&mut self) -> RcType {
        let typ = self.environment.get_bool().clone();
        self.translate_arc_type(&typ)
    }

    fn find_at(&mut self, span: Span<BytePos>, id: &Symbol) -> RcType {
        match self.find(id) {
            Ok(typ) => typ,
            Err(err) => self.error(span, err),
        }
    }

    fn find(&mut self, id: &Symbol) -> TcResult<RcType> {
        match self.environment.find_type(id).map(RcType::clone) {
            Some(typ) => {
                self.named_variables.clear();
                debug!("Find {} : {}", self.symbols.string(id), typ);
                Ok(typ)
            }
            None => {
                // Don't report global variables inserted by the `import!` macro as undefined
                // (if they don't exist the error will already have been reported by the macro)
                if id.is_global() {
                    Ok(self.subs.new_var())
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
                self.subs
                    .new_alias(id.clone(), Vec::new(), self.type_cache.hole())
            }
        }
    }

    fn find_type_info(&self, id: &Symbol) -> TcResult<&Alias<Symbol, RcType>> {
        self.environment
            .find_type_info(id)
            .ok_or_else(|| TypeError::UndefinedType(id.clone()))
    }

    fn stack_var(&mut self, id: Symbol, typ: RcType) {
        debug!("Insert {} : {}", id, typ);

        self.implicit_resolver.on_stack_var(&id, &typ);

        // HACK
        // Insert the non_renamed symbol so that type projections in types can be translated (see
        // translate_projected_type)
        let non_renamed_symbol = self.symbols.symbol(id.declared_name());
        self.environment
            .stack
            .insert(non_renamed_symbol, StackBinding { typ: typ.clone() });

        self.environment.stack.insert(id, StackBinding { typ });
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
            self.unpack_canonical_alias(alias, &canonical_alias_type);

        if let Type::Variant(ref variants) = **inner_type {
            for field in variants.row_iter().cloned() {
                let params = canonical_alias
                    .params()
                    .iter()
                    .map(|g| self.generic(g.clone()))
                    .collect();
                let a = self.intern(Type::Alias(canonical_alias.clone()));
                let variant_type = self.app(a, params);

                let ctor_type = self.subs.function(
                    field
                        .typ
                        .row_iter()
                        .map(|f| f.typ.clone())
                        .collect::<AppVec<_>>(),
                    variant_type,
                );

                let typ = self.forall(
                    canonical_alias
                        .params()
                        .iter()
                        .chain(outer_params.iter())
                        .cloned()
                        .collect(),
                    ctor_type,
                );

                self.stack_var(field.name, typ);
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

    fn unpack_canonical_alias<'b>(
        &mut self,
        alias: &'b Alias<Symbol, RcType>,
        canonical_alias_type: &'b RcType,
    ) -> (
        Cow<'b, [Generic<Symbol>]>,
        &'b AliasRef<Symbol, RcType>,
        Cow<'b, RcType>,
    ) {
        match **canonical_alias_type {
            Type::App(ref func, _) => match **func {
                Type::Alias(ref alias) => (Cow::Borrowed(&[]), alias, alias.typ(&mut &self.subs)),
                _ => (Cow::Borrowed(&[]), &**alias, Cow::Borrowed(func)),
            },
            Type::Alias(ref alias) => (Cow::Borrowed(&[]), alias, alias.typ(&mut &self.subs)),
            Type::Forall(ref params, ref typ) => {
                let mut params = Cow::Borrowed(&params[..]);
                let (more_params, canonical_alias, inner_type) =
                    self.unpack_canonical_alias(alias, typ);
                if !more_params.is_empty() {
                    params.to_mut().extend(more_params.iter().cloned());
                }
                (params, canonical_alias, inner_type)
            }
            _ => (
                Cow::Borrowed(&[]),
                &**alias,
                Cow::Borrowed(canonical_alias_type),
            ),
        }
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
        binding: &mut ValueBinding<Symbol>,
    ) {
        let mut generalizer = TypeGeneralizer::new(level, self, resolved_type, binding.name.span);
        generalize_binding(&mut generalizer, resolved_type, binding);
    }

    fn generalize_variables<'i>(
        &mut self,
        level: u32,
        args: &mut Iterator<Item = &'i mut SpannedIdent<Symbol>>,
        expr: &mut SpannedExpr<Symbol>,
    ) {
        let typ = self.type_cache.hole();
        TypeGeneralizer::new(level, self, &typ, expr.span).generalize_variables(args, expr)
    }

    fn generalize_type_errors(&mut self, errors: &mut Errors<SpannedTypeError<Symbol, RcType>>) {
        self.type_variables.enter_scope();

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
                | PatternError(ref mut typ, _)
                | InvalidProjection(ref mut typ) => self.generalize_type(0, typ, err.span),
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

        self.type_variables.exit_scope();
    }

    /// Typecheck `expr`. If successful the type of the expression will be returned and all
    /// identifiers in `expr` will be filled with the inferred type
    pub fn typecheck_expr(&mut self, expr: &mut SpannedExpr<Symbol>) -> Result<ArcType, Error> {
        self.typecheck_expr_expected(expr, None)
    }

    pub fn typecheck_expr_expected(
        &mut self,
        expr: &mut SpannedExpr<Symbol>,
        expected_type: Option<&ArcType>,
    ) -> Result<ArcType, Error> {
        let expected_type = expected_type.map(|t| self.translate_arc_type(t));

        self.typecheck_expr_expected_(expr, expected_type.as_ref())
            .map(|t| self.translate_rc_type(&t))
    }

    fn typecheck_expr_expected_(
        &mut self,
        expr: &mut SpannedExpr<Symbol>,
        expected_type: Option<&RcType>,
    ) -> Result<RcType, Error> {
        fn tail_expr(e: &mut SpannedExpr<Symbol>) -> &mut SpannedExpr<Symbol> {
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

        let mut typ = self.typecheck_opt(expr, expected_type);
        {
            if let Some(expected_type) = expected_type {
                let type_cache = &self.type_cache;
                self.type_variables.extend(
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
            struct ReplaceVisitor<'a: 'b, 'b> {
                tc: &'b mut Typecheck<'a>,
            }

            impl<'a, 'b, 'd> MutVisitor<'d> for ReplaceVisitor<'a, 'b> {
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
            Ok(typ)
        }
    }

    fn infer_expr(&mut self, expr: &mut SpannedExpr<Symbol>) -> RcType {
        self.typecheck_opt(expr, None)
    }

    fn typecheck(&mut self, expr: &mut SpannedExpr<Symbol>, expected_type: &RcType) -> RcType {
        self.typecheck_opt(expr, Some(expected_type))
    }

    /// Main typechecking function. Returns the type of the expression if typechecking was
    /// successful
    fn typecheck_opt(
        &mut self,
        mut expr: &mut SpannedExpr<Symbol>,
        mut expected_type: Option<&RcType>,
    ) -> RcType {
        fn moving<T>(t: T) -> T {
            t
        }
        // How many scopes that have been entered in this "tailcall" loop
        let mut scope_count = 0;
        let returned_type;
        loop {
            match self.typecheck_(expr, &mut expected_type) {
                Ok(tailcall) => {
                    match tailcall {
                        TailCall::TailCall => {
                            // Call typecheck_ again with the next expression
                            expr = match moving(expr).value {
                                Expr::LetBindings(_, ref mut new_expr)
                                | Expr::TypeBindings(_, ref mut new_expr)
                                | Expr::Do(Do {
                                    body: ref mut new_expr,
                                    ..
                                }) => new_expr,
                                _ => ice!("Only Let and Type expressions can tailcall"),
                            };
                            scope_count += 1;
                        }
                        TailCall::TypeImplicit(typ, args) => {
                            if !args.is_empty() {
                                match expr.value {
                                    Expr::App {
                                        ref mut implicit_args,
                                        ..
                                    } => {
                                        if implicit_args.is_empty() {
                                            *implicit_args = args;
                                        } else {
                                            implicit_args.extend(args);
                                        }
                                    }
                                    _ => {
                                        let dummy = Expr::Literal(Literal::Int(0));
                                        let func = mem::replace(&mut expr.value, dummy);
                                        expr.value = Expr::App {
                                            func: Box::new(pos::spanned(expr.span, func)),
                                            implicit_args: args,
                                            args: vec![],
                                        }
                                    }
                                }
                            }

                            returned_type = match expected_type {
                                Some(expected_type) => {
                                    self.subsumes_expr(expr.span, &typ, expected_type.clone(), expr)
                                }
                                None => typ,
                            };
                            break;
                        }
                        TailCall::Type(typ) => {
                            returned_type = match expected_type {
                                Some(expected_type) => {
                                    self.subsumes_expr(expr.span, &typ, expected_type.clone(), expr)
                                }
                                None => typ,
                            };
                            break;
                        }
                    }
                }
                Err(err) => {
                    returned_type = self.type_cache.error();
                    self.errors.push(Spanned {
                        span: expr_check_span(expr),
                        value: err.into(),
                    });
                    break;
                }
            }
        }
        for _ in 0..scope_count {
            self.exit_scope();
        }
        returned_type
    }

    /// `expected_type` should be set to `None` if subsumption is done with it (to prevent us from
    /// doing it twice)
    fn typecheck_(
        &mut self,
        expr: &mut SpannedExpr<Symbol>,
        expected_type: &mut Option<&RcType<Symbol>>,
    ) -> TcResult<TailCall> {
        if let Some(result) = self.check_macro(expr) {
            return result;
        }
        match expr.value {
            Expr::Ident(ref mut id) => {
                let typ = self.find(&id.name)?;
                let (args, typ) = self.instantiate_sigma(expr.span, &typ, expected_type);
                id.typ = self.subs.bind_arc(&typ);
                Ok(TailCall::TypeImplicit(typ, args))
            }
            Expr::Literal(ref lit) => Ok(TailCall::Type(match *lit {
                Literal::Int(_) => self.type_cache.int(),
                Literal::Byte(_) => self.type_cache.byte(),
                Literal::Float(_) => self.type_cache.float(),
                Literal::String(_) => self.type_cache.string(),
                Literal::Char(_) => self.type_cache.char(),
            })),
            Expr::App {
                ref mut func,
                ref mut implicit_args,
                ref mut args,
            } => {
                let func_type = self.infer_expr(func);
                self.typecheck_application(expr.span, func_type, implicit_args, args)
            }
            Expr::IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
                let bool_type = self.bool();
                let pred_type = self.typecheck(&mut **pred, &bool_type);
                self.unify_span(expr_check_span(pred), &bool_type, pred_type);

                // Both branches must unify to the same type
                let true_type = self.typecheck_opt(&mut **if_true, expected_type.clone());
                let false_type = self.typecheck_opt(&mut **if_false, expected_type.take());

                let true_type = self.instantiate_generics(&true_type);
                let false_type = self.instantiate_generics(&false_type);

                self.unify(&true_type, false_type).map(TailCall::Type)
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
                    self.subs.function(
                        vec![prim_type.clone(), prim_type.clone()],
                        return_type.clone(),
                    )
                } else {
                    match &*op_name {
                        "&&" | "||" => {
                            let b = self.bool();
                            self.subs.function(vec![b.clone(), b.clone()], b)
                        }
                        _ => self.find_at(op.span, &op.value.name),
                    }
                };

                let func_type = self.instantiate_generics(&func_type);

                op.value.typ = self.subs.bind_arc(&func_type);

                self.typecheck_application(
                    op.span,
                    func_type,
                    implicit_args,
                    [&mut **lhs, &mut **rhs].iter_mut().map(|expr| &mut **expr),
                )
            }
            Expr::Tuple {
                ref mut typ,
                elems: ref mut exprs,
            } => {
                let new_type = match exprs.len() {
                    0 => self.unit(),
                    1 => self.typecheck_opt(&mut exprs[0], expected_type.take()),
                    _ => {
                        let fields = exprs
                            .iter_mut()
                            .enumerate()
                            .map(|(i, expr)| {
                                let typ = self.infer_expr(expr);
                                Field {
                                    name: self.symbols.symbol(format!("_{}", i)),
                                    typ: typ,
                                }
                            })
                            .collect();
                        self.record(vec![], fields)
                    }
                };
                *typ = self.subs.bind_arc(&new_type);
                Ok(TailCall::Type(new_type))
            }
            Expr::Match(ref mut expr, ref mut alts) => {
                let mut scrutinee_type = self.infer_expr(&mut **expr);
                let expected_type = expected_type.take().cloned();

                let mut unaliased_scrutinee_type = match alts.first().map(|alt| &alt.pattern.value)
                {
                    Some(Pattern::Constructor(..)) => {
                        let variant_type = self.subs.poly_variant(vec![], self.subs.new_var());
                        let scrutinee_type = self.subsumes(
                            expr.span,
                            ErrorOrder::ExpectedActual,
                            &variant_type,
                            scrutinee_type.clone(),
                        );
                        let typ = self.remove_aliases(scrutinee_type);
                        self.instantiate_generics(&typ)
                    }
                    _ => scrutinee_type.clone(),
                };

                let mut expr_type = None;

                for alt in alts.iter_mut() {
                    self.enter_scope();
                    self.typecheck_pattern(&mut alt.pattern, scrutinee_type.clone());

                    let mut alt_type = self.typecheck_opt(&mut alt.expr, expected_type.as_ref());
                    alt_type = self.instantiate_generics(&alt_type);
                    match expr_type {
                        Some(ref expr_type) if expected_type.is_none() => {
                            alt_type = self.unify_span(alt.expr.span, expr_type, alt_type);
                        }
                        _ => (),
                    }
                    self.exit_scope();

                    // The variant we matched on will not appear in any followup bindings so remove
                    // this variant from the type we are matching on
                    //
                    // TODO Make this more general so it can error when not matching on all the
                    // variants
                    {
                        let replaced = match (&alt.pattern.value, &*unaliased_scrutinee_type) {
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
                                    scrutinee_type = self.poly_variant(
                                        variants,
                                        self.subs.new_var(), // TODO Double check
                                    );
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
                expr_type.ok_or(TypeError::EmptyCase).map(TailCall::Type)
            }
            Expr::LetBindings(ref mut bindings, _) => {
                self.typecheck_bindings(bindings)?;
                Ok(TailCall::TailCall)
            }
            Expr::Projection(ref mut expr, ref field_id, ref mut ast_field_typ) => {
                let mut expr_typ = self.infer_expr(&mut **expr);
                debug!(
                    "Projection {} . {:?}",
                    &expr_typ,
                    self.symbols.string(field_id)
                );
                self.subs.make_real(&mut expr_typ);
                expr_typ = self.instantiate_generics(&expr_typ);
                let record = self.remove_aliases(expr_typ.clone());
                match *record {
                    Type::Variable(_) | Type::Record(_) => {
                        let field_type = record
                            .row_iter()
                            .find(|field| field.name.name_eq(field_id))
                            .map(|field| field.typ.clone());
                        let mut implicit_args = Vec::new();
                        let new_ast_field_type = match field_type {
                            Some(typ) => {
                                let (args, typ) =
                                    self.instantiate_sigma(expr.span, &typ, expected_type);
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
                        Ok(TailCall::TypeImplicit(new_ast_field_type, implicit_args))
                    }
                    Type::Error => Ok(TailCall::Type(record.clone())),
                    _ => Err(TypeError::InvalidProjection(record)),
                }
            }
            Expr::Array(ref mut array) => {
                let mut expected_element_type = self.subs.new_var();

                let array_type = self.subs.array(expected_element_type.clone());
                array.typ = self.subs.bind_arc(&array_type);
                if let Some(expected_type) = expected_type.take() {
                    self.unify_span(expr.span, &expected_type, array_type.clone());
                }

                for expr in &mut array.exprs {
                    expected_element_type = self.typecheck(expr, &expected_element_type);
                }

                Ok(TailCall::Type(array_type))
            }
            Expr::Lambda(ref mut lambda) => {
                let loc = format!("{}.lambda:{}", self.symbols.module(), expr.span.start());
                lambda.id.name = self.symbols.symbol(loc);
                let level = self.subs.var_id();
                let function_type = expected_type
                    .take()
                    .cloned()
                    .unwrap_or_else(|| self.subs.new_var());

                let start = expr.span.start();
                let mut typ =
                    self.skolemize_in(expr.span, &function_type, |self_, function_type| {
                        self_.typecheck_lambda(
                            function_type,
                            start,
                            &mut lambda.args,
                            &mut lambda.body,
                        )
                    });

                self.generalize_type(level, &mut typ, expr.span);
                lambda.id.typ = self.subs.bind_arc(&typ);
                Ok(TailCall::Type(typ.clone()))
            }
            Expr::TypeBindings(ref mut bindings, ref expr) => {
                self.typecheck_type_bindings(bindings, expr);
                Ok(TailCall::TailCall)
            }
            Expr::Record {
                ref mut typ,
                ref mut types,
                exprs: ref mut fields,
                ref mut base,
            } => {
                let level = self.subs.var_id();

                let expected_record_type = expected_type.and_then(|expected_type| {
                    let expected_type = self.subs.real(expected_type).clone();
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
                let mut base_fields: Vec<Field<_, _>> = Vec::new();
                if let Some(ref mut base) = *base {
                    let base_type = self.infer_expr(base);
                    let base_type = self.remove_aliases(base_type);

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
                for field in types {
                    if let Some(ref mut typ) = field.value {
                        let rc_type = self.translate_arc_type(typ);
                        if let Some(new_type) = self.create_unifiable_signature(&rc_type) {
                            *typ = self.translate_rc_type(&new_type);
                        }
                    }

                    let alias = self.find_type_info_at(field.name.span, &field.name.value);
                    if self.error_on_duplicated_field(&mut duplicated_fields, field.name.clone()) {
                        match base_record_types.get(field.name.value.declared_name()) {
                            Some(&i) => base_types[i].typ = alias,
                            None => new_types.push(Field::new(field.name.value.clone(), alias)),
                        }
                    }
                }

                let mut new_fields: Vec<Field<_, _>> = Vec::with_capacity(fields.len());
                for field in fields {
                    let name = &field.name.value;
                    let expected_field_type = expected_type
                        .and_then(|expected_type| {
                            expected_type
                                .row_iter()
                                .find(|expected_field| expected_field.name.name_eq(&name))
                        })
                        .map(|field| &field.typ);

                    let mut typ = match field.value {
                        Some(ref mut expr) => self.typecheck_opt(expr, expected_field_type),
                        None => {
                            let typ = self.find_at(field.name.span, &field.name.value);
                            match expected_field_type {
                                Some(expected_field_type) => {
                                    let mut implicit_args = Vec::new();
                                    let typ = self.subsumes_implicit(
                                        field.name.span,
                                        ErrorOrder::ExpectedActual,
                                        &expected_field_type,
                                        typ,
                                        &mut |implicit_arg| {
                                            implicit_args
                                                .push(pos::spanned(field.name.span, implicit_arg));
                                        },
                                    );

                                    if !implicit_args.is_empty() {
                                        field.value = Some(pos::spanned(
                                            field.name.span,
                                            Expr::App {
                                                func: Box::new(pos::spanned(
                                                    field.name.span,
                                                    Expr::Ident(TypedIdent {
                                                        name: field.name.value.clone(),
                                                        typ: self.subs.bind_arc(&typ),
                                                    }),
                                                )),
                                                implicit_args,
                                                args: Vec::new(),
                                            },
                                        ));
                                    }

                                    typ
                                }
                                None => typ,
                            }
                        }
                    };
                    self.generalize_type(level, &mut typ, field.name.span);

                    if self.error_on_duplicated_field(&mut duplicated_fields, field.name.clone()) {
                        match base_record_fields.get(field.name.value.declared_name()) {
                            Some(&i) => base_fields[i].typ = typ,
                            None => new_fields.push(Field::new(field.name.value.clone(), typ)),
                        }
                    }
                }

                new_types.extend(base_types);
                new_fields.extend(base_fields);
                let new_type = self.subs.record(new_types, new_fields);
                *typ = self.subs.bind_arc(&new_type);

                Ok(TailCall::Type(new_type))
            }
            Expr::Block(ref mut exprs) => {
                let (last, exprs) = exprs.split_last_mut().expect("Expr in block");
                for expr in exprs {
                    self.infer_expr(expr);
                }
                Ok(TailCall::Type(
                    self.typecheck_opt(last, expected_type.take()),
                ))
            }
            Expr::Do(Do {
                ref mut id,
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
                            self.type_cache.error()
                        }
                    },
                    _ => ice!("flat_map_id not inserted during renaming"),
                };

                let flat_map_type = self.instantiate_generics(&flat_map_type);

                let flat_map_type = match *flat_map_type {
                    Type::Function(ArgType::Implicit, ref arg_type, ref r) => {
                        let name = self.implicit_resolver.make_implicit_ident(arg_type);
                        *flat_map_id = Some(Box::new(pos::spanned(
                            do_span,
                            Expr::App {
                                func: flat_map_id.take().unwrap(),
                                args: vec![pos::spanned(
                                    do_span,
                                    Expr::Ident(TypedIdent {
                                        name,
                                        typ: self.subs.bind_arc(&arg_type),
                                    }),
                                )],
                                implicit_args: Vec::new(),
                            },
                        )));
                        r.clone()
                    }
                    _ => flat_map_type.clone(),
                };

                let id_var = self.subs.new_var();
                let arg1 = self
                    .subs
                    .function(Some(id_var.clone()), self.subs.new_var());
                let arg2 = self.subs.new_var();

                let ret = expected_type
                    .cloned()
                    .unwrap_or_else(|| self.subs.new_var());
                let func_type = self
                    .subs
                    .function(vec![arg1.clone(), arg2.clone()], ret.clone());

                self.unify_span(do_span, &flat_map_type, func_type);

                self.typecheck(bound, &arg2);

                if let Some(ref mut id) = *id {
                    self.typecheck_pattern(id, id_var);
                }

                let body_type = self.typecheck(body, &ret);

                let ret = self.unify_span(body.span, &ret, body_type);

                Ok(TailCall::Type(ret))
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
                self.typecheck_(expr, &mut Some(&typ))
            }

            Expr::Error(ref typ) => Ok(TailCall::Type(
                typ.as_ref()
                    .map(|typ| self.translate_arc_type(typ))
                    .unwrap_or_else(|| self.subs.new_var()),
            )),
        }
    }

    fn typecheck_application<'e, I>(
        &mut self,
        span: Span<BytePos>,
        func_type: RcType,
        implicit_args: &mut Vec<SpannedExpr<Symbol>>,
        args: I,
    ) -> TcResult<TailCall>
    where
        I: IntoIterator<Item = &'e mut SpannedExpr<Symbol>>,
        I::IntoIter: ExactSizeIterator,
    {
        self.typecheck_application_(span, func_type, implicit_args, &mut args.into_iter())
    }

    fn typecheck_application_<'e>(
        &mut self,
        span: Span<BytePos>,
        mut func_type: RcType,
        implicit_args: &mut Vec<SpannedExpr<Symbol>>,
        args: &mut ExactSizeIterator<Item = &'e mut SpannedExpr<Symbol>>,
    ) -> TcResult<TailCall> {
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

        func_type = self.instantiate_generics(&func_type);

        for arg in &mut **implicit_args {
            let arg_ty = self.subs.new_var();
            let ret_ty = self.subs.new_var();
            let f = self
                .subs
                .function_implicit(once(arg_ty.clone()), ret_ty.clone());

            self.subsumes(arg.span, ErrorOrder::ExpectedActual, &f, func_type.clone());

            self.typecheck(arg, &arg_ty);

            func_type = ret_ty;
        }

        let mut not_a_function_index = None;

        let mut prev_arg_end = implicit_args.last().map_or(span, |arg| arg.span).end();
        for arg in args.map(|arg| arg.borrow_mut()) {
            let errors_before = self.errors.len();
            let (arg_ty, ret_ty) =
                self.subsume_function(prev_arg_end, arg.span, func_type.clone(), implicit_args);

            if errors_before != self.errors.len() {
                self.errors.pop();
                not_a_function_index = Some(arg);
                break;
            }

            self.typecheck(arg, &arg_ty);

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
                    self.infer_expr(arg.borrow_mut())
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

        Ok(TailCall::Type(func_type))
    }

    fn typecheck_lambda(
        &mut self,
        function_type: RcType,
        before_args_pos: BytePos,
        args: &mut Vec<Argument<SpannedIdent<Symbol>>>,
        body: &mut SpannedExpr<Symbol>,
    ) -> RcType {
        debug!("Checking lambda {}", function_type);
        debug!("Checking lambda {:#?}", self.type_variables);
        self.enter_scope();

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
                    self.unify_function(span, return_type.clone());

                match type_implicit {
                    ArgType::Implicit => {
                        let arg = match args.get(i).map(|t| t.arg_type) {
                            Some(ArgType::Implicit) => {
                                i += 1;
                                &mut args[i - 1].name.value
                            }
                            _ => {
                                let id = Symbol::from(format!("__implicit_arg"));
                                let pos = if i == 0 {
                                    before_args_pos
                                } else {
                                    args.get(i - 1)
                                        .map(|arg| arg.name.span.end())
                                        .unwrap_or(before_args_pos)
                                };
                                args.insert(
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
                        self.implicit_resolver
                            .add_implicits_of_record(&self.subs, &arg.name, &arg_type);
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
                        None => break,
                    },
                }
                return_type = ret_type;
            }

            return_type
        };

        let body_type = self.typecheck(body, &body_type);
        self.exit_scope();

        let f = self.subs.function(arg_types, body_type);
        let done = self.with_forall(&function_type, f);

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
            _ => self.typecheck_pattern(pattern, match_type),
        }
    }

    fn typecheck_pattern(
        &mut self,
        pattern: &mut SpannedPattern<Symbol>,
        mut match_type: RcType,
    ) -> RcType {
        let span = pattern.span;
        match pattern.value {
            Pattern::As(ref id, ref mut pat) => {
                self.stack_var(id.value.clone(), match_type.clone());
                self.typecheck_pattern(pat, match_type.clone());
                match_type
            }
            Pattern::Constructor(ref mut id, ref mut args) => {
                match_type = self.subs.real(&match_type).clone();
                match_type = self.instantiate_generics(&match_type);
                // Find the enum constructor and return the types for its arguments
                let ctor_type = self.find_at(span, &id.name);
                id.typ = self.subs.bind_arc(&ctor_type);
                let return_type = match self.typecheck_pattern_rec(args, ctor_type) {
                    Ok(return_type) => return_type,
                    Err(err) => self.error(span, err),
                };
                let return_type = self.instantiate_generics(&return_type);
                self.subsumes(span, ErrorOrder::ExpectedActual, &match_type, return_type)
            }
            Pattern::Record {
                typ: ref mut curr_typ,
                types: ref mut associated_types,
                ref mut fields,
                ref implicit_import,
            } => {
                let uninstantiated_match_type = match_type.clone();
                match_type = self.instantiate_generics(&match_type);
                *curr_typ = self.subs.bind_arc(&match_type);

                let mut pattern_fields = Vec::with_capacity(associated_types.len() + fields.len());

                let mut duplicated_fields = FnvSet::default();
                {
                    let all_fields = associated_types
                        .iter()
                        .map(|field| &field.name)
                        .chain(fields.iter().map(|field| &field.name));
                    for field in all_fields {
                        if self.error_on_duplicated_field(&mut duplicated_fields, field.clone()) {
                            pattern_fields.push(field.value.clone());
                        }
                    }
                }

                let record_match_type = self.remove_alias(match_type.clone());

                let mut missing_fields_from_match_type = Vec::new();

                for field in fields {
                    let name = &field.name.value;
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
                    match field.value {
                        Some(ref mut pattern) => {
                            self.typecheck_pattern(pattern, field_type);
                        }
                        None => {
                            self.stack_var(name.clone(), field_type);
                        }
                    }
                }

                // Check that all types declared in the pattern exists
                for field in associated_types.iter_mut() {
                    let name = field.value.as_ref().unwrap_or(&field.name.value).clone();
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
                                field.name.span,
                                TypeError::UndefinedField(match_type.clone(), name.clone()),
                            );
                            // We still define the type so that any uses later on in the program
                            // won't error on UndefinedType
                            alias =
                                self.new_alias(name.clone(), Vec::new(), self.type_cache.hole());
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
                    self.unify_span(pattern.span, &expected, match_type.clone());
                }

                if let Some(ref implicit_import) = *implicit_import {
                    self.implicit_resolver.add_implicits_of_record(
                        &self.subs,
                        &implicit_import.value,
                        &uninstantiated_match_type,
                    );
                }

                match_type
            }
            Pattern::Tuple {
                ref mut typ,
                ref mut elems,
            } => {
                let tuple_type = {
                    let subs = &mut self.subs;
                    (&*subs).tuple(&mut self.symbols, (0..elems.len()).map(|_| subs.new_var()))
                };
                let new_type = self.unify_span(span, &tuple_type, match_type);
                *typ = self.subs.bind_arc(&new_type);
                for (elem, field) in elems.iter_mut().zip(tuple_type.row_iter()) {
                    self.typecheck_pattern(elem, field.typ.clone());
                }
                tuple_type
            }
            Pattern::Ident(ref mut id) => {
                self.stack_var(id.name.clone(), match_type.clone());
                id.typ = self.subs.bind_arc(&match_type);
                match_type
            }
            Pattern::Literal(ref l) => {
                let typ = l.env_type_of(&self.environment.environment.environment);
                let typ = self.translate_arc_type(&typ);
                self.unify_span(span, &match_type, typ);
                match_type
            }
            Pattern::Error => self.subs.new_var(),
        }
    }

    fn typecheck_pattern_rec(
        &mut self,
        args: &mut [SpannedPattern<Symbol>],
        typ: RcType,
    ) -> TcResult<RcType> {
        let len = args.len();
        match args.split_first_mut() {
            Some((head, tail)) => {
                let typ = self.instantiate_generics(&typ);
                match typ.as_function() {
                    Some((arg, ret)) => {
                        self.typecheck_pattern(head, arg.clone());
                        self.typecheck_pattern_rec(tail, ret.clone())
                    }
                    None => Err(TypeError::PatternError(typ.clone(), len)),
                }
            }
            None => Ok(typ),
        }
    }

    fn translate_projected_type(&mut self, id: &[Symbol]) -> TcResult<RcType> {
        translate_projected_type(&self.environment, &mut self.symbols, &mut &self.subs, id)
    }

    fn translate_arc_type(&mut self, arc_type: &ArcType) -> RcType {
        translate_interned_type(
            &mut *RefCell::borrow_mut(&self.type_interner),
            &mut &self.subs,
            &self.type_cache,
            arc_type,
        )
    }

    fn translate_rc_type(&mut self, rc_type: &RcType) -> ArcType {
        translate_rc_interned_type(
            &mut self.arc_type_interner,
            &mut NullInterner,
            &self.arc_type_cache,
            rc_type,
        )
    }

    fn translate_ast_type(
        &mut self,
        type_cache: &TypeCache<Symbol, RcType>,
        ast_type: &AstType<Symbol>,
    ) -> RcType {
        use crate::base::pos::HasSpan;

        match **ast_type {
            // Undo the hack in kindchecking that inserts a dummy alias wrapping a generic
            Type::Alias(ref alias) => match **alias.unresolved_type() {
                Type::Generic(ref gen) if gen.id == alias.name => self.ident(alias.name.clone()),
                _ => types::translate_type_with(type_cache, self, ast_type, |self_, typ| {
                    self_.translate_ast_type(type_cache, typ)
                }),
            },

            Type::ExtendRow {
                ref types,
                ref fields,
                ref rest,
            } => {
                let types = types
                    .iter()
                    .map(|field| Field {
                        name: field.name.clone(),
                        typ: if let Type::Hole = **field.typ.unresolved_type() {
                            self.find_type_info_at(field.typ.unresolved_type().span(), &field.name)
                        } else {
                            let alias_data = types::translate_alias(&field.typ, |typ| {
                                self.translate_ast_type(type_cache, typ)
                            });
                            self.new_data_alias(alias_data)
                        },
                    })
                    .collect();

                let fields = fields
                    .iter()
                    .map(|field| Field {
                        name: field.name.clone(),
                        typ: self.translate_ast_type(type_cache, &field.typ),
                    })
                    .collect();

                let rest = self.translate_ast_type(type_cache, rest);

                self.extend_row(types, fields, rest)
            }

            Type::Projection(ref ids) => match self.translate_projected_type(ids) {
                Ok(typ) => typ,
                Err(err) => self.error(ast_type.span(), err),
            },

            _ => types::translate_type_with(type_cache, self, ast_type, |self_, typ| {
                self_.translate_ast_type(type_cache, typ)
            }),
        }
    }

    fn typecheck_bindings(&mut self, bindings: &mut ValueBindings<Symbol>) -> TcResult<()> {
        self.enter_scope();
        self.type_variables.enter_scope();
        let level = self.subs.var_id();

        let is_recursive = bindings.is_recursive();
        let mut resolved_types = AppVec::new();
        // When the definitions are allowed to be mutually recursive
        if is_recursive {
            for (i, bind) in bindings.iter_mut().enumerate() {
                let typ = {
                    if let Some(ref mut typ) = bind.typ {
                        let type_cache = self.type_cache.clone();
                        let rc_type = self.translate_ast_type(&type_cache, typ);
                        self.kindcheck(typ);

                        resolved_types.push(rc_type);
                    } else {
                        resolved_types.push(self.type_cache.hole());
                    }

                    let typ = self.create_unifiable_signature(&resolved_types[i]);
                    if let Some(typ) = typ {
                        resolved_types[i] = typ;
                    }

                    resolved_types[i].clone()
                };
                self.typecheck_let_pattern(&mut bind.name, typ);
                if let Expr::Lambda(ref mut lambda) = bind.expr.value {
                    if let Pattern::Ident(ref name) = bind.name.value {
                        lambda.id.name = name.name.clone();
                    }
                }
            }
        }

        let mut types = Vec::new();
        for (i, bind) in bindings.iter_mut().enumerate() {
            // Functions which are declared as `let f x = ...` are allowed to be self
            // recursive
            let typ = if !is_recursive {
                if let Some(ref mut typ) = bind.typ {
                    let type_cache = self.type_cache.clone();
                    let rc_type = self.translate_ast_type(&type_cache, typ);
                    self.kindcheck(typ);

                    resolved_types.push(rc_type);
                } else {
                    resolved_types.push(self.type_cache.hole());
                }

                let typ = self.create_unifiable_signature(&resolved_types[i]);
                if let Some(typ) = typ {
                    resolved_types[i] = typ;
                }

                let typ = &resolved_types[i];
                self.skolemize_in(bind.expr.span, &typ, |self_, typ| {
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
                        let type_cache = &self.type_cache;
                        self.environment
                            .stack
                            .get(&id.name)
                            .map_or_else(|| type_cache.error(), |b| b.typ.clone())
                    }
                    _ => self.type_cache.error(),
                };

                self.skolemize_in_no_scope(bind.expr.span, &typ, |self_, function_type| {
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
                let resolved_type = &mut resolved_types[i];
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
            let hole = self.type_cache.hole();
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

            // Update the implicit bindings with the generalized types we just created
            let bindings = self.implicit_resolver.implicit_bindings.last_mut().unwrap();

            let stack = &self.environment.stack;
            bindings.update(|name| Some(stack.get(name).unwrap().typ.clone()));
        }

        debug!("Typecheck `in`");
        self.type_variables.exit_scope();
        Ok(())
    }

    fn typecheck_type_bindings(
        &mut self,
        bindings: &mut [TypeBinding<Symbol>],
        expr: &SpannedExpr<Symbol>,
    ) {
        self.enter_scope();

        // Rename the types so they get a name which is distinct from types from other
        // modules
        for bind in bindings.iter_mut() {
            self.type_variables.enter_scope();

            {
                let type_cache = &self.type_cache;
                self.type_variables.extend(
                    bind.alias
                        .value
                        .params()
                        .iter()
                        .map(|param| (param.id.clone(), type_cache.hole())),
                );
            }
            self.check_undefined_variables(bind.alias.value.unresolved_type());

            self.type_variables.exit_scope();
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
                check.set_variables(bind.alias.value.params());

                let typ = bind
                    .alias
                    .value
                    .unresolved_type_mut()
                    .remove_single_forall();
                if let Err(err) = check.kindcheck_type(typ) {
                    self.errors
                        .push(pos::spanned(err.span, TypeError::from(err.value).into()));
                }
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
            self.type_variables.enter_scope();

            let mut alias = types::translate_alias(&bind.alias.value, |typ| {
                let type_cache = self.type_cache.clone();
                self.translate_ast_type(&type_cache, typ)
            });

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

            self.type_variables.exit_scope();
        }

        let arc_alias_group = Alias::group(
            resolved_aliases
                .iter()
                .map(|a| types::translate_alias(&a, |t| self.translate_rc_type(t)))
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
        if let Err(err) = result {
            self.errors
                .push(pos::spanned(err.span, TypeError::from(err.value).into()));
        }
    }

    fn check_undefined_variables(&mut self, typ: &AstType<Symbol>) {
        use crate::base::pos::HasSpan;
        match **typ {
            Type::Generic(ref id) => {
                if !self.type_variables.contains_key(&id.id) {
                    info!("Undefined type variable {}", id.id);
                    self.error(typ.span(), TypeError::UndefinedVariable(id.id.clone()));
                }
            }
            Type::Record(_) => {
                // Inside records variables are bound implicitly to the closest field
                // so variables are allowed to be undefined/implicit
            }
            _ => {
                if let Type::Forall(ref params, ..) = **typ {
                    let type_cache = &self.type_cache;
                    self.type_variables
                        .extend(params.iter().map(|gen| (gen.id.clone(), type_cache.hole())));
                }
                types::walk_move_type_opt(
                    typ,
                    &mut types::ControlVisitation(|typ: &AstType<_>| {
                        self.check_undefined_variables(typ);
                        None
                    }),
                );
            }
        }
    }

    fn update_var(&mut self, id: &Symbol, typ: &RcType) {
        if let Some(bind) = self.environment.stack.get_mut(id) {
            if let Type::Variable(_) = *bind.typ {
                self.implicit_resolver.on_stack_var(id, typ);
            }
            bind.typ = typ.clone();
        }
        // HACK
        // For type projections
        let id = self.symbols.symbol(id.declared_name());
        if let Some(bind) = self.environment.stack.get_mut(&id) {
            bind.typ = typ.clone();
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
                    let mut field_type = field_type.clone();
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

    fn generalize_type(&mut self, level: u32, typ: &mut RcType, span: Span<BytePos>) {
        debug!("Start generalize {:#?}", self.type_variables);
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
        self.type_variables.enter_scope();

        let mut generalizer = TypeGeneralizer::new(level, self, typ, span);
        let result_type = generalizer.generalize_type(typ);

        generalizer.type_variables.exit_scope();

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

        self.type_variables.extend(scope);

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
            .map(|(id, var)| {
                let kind = var.kind().into_owned();
                Generic::new(id.clone(), kind)
            })
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
                    .find_type_info(id)
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
                ref types,
                ref fields,
                ref rest,
            } => {
                let new_types = types::walk_move_types(types, |field| {
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
                let new_fields = types::walk_move_types(fields, |field| {
                    self.create_unifiable_signature2(&field.typ)
                        .map(|typ| Field::new(field.name.clone(), typ))
                });
                let new_rest = self.create_unifiable_signature_(rest);
                merge::merge3(
                    types,
                    new_types,
                    fields,
                    new_fields,
                    rest,
                    new_rest,
                    |types, fields, rest| {
                        self.intern(Type::ExtendRow {
                            types,
                            fields,
                            rest,
                        })
                    },
                )
            }
            Type::Forall(ref params, ref typ) => {
                for param in params {
                    self.type_variables
                        .insert(param.id.clone(), self.type_cache.hole());
                }
                let result = self.create_unifiable_signature_(typ);
                // Remove any implicit variables inserted inside the forall since
                // they were actually bound at this stage
                for param in params {
                    self.type_variables.remove(&param.id);
                }
                result.map(|typ| self.intern(Type::Forall(params.clone(), typ)))
            }
            Type::Generic(ref generic) => {
                if let Some(typ) = self.type_variables.get(&generic.id) {
                    match **typ {
                        Type::Skolem(_) => Some(typ.clone()),
                        _ => None,
                    }
                } else {
                    match self.unbound_variables.get(&generic.id).cloned() {
                        Some(typ) => match *typ {
                            Type::Variable(_) => None,
                            _ => Some(typ.clone()),
                        },
                        None => {
                            let kind = typ.kind().into_owned();
                            let mut subs = &self.subs;
                            let var = subs.new_var_fn(|id| {
                                subs.variable(TypeVariable {
                                    kind: kind.clone(),
                                    id: id,
                                })
                            });
                            self.unbound_variables.insert(generic.id.clone(), var);
                            None
                        }
                    }
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
        expr: &mut SpannedExpr<Symbol>,
    ) -> RcType {
        let new = self.subsumes_implicit(
            span,
            ErrorOrder::ExpectedActual,
            &r,
            l.clone(),
            &mut |arg| {
                match expr.value {
                    Expr::App { .. } => (),
                    _ => {
                        let dummy = Expr::default();
                        let func = mem::replace(&mut expr.value, dummy);
                        expr.value = Expr::App {
                            func: Box::new(pos::spanned(expr.span, func)),
                            implicit_args: Vec::new(),
                            args: vec![],
                        }
                    }
                }

                match expr.value {
                    Expr::App {
                        ref mut implicit_args,
                        ..
                    } => implicit_args.push(pos::spanned(expr.span, arg)),
                    _ => (),
                }
            },
        );
        // We ended up skolemizing r. To prevent the variables from looking like they
        // are escaping we need to bind the forall at this location
        if let Type::Forall(..) = *new {
            let temp = mem::replace(expr, Default::default());
            *expr = Expr::annotated(temp, self.subs.bind_arc(&new));
        }
        new
    }

    fn subsumes_implicit(
        &mut self,
        span: Span<BytePos>,
        error_order: ErrorOrder,
        expected: &RcType,
        mut actual: RcType,
        receiver: &mut FnMut(Expr<Symbol>),
    ) -> RcType {
        debug!("Subsume expr {} <=> {}", expected, actual);

        self.type_variables.enter_scope();

        // Act as the implicit arguments of `actual` has been supplied (unless `expected` is
        // specified to have implicit arguments)
        loop {
            actual = self.instantiate_generics(&actual);
            actual = match *actual {
                Type::Function(ArgType::Implicit, ref arg_type, ref r_ret) => {
                    match **self.subs.real(expected) {
                        Type::Variable(_) | Type::Function(ArgType::Implicit, _, _) => break,
                        _ => {
                            let name = self.implicit_resolver.make_implicit_ident(arg_type);

                            receiver(Expr::Ident(TypedIdent {
                                name,
                                typ: self.subs.bind_arc(&arg_type),
                            }));

                            r_ret.clone()
                        }
                    }
                }
                _ => break,
            };
        }
        let original_expected = expected;
        let mut expected = expected.clone();
        let mut resolved_implicit = false;

        let mut skolem_scope = FnvMap::default();
        loop {
            expected = expected.skolemize(&mut &self.subs, &mut skolem_scope);
            self.type_variables.extend(skolem_scope.drain());

            expected = match *expected {
                Type::Function(ArgType::Implicit, ref arg_type, ref r_ret) => {
                    match **self.subs.real(&actual) {
                        Type::Variable(_) | Type::Function(ArgType::Implicit, _, _) => break,
                        _ => {
                            resolved_implicit = true;

                            let name = self.implicit_resolver.make_implicit_ident(arg_type);

                            receiver(Expr::Ident(TypedIdent {
                                name,
                                typ: self.subs.bind_arc(&arg_type),
                            }));

                            r_ret.clone()
                        }
                    }
                }
                _ => break,
            };
        }

        // HACK Need to move elaboration/implicit argument insertion into the normal subsumption so
        // variables get correctly subsumed with forall
        if !resolved_implicit {
            expected = original_expected.clone();
        }

        let new_type = self.subsumes(span, error_order, &expected, actual);
        let typ = self.with_forall(original_expected, new_type);

        self.type_variables.exit_scope();

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
                    "Error '{:?}' between:\n>> {}\n>> {}",
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

    fn subsume_function(
        &mut self,
        prev_arg_end: BytePos,
        span: Span<BytePos>,
        actual: RcType,
        implicit_args: &mut Vec<SpannedExpr<Symbol>>,
    ) -> (RcType, RcType) {
        let actual = self.remove_aliases(actual);
        match actual.as_function_with_type() {
            Some((ArgType::Explicit, arg, ret)) => return (arg.clone(), ret.clone()),
            _ => (),
        }

        let arg_ty = self.subs.new_var();
        let ret_ty = self.subs.new_var();
        let f = self.subs.function(once(arg_ty.clone()), ret_ty.clone());

        self.subsumes_implicit(
            span,
            ErrorOrder::ExpectedActual,
            &f,
            actual,
            &mut |implicit_arg| {
                implicit_args.push(pos::spanned2(prev_arg_end, span.start(), implicit_arg));
            },
        );
        (arg_ty, ret_ty)
    }

    fn instantiate_sigma(
        &mut self,
        span: Span<BytePos>,
        typ: &RcType,
        expected_type: &mut Option<&RcType>,
    ) -> (Vec<SpannedExpr<Symbol>>, RcType) {
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

    fn unify_function(&mut self, span: Span<BytePos>, actual: RcType) -> (ArgType, RcType, RcType) {
        let actual = self.remove_aliases(actual);
        match actual.as_function_with_type() {
            Some((arg_type, arg, ret)) => return (arg_type, arg.clone(), ret.clone()),
            None => (),
        }
        let arg = self.subs.new_var();
        let ret = self.subs.new_var();
        let f = self.subs.function(Some(arg.clone()), ret.clone());
        self.unify_span(span, &f, actual);
        (ArgType::Explicit, arg, ret)
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
                self.type_cache.error()
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

    fn with_forall(&mut self, from: &RcType, to: RcType) -> RcType {
        let mut params = Vec::new();
        for param in from.forall_params() {
            params.push(param.clone());
        }
        self.forall(params, to)
    }

    fn skolemize_in(
        &mut self,
        span: Span<BytePos>,
        original_type: &RcType,
        f: impl FnOnce(&mut Self, RcType) -> RcType,
    ) -> RcType {
        self.type_variables.enter_scope();
        let t = self.skolemize_in_no_scope(span, original_type, f);

        self.type_variables.exit_scope();
        t
    }

    fn skolemize_in_no_scope(
        &mut self,
        span: Span<BytePos>,
        original_type: &RcType,
        f: impl FnOnce(&mut Self, RcType) -> RcType,
    ) -> RcType {
        let skolemized = self.skolemize(original_type);
        let new_type = f(self, skolemized);

        let original_type = self.subs.zonk(original_type);
        types::walk_type(&original_type, &mut |typ: &RcType| {
            if let Type::Skolem(skolem) = &**typ {
                if !self.type_variables.contains_key(&skolem.name) {
                    self.error(
                        span,
                        TypeError::Message(format!(
                            "Skolem variable `{}` would escape as it is not bound in `{}`",
                            skolem.name, original_type
                        )),
                    );
                }
            }
        });

        self.with_forall(&original_type, new_type)
    }

    fn skolemize(&mut self, typ: &RcType) -> RcType {
        self.named_variables.clear();
        self.named_variables.extend(
            self.type_variables
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );
        let new_type = typ.skolemize(&mut &self.subs, &mut self.named_variables);
        for (id, typ) in self.named_variables.drain() {
            match self.type_variables.entry(id) {
                scoped_map::Entry::Vacant(e) => {
                    e.insert(typ);
                }
                scoped_map::Entry::Occupied(mut e) => {
                    if *e.get() != typ {
                        e.insert(typ);
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

    fn error_on_duplicated_field(
        &mut self,
        duplicated_fields: &mut FnvSet<String>,
        new_name: Spanned<Symbol, BytePos>,
    ) -> bool {
        let span = new_name.span;
        duplicated_fields
            .replace(new_name.value.declared_name().to_string())
            .map_or(true, |name| {
                self.errors.push(Spanned {
                    span: span,
                    // TODO Help to the other fields location
                    value: TypeError::DuplicateField(name).into(),
                });
                false
            })
    }

    fn check_macro(&mut self, expr: &mut SpannedExpr<Symbol>) -> Option<TcResult<TailCall>> {
        let (replacement, typ) = match expr.value {
            Expr::App {
                ref mut func,
                ref mut args,
                ..
            } => match func.value {
                Expr::Ident(ref id) => match id.name.declared_name() {
                    "convert_effect!" => {
                        let (name, typ) = match args.len() {
                            1 => (None, self.infer_expr(&mut args[0])),
                            2 => (
                                Some(match args[0].value {
                                    Expr::Ident(ref id) => id.name.clone(),
                                    _ => unreachable!(),
                                }),
                                self.infer_expr(&mut args[1]),
                            ),
                            _ => unreachable!(),
                        };

                        let unaliased = self.remove_aliases(typ.clone());
                        let valid_type = match *unaliased {
                            Type::Forall(ref params, ref variant) => match **variant {
                                Type::Variant(ref variant) => {
                                    let mut iter = variant.row_iter();
                                    for _ in iter.by_ref() {}
                                    match **iter.current_type() {
                                        Type::Generic(ref gen) => {
                                            params.iter().any(|param| param.id == gen.id)
                                        }
                                        _ => false,
                                    }
                                }
                                _ => false,
                            },
                            _ => false,
                        };
                        if !valid_type {
                            return Some(Err(TypeError::Message(format!("Invalid form for the type. Expect the type to be of the form `forall a . | Variant X | a` but found `{}`", unaliased))));
                        }

                        let f = self.subs.new_var();
                        let arg = self.subs.new_var();
                        let expected_shape = self.app(f.clone(), collect![arg.clone()]);
                        self.unify_span(expr.span, &expected_shape, typ);

                        let eff = self.poly_effect(
                            name.map(|name| Field {
                                name,
                                typ: self.subs.real(&f).clone(),
                            })
                            .into_iter()
                            .collect(),
                            self.subs.new_var(),
                        );
                        (
                            args.pop().unwrap(),
                            self.app(eff, collect![self.subs.real(&arg).clone()]),
                        )
                    }
                    "convert_variant!" => {
                        let typ = self.infer_expr(&mut args[0]);

                        let unaliased = self.remove_aliases(typ);
                        let variant_type = match *unaliased {
                            Type::App(ref f, ref type_args) if type_args.len() == 1 => {
                                let f = self.subs.real(f).clone();
                                match *f {
                                    Type::Effect(ref row) => row.row_iter().fold(
                                        self.poly_variant(vec![], self.subs.new_var()),
                                        |variant, field| {
                                            let typ = self.app(
                                                field.typ.clone(),
                                                collect![type_args[0].clone()],
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
                                    ),
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
                        (args.pop().unwrap(), variant_type)
                    }

                    _ => return None,
                },

                _ => return None,
            },

            _ => return None,
        };

        *expr = Expr::annotated(replacement, self.subs.bind_arc(&typ));

        Some(Ok(TailCall::Type(typ)))
    }
}

pub fn translate_projected_type(
    env: &TypeEnv<Type = RcType>,
    symbols: &mut IdentEnv<Ident = Symbol>,
    interner: &mut impl TypeInterner<Symbol, RcType>,
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
                    .cloned()
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

fn with_pattern_types<'a: 'b, 'b>(
    fields: &'a mut [PatternField<Symbol, SpannedPattern<Symbol>>],
    typ: &'b RcType,
) -> impl Iterator<
    Item = (
        &'a Spanned<Symbol, BytePos>,
        &'a mut Option<SpannedPattern<Symbol>>,
        &'b RcType,
    ),
> {
    fields.iter_mut().filter_map(move |field| {
        // If the field in the pattern does not exist (undefined field error) then skip it as
        // the error itself will already have been reported
        let opt = typ
            .row_iter()
            .find(|type_field| type_field.name.name_eq(&field.name.value));
        opt.map(move |associated_type| (&field.name, &mut field.value, &associated_type.typ))
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
    env: &'a TypeEnv<Type = RcType>,
    typ: &'a RcType,
) -> Option<(&'a AliasRef<Symbol, RcType>, Cow<'a, [RcType]>)> {
    match **typ {
        Type::Alias(ref alias) => Some((alias, Cow::Borrowed(&[][..]))),
        Type::App(ref alias, ref args) => match **alias {
            Type::Alias(ref alias) => Some((alias, Cow::Borrowed(&args[..]))),
            _ => None,
        },
        _ => typ.alias_ident().and_then(|id| {
            env.find_type_info(id)
                .map(|alias| (&**alias, typ.unapplied_args()))
        }),
    }
}
struct FunctionArgIter<'a, 'b: 'a> {
    tc: &'a mut Typecheck<'b>,
    typ: RcType,
}

impl<'a, 'b> Iterator for FunctionArgIter<'a, 'b> {
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
                        match alias.typ(&mut &self.tc.subs).apply_args(
                            alias.params(),
                            &args,
                            &mut &self.tc.subs,
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

fn function_arg_iter<'a, 'b>(tc: &'a mut Typecheck<'b>, typ: RcType) -> FunctionArgIter<'a, 'b> {
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

fn generalize_binding(
    generalizer: &mut TypeGeneralizer,
    resolved_type: &mut RcType,
    binding: &mut ValueBinding<Symbol>,
) {
    crate::implicits::resolve(generalizer.tc, &mut binding.expr);

    generalizer.tc.type_variables.enter_scope();

    {
        let type_cache = &generalizer.tc.type_cache;
        generalizer.tc.type_variables.extend(
            resolved_type
                .forall_params()
                .map(|param| (param.id.clone(), type_cache.hole())),
        );
    }

    {
        generalizer.generalize_type_top(resolved_type);

        generalizer.generalize_variables(
            &mut binding.args.iter_mut().map(|arg| &mut arg.name),
            &mut binding.expr,
        );
    }
    generalizer.tc.type_variables.exit_scope();
}
