//! The main typechecking interface which is responsible for typechecking expressions, patterns,
//! etc. Only checks which need to be aware of expressions are handled here the actual unifying and
//! checking of types are done in the `unify_type` and `kindcheck` modules.
use std::borrow::Cow;
use std::fmt;
use std::iter::once;
use std::mem;

use itertools::Itertools;

use base::scoped_map::ScopedMap;
use base::ast::{Argument, AstType, DisplayEnv, Do, Expr, Literal, MutVisitor, Pattern,
                PatternField, SpannedExpr, SpannedIdent, SpannedPattern, TypeBinding, Typed,
                TypedIdent, ValueBinding};
use base::error::Errors;
use base::fnv::{FnvMap, FnvSet};
use base::metadata::{Metadata, MetadataEnv};
use base::resolve;
use base::kind::{ArcKind, Kind, KindCache, KindEnv};
use base::merge;
use base::pos::{self, BytePos, Span, Spanned};
use base::symbol::{Symbol, SymbolModule, SymbolRef, Symbols};
use base::types::{self, Alias, AliasRef, AppVec, ArcType, ArgType, BuiltinType, Field, Filter,
                  Generic, PrimitiveEnv, Skolem, Type, TypeCache, TypeEnv,
                  TypeFormatter, TypeVariable};

use kindcheck::{self, Error as KindCheckError, KindCheck, KindError};
use substitution::{self, Substitution};
use unify::{self, Error as UnifyError};
use unify_type::{self, new_skolem_scope, Error as UnifyTypeError};

/// Type representing a single error when checking a type
#[derive(Debug, PartialEq)]
pub enum TypeError<I> {
    /// Variable has not been defined before it was used
    UndefinedVariable(I),
    /// Attempt to call a type which is not a function
    NotAFunction(ArcType<I>),
    /// Type has not been defined before it was used
    UndefinedType(I),
    /// Type were expected to have a certain field
    UndefinedField(ArcType<I>, I),
    /// Constructor type was found in a pattern but did not have the expected number of arguments
    PatternError(ArcType<I>, usize),
    /// Errors found when trying to unify two types
    Unification(ArcType<I>, ArcType<I>, Vec<UnifyTypeError<I>>),
    /// Error were found when trying to unify the kinds of two types
    KindError(KindCheckError<I>),
    /// Multiple types were declared with the same name in the same expression
    DuplicateTypeDefinition(I),
    /// A field was defined more than once in a record constructor or pattern match
    DuplicateField(String),
    /// Type is not a type which has any fields
    InvalidProjection(ArcType<I>),
    /// Expected to find a record with the following fields
    UndefinedRecord {
        fields: Vec<I>,
    },
    /// Found a case expression without any alternatives
    EmptyCase,
    Message(String),
    /// An implicit parameter were not possible to resolve
    UnableToResolveImplicit(ArcType<I>, Vec<String>),
    LoopInImplicitResolution(Vec<String>),
    AmbiguousImplicit(Vec<(String, ArcType<I>)>),
}

impl<I> From<KindCheckError<I>> for TypeError<I> {
    fn from(e: KindCheckError<I>) -> Self {
        match e {
            UnifyError::Other(KindError::UndefinedType(name)) => TypeError::UndefinedType(name),
            e => TypeError::KindError(e),
        }
    }
}

impl<I: fmt::Display + AsRef<str> + Clone> fmt::Display for TypeError<I> {
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
                let arena = Arena::new();
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

                let arena = Arena::new();
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
                ].group();
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
                        UnifyError::Other(ref err) => err.filter_fmt(&filter, f)?,
                        _ => writeln!(f, "{}", error)?,
                    }
                }
                write!(f, "{}", errors.last().unwrap())
            }
            PatternError(ref typ, expected_len) => {
                write!(f, "Type {} has {} to few arguments", typ, expected_len)
            }
            KindError(ref err) => kindcheck::fmt_kind_error(err, f),
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
            UnableToResolveImplicit(ref typ, ref paths) => write!(
                f,
                "Implicit parameter with type `{}` could not be resolved.\nPossible bindings: {}",
                typ,
                paths.iter().format(", ")
            ),
            LoopInImplicitResolution(ref paths) => write!(
                f,
                "Unable to resolve implicit, possible infinite loop. When resolving, {}",
                paths.iter().format(", ")
            ),
            AmbiguousImplicit(ref candidates) => write!(
                f,
                "Unable to resolve implicit. Multiple candidates were found: {}",
                candidates
                    .iter()
                    .format_with(", ", |&(ref path, ref typ), fmt| fmt(&format_args!(
                        "{}: {}",
                        path, typ
                    )))
            ),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Help {
    UndefinedFlatMapInDo,
}

impl fmt::Display for Help {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Help::UndefinedFlatMapInDo => write!(
                f,
                "Try bringing the `flat_map` function found in the `Monad`\
                 instance for your type into scope"
            ),
        }
    }
}

pub type HelpError<Id> = ::base::error::Help<TypeError<Id>, Help>;
pub type SpannedTypeError<Id> = Spanned<HelpError<Id>, BytePos>;

pub(crate) type TcResult<T> = Result<T, TypeError<Symbol>>;

pub trait TypecheckEnv: PrimitiveEnv + MetadataEnv {}

impl<T> TypecheckEnv for T
where
    T: PrimitiveEnv + MetadataEnv,
{
}

#[derive(Clone, Debug)]
struct StackBinding {
    typ: ArcType,
}

pub(crate) struct Environment<'a> {
    /// The global environment which the typechecker extracts types from
    environment: &'a (TypecheckEnv + 'a),
    /// Stack allocated variables
    stack: ScopedMap<Symbol, StackBinding>,
    /// Types which exist in some scope (`type Test = ... in ...`)
    stack_types: ScopedMap<Symbol, (ArcType, Alias<Symbol, ArcType>)>,
}

impl<'a> KindEnv for Environment<'a> {
    fn find_kind(&self, type_name: &SymbolRef) -> Option<ArcKind> {
        self.stack_types
            .get(type_name)
            .map(|&(_, ref alias)| {
                let mut kind = Kind::typ();
                for arg in alias.params().iter().rev() {
                    kind = Kind::function(arg.kind.clone(), kind);
                }
                kind
            })
            .or_else(|| self.environment.find_kind(type_name))
    }
}

impl<'a> TypeEnv for Environment<'a> {
    fn find_type(&self, id: &SymbolRef) -> Option<&ArcType> {
        self.stack
            .get(id)
            .map(|bind| &bind.typ)
            .or_else(|| self.environment.find_type(id))
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>> {
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
    Type(ArcType),
    /// Returned from typechecking a `let` or `type` expresion to indicate that the expression body
    /// should be typechecked now.
    TailCall,
}

/// Struct which provides methods to typecheck expressions.
pub struct Typecheck<'a> {
    pub(crate) environment: Environment<'a>,
    symbols: SymbolModule<'a>,
    /// Mapping from the fresh symbol generated during typechecking to the symbol that was assigned
    /// during typechecking
    original_symbols: ScopedMap<Symbol, Symbol>,
    pub(crate) subs: Substitution<ArcType>,
    named_variables: FnvMap<Symbol, ArcType>,
    pub(crate) errors: Errors<SpannedTypeError<Symbol>>,
    /// Type variables `let test: a -> b` (`a` and `b`)
    type_variables: ScopedMap<Symbol, ArcType>,
    type_cache: TypeCache<Symbol, ArcType>,
    kind_cache: KindCache,

    pub(crate) implicit_resolver: ::implicits::ImplicitResolver<'a>,
}

/// Error returned when unsuccessfully typechecking an expression
pub type Error = Errors<SpannedTypeError<Symbol>>;

impl<'a> Typecheck<'a> {
    /// Create a new typechecker which typechecks expressions in `module`
    pub fn new(
        module: String,
        symbols: &'a mut Symbols,
        environment: &'a (TypecheckEnv + 'a),
        type_cache: TypeCache<Symbol, ArcType>,
    ) -> Typecheck<'a> {
        let symbols = SymbolModule::new(module, symbols);
        let kind_cache = KindCache::new();
        Typecheck {
            environment: Environment {
                environment: environment,
                stack: ScopedMap::new(),
                stack_types: ScopedMap::new(),
            },
            symbols: symbols,
            original_symbols: ScopedMap::new(),
            subs: Substitution::new(kind_cache.typ()),
            named_variables: FnvMap::default(),
            errors: Errors::new(),
            type_variables: ScopedMap::new(),
            type_cache: type_cache,
            kind_cache: kind_cache,
            implicit_resolver: ::implicits::ImplicitResolver::new(environment),
        }
    }

    pub(crate) fn error<E>(&mut self, span: Span<BytePos>, error: E) -> ArcType
    where
        E: Into<HelpError<Symbol>>,
    {
        self.errors.push(Spanned {
            span: span,
            value: error.into(),
        });
        self.subs.new_var()
    }

    fn bool(&self) -> ArcType {
        self.environment.get_bool().clone()
    }

    fn find_at(&mut self, span: Span<BytePos>, id: &Symbol) -> ArcType {
        match self.find(id) {
            Ok(typ) => typ,
            Err(err) => self.error(span, err),
        }
    }

    fn find(&mut self, id: &Symbol) -> TcResult<ArcType> {
        match self.environment.find_type(id).map(ArcType::clone) {
            Some(typ) => {
                let typ = self.subs.set_type(typ);

                self.named_variables.clear();
                let typ = new_skolem_scope(&self.subs, &typ);
                debug!("Find {} : {}", self.symbols.string(id), typ);
                Ok(typ)
            }
            None => {
                // Don't report global variables inserted by the `import!` macro as undefined
                // (if they don't exist the error will already have been reported by the macro)
                if id.is_global() {
                    Ok(self.subs.new_var())
                } else {
                    Err(TypeError::UndefinedVariable(id.clone()))
                }
            }
        }
    }

    fn find_type_info(&self, id: &Symbol) -> TcResult<&Alias<Symbol, ArcType>> {
        self.environment
            .find_type_info(id)
            .ok_or_else(|| TypeError::UndefinedType(id.clone()))
    }

    fn stack_var(&mut self, id: Symbol, typ: ArcType) {
        debug!("Insert {} : {}", id, typ);

        self.implicit_resolver.on_stack_var(&id, &typ);

        // HACK
        // Insert the non_renamed symbol so that type projections in types can be translated (see
        // translate_projected_type)
        let non_renamed_symbol = self.symbols.symbol(id.declared_name());
        self.environment
            .stack
            .insert(non_renamed_symbol, StackBinding { typ: typ.clone() });

        self.environment.stack.insert(id, StackBinding { typ: typ });
    }

    fn stack_type(&mut self, id: Symbol, alias: &Alias<Symbol, ArcType>) {
        // Insert variant constructors into the local scope
        let aliased_type = alias.typ();
        if let Type::Variant(ref row) = **aliased_type.remove_forall() {
            for field in row.row_iter().cloned() {
                let symbol = self.symbols.symbol(field.name.as_ref());
                self.original_symbols.insert(symbol, field.name.clone());
                self.stack_var(
                    field.name,
                    Type::forall(alias.params().to_owned(), field.typ),
                );
            }
        }
        let generic_args = alias.params().iter().cloned().map(Type::generic).collect();
        let typ = Type::<_, ArcType>::app(alias.as_ref().clone(), generic_args);
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
        self.original_symbols.enter_scope();
        self.implicit_resolver.enter_scope();
    }

    fn exit_scope(&mut self) {
        self.environment.stack.exit_scope();
        self.environment.stack_types.exit_scope();
        self.original_symbols.exit_scope();
        self.implicit_resolver.exit_scope();
    }

    fn generalize_binding(&mut self, level: u32, binding: &mut ValueBinding<Symbol>) {
        self.generalize_variables(
            level,
            &mut binding.args.iter_mut().map(|arg| &mut arg.name),
            &mut binding.expr,
        );
        self.generalize_type(level, &mut binding.resolved_type);
    }

    /// Generalizing updates all variables which are above `level` into "generic variables". A
    /// generic variable is instantiated with a fresh type variable each time it is refered to.
    ///
    /// Generalzing is a crucial part when inferring types as types will otherwise be less general
    /// than they need to. Consider the following expression.
    /// ```f#
    /// let id x = x
    /// in id 2
    /// ```
    /// If the variable in `id` was not generalized before the `id 2` call the variable would be
    /// unified to an `Int` which is not what we want. Generalazing before checking the body of the
    /// `let` basically infers that the variables in `id` does not refer to anything outside the
    /// `let` scope and can thus be "generalized" into `a -> a` which is instantiated with a fresh
    /// type variable in the `id 2` call.
    fn generalize_variables<'i>(
        &mut self,
        level: u32,
        args: &mut Iterator<Item = &'i mut SpannedIdent<Symbol>>,
        expr: &mut SpannedExpr<Symbol>,
    ) {
        self.type_variables.enter_scope();

        // Replaces all type variables with their inferred types
        struct ReplaceVisitor<'a, 'b: 'a> {
            level: u32,
            tc: &'a mut Typecheck<'b>,
        }

        impl<'a, 'b, 'c> MutVisitor<'c> for ReplaceVisitor<'a, 'b> {
            type Ident = Symbol;

            fn visit_typ(&mut self, typ: &mut ArcType) {
                let mut generalizer = TypeGeneralizer::new(self.level, &mut self.tc, typ);
                if let Some(finished) = generalizer.generalize_type(typ) {
                    *typ = finished;
                }
            }
        }

        ::implicits::resolve(self, expr);

        {
            let mut visitor = ReplaceVisitor {
                level: level,
                tc: self,
            };
            visitor.visit_expr(expr);
            for arg in &mut *args {
                visitor.visit_typ(&mut arg.value.typ)
            }
        }

        self.type_variables.exit_scope();
    }

    fn generalize_type_errors(&mut self, errors: &mut Error) {
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
                | Message(_)
                | LoopInImplicitResolution(..) => (),
                NotAFunction(ref mut typ)
                | UndefinedField(ref mut typ, _)
                | PatternError(ref mut typ, _)
                | InvalidProjection(ref mut typ)
                | UnableToResolveImplicit(ref mut typ, _) => {
                    self.generalize_type(0, typ);
                }
                AmbiguousImplicit(ref mut xs) => for &mut (_, ref mut typ) in xs {
                    self.generalize_type(0, typ);
                },
                Unification(ref mut expected, ref mut actual, ref mut errors) => {
                    self.generalize_type_without_forall(0, expected);
                    self.generalize_type_without_forall(0, actual);
                    for err in errors {
                        match *err {
                            unify::Error::TypeMismatch(ref mut l, ref mut r) => {
                                self.generalize_type_without_forall(0, l);
                                self.generalize_type_without_forall(0, r);
                            }
                            unify::Error::Substitution(ref mut err) => match *err {
                                substitution::Error::Occurs(_, ref mut typ) => {
                                    self.generalize_type_without_forall(0, typ);
                                }
                            },
                            unify::Error::Other(ref mut err) => {
                                if let unify_type::TypeError::MissingFields(ref mut typ, _) = *err {
                                    self.generalize_type_without_forall(0, typ);
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
        fn tail_expr(e: &mut SpannedExpr<Symbol>) -> &mut SpannedExpr<Symbol> {
            match e.value {
                Expr::LetBindings(_, ref mut b) | Expr::TypeBindings(_, ref mut b) => tail_expr(b),
                _ => e,
            }
        }
        info!("Typechecking {}", self.symbols.module());
        self.subs.clear();
        self.environment.stack.clear();

        let _ = ::rename::rename(&mut self.symbols, expr);
        self.implicit_resolver.metadata = ::metadata::metadata(&self.environment, expr).1;

        let temp = expected_type.and_then(|expected| self.create_unifiable_signature(expected));
        let expected_type = temp.as_ref().or(expected_type);

        let mut typ = self.typecheck_opt(expr, expected_type);
        // Only the 'tail' expression need to be generalized at this point as all bindings
        // will have already been generalized
        self.generalize_variables(0, &mut [].iter_mut(), tail_expr(expr));

        self.generalize_type(0, &mut typ);
        typ = types::walk_move_type(typ, &mut unroll_typ);

        if self.errors.has_errors() {
            let mut errors = mem::replace(&mut self.errors, Errors::new());
            self.generalize_type_errors(&mut errors);
            Err(errors)
        } else {
            debug!("Typecheck result: {}", typ);
            Ok(typ)
        }
    }

    fn infer_expr(&mut self, expr: &mut SpannedExpr<Symbol>) -> ArcType {
        self.typecheck_opt(expr, None)
    }

    fn typecheck(&mut self, expr: &mut SpannedExpr<Symbol>, expected_type: &ArcType) -> ArcType {
        self.typecheck_opt(expr, Some(expected_type))
    }

    /// Main typechecking function. Returns the type of the expression if typechecking was
    /// successful
    fn typecheck_opt(
        &mut self,
        mut expr: &mut SpannedExpr<Symbol>,
        expected_type: Option<&ArcType>,
    ) -> ArcType {
        fn moving<T>(t: T) -> T {
            t
        }
        // How many scopes that have been entered in this "tailcall" loop
        let mut scope_count = 0;
        let returned_type;
        loop {
            let expected_type = expected_type.map(|t| self.skolemize(t));
            let mut expected_type = expected_type.as_ref();
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
                        TailCall::Type(mut typ) => {
                            returned_type = match expected_type {
                                Some(expected_type) => {
                                    let level = self.subs.var_id();
                                    self.subsumes_expr(expr.span, level, &expected_type, typ, expr)
                                }
                                None => typ,
                            };
                            break;
                        }
                    }
                }
                Err(err) => {
                    returned_type = self.subs.new_var();
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
        expected_type: &mut Option<&ArcType<Symbol>>,
    ) -> Result<TailCall, TypeError<Symbol>> {
        match expr.value {
            Expr::Ident(ref mut id) => {
                if let Some(new) = self.original_symbols.get(&id.name) {
                    id.name = new.clone();
                }
                id.typ = self.find(&id.name)?;
                Ok(TailCall::Type(id.typ.clone()))
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
                    let prim_type = self.type_cache.builtin_type(builtin_type);
                    let return_type = match &op_name[1 + op_type.len()..] {
                        "+" | "-" | "*" | "/" => prim_type.clone(),
                        "==" | "<" => self.bool(),
                        _ => return Err(TypeError::UndefinedVariable(op.value.name.clone())),
                    };
                    self.type_cache.function(
                        vec![prim_type.clone(), prim_type.clone()],
                        return_type.clone(),
                    )
                } else {
                    match &*op_name {
                        "&&" | "||" => self.type_cache
                            .function(vec![self.bool(), self.bool()], self.bool()),
                        _ => self.find(&op.value.name)?,
                    }
                };

                op.value.typ = func_type.clone();

                self.typecheck_application(
                    op.span,
                    func_type,
                    implicit_args,
                    Some(&mut **lhs).into_iter().chain(Some(&mut **rhs)),
                )
            }
            Expr::Tuple {
                ref mut typ,
                elems: ref mut exprs,
            } => {
                *typ = match exprs.len() {
                    0 => Type::unit(),
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
                        Type::record(vec![], fields)
                    }
                };
                Ok(TailCall::Type(typ.clone()))
            }
            Expr::Match(ref mut expr, ref mut alts) => {
                let typ = self.infer_expr(&mut **expr);
                let mut expected_alt_type = expected_type.cloned();

                let expected_type = expected_type.take();

                for alt in alts.iter_mut() {
                    self.enter_scope();
                    self.typecheck_pattern(&mut alt.pattern, typ.clone());
                    let mut alt_type = self.typecheck_opt(&mut alt.expr, expected_type);
                    alt_type = self.instantiate_generics(&alt_type);
                    self.exit_scope();
                    // All alternatives must unify to the same type
                    if let Some(ref expected) = expected_alt_type {
                        alt_type = self.unify(expected, alt_type)?;
                    }
                    expected_alt_type = Some(alt_type);
                }
                expected_alt_type
                    .ok_or(TypeError::EmptyCase)
                    .map(TailCall::Type)
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
                        *ast_field_typ = match field_type {
                            Some(typ) => self.new_skolem_scope(&typ),
                            None => {
                                // FIXME As the polymorphic `record_type` do not have the type
                                // fields which `typ` this unification is only done after we
                                // checked if the field exists which lets field accesses on
                                // types with type fields still work
                                let field_var = self.subs.new_var();
                                let field = Field::new(field_id.clone(), field_var.clone());
                                let record_type =
                                    Type::poly_record(vec![], vec![field], self.subs.new_var());
                                self.unify(&record_type, record)?;
                                field_var
                            }
                        };
                        Ok(TailCall::Type(ast_field_typ.clone()))
                    }
                    _ => Err(TypeError::InvalidProjection(record)),
                }
            }
            Expr::Array(ref mut array) => {
                let mut expected_element_type = self.subs.new_var();

                if let Some(expected_type) = expected_type.take() {
                    array.typ = self.type_cache.array(expected_element_type.clone());
                    self.unify_span(expr.span, &expected_type, array.typ.clone());
                }

                for expr in &mut array.exprs {
                    expected_element_type = self.typecheck(expr, &expected_element_type);
                }

                Ok(TailCall::Type(array.typ.clone()))
            }
            Expr::Lambda(ref mut lambda) => {
                let loc = format!("{}.lambda:{}", self.symbols.module(), expr.span.start);
                lambda.id.name = self.symbols.symbol(loc);
                let level = self.subs.var_id();
                let function_type = expected_type
                    .cloned()
                    .unwrap_or_else(|| self.subs.new_var());

                let mut typ = self.typecheck_lambda(
                    function_type,
                    expr.span.start,
                    &mut lambda.args,
                    &mut lambda.body,
                );

                self.generalize_type(level, &mut typ);
                lambda.id.typ = typ.clone();
                Ok(TailCall::Type(typ))
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
                let expected_type = expected_type.map(|expected_type| {
                    let typ = resolve::remove_aliases_cow(&self.environment, expected_type);
                    self.new_skolem_scope(&typ)
                });
                let expected_type = expected_type.as_ref();

                let mut new_types: Vec<Field<_, _>> = Vec::with_capacity(types.len());

                let mut duplicated_fields = FnvSet::default();
                for field in types {
                    if let Some(ref mut typ) = field.value {
                        *typ = self.create_unifiable_signature(typ)
                            .unwrap_or_else(|| typ.clone());
                    }

                    let alias = match self.find_type_info(&field.name.value)
                        .map(|alias| alias.clone())
                    {
                        Ok(alias) => alias,
                        Err(err) => {
                            self.errors.push(Spanned {
                                span: field.name.span,
                                value: err.into(),
                            });
                            Alias::new(field.name.value.clone(), self.type_cache.hole())
                        }
                    };
                    if self.error_on_duplicated_field(&mut duplicated_fields, field.name.clone()) {
                        new_types.push(Field::new(field.name.value.clone(), alias));
                    }
                }

                let mut new_fields: Vec<Field<_, _>> = Vec::with_capacity(fields.len());
                for field in fields {
                    let level = self.subs.var_id();

                    let name = &field.name.value;
                    let expected_field_type = expected_type
                        .and_then(|expected_type| {
                            expected_type
                                .row_iter()
                                .find(|expected_field| expected_field.name.name_eq(&name))
                        })
                        .map(|field| &field.typ);

                    let typ = match field.value {
                        Some(ref mut expr) => {
                            let mut typ = self.typecheck_opt(expr, expected_field_type);

                            self.generalize_type(level, &mut typ);
                            new_skolem_scope(&self.subs, &typ)
                        }
                        None => {
                            let typ = self.find_at(field.name.span, &field.name.value);
                            match expected_field_type {
                                Some(expected_field_type) => {
                                    let mut implicit_args = Vec::new();
                                    let typ = self.subsumes_implicit(
                                        field.name.span,
                                        level,
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
                                                        typ: typ.clone(),
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
                    if self.error_on_duplicated_field(&mut duplicated_fields, field.name.clone()) {
                        new_fields.push(Field::new(field.name.value.clone(), typ));
                    }
                }

                if let Some(ref mut base) = *base {
                    let base_type = self.infer_expr(base);
                    let base_type = self.remove_aliases(base_type);

                    let record_type = Type::poly_record(vec![], vec![], self.subs.new_var());
                    let base_type = self.unify_span(base.span, &record_type, base_type);

                    new_types.extend(
                        base_type
                            .type_field_iter()
                            .filter(|field| !duplicated_fields.contains(field.name.declared_name()))
                            .cloned(),
                    );
                    new_fields.extend(
                        base_type
                            .row_iter()
                            .filter(|field| !duplicated_fields.contains(field.name.declared_name()))
                            .cloned(),
                    );
                }

                *typ = self.type_cache.record(new_types, new_fields);
                Ok(TailCall::Type(typ.clone()))
            }
            Expr::Block(ref mut exprs) => {
                let (last, exprs) = exprs.split_last_mut().expect("Expr in block");
                for expr in exprs {
                    self.infer_expr(expr);
                }
                Ok(TailCall::Type(self.typecheck_opt(
                    last,
                    expected_type.take(),
                )))
            }
            Expr::Do(Do {
                ref mut id,
                ref mut bound,
                ref mut body,
                ref mut flat_map_id,
            }) => {
                let flat_map_type = match flat_map_id
                    .as_mut()
                    .expect("flat_map inserted during renaming")
                    .value
                {
                    Expr::Ident(ref mut flat_map) => match self.find(&flat_map.name) {
                        Ok(x) => x,
                        Err(error) => {
                            self.error(
                                id.span,
                                ::base::error::Help {
                                    error,
                                    help: Some(Help::UndefinedFlatMapInDo),
                                },
                            );
                            self.subs.new_var()
                        }
                    },
                    _ => ice!("flat_map_id not inserted during renaming"),
                };

                let flat_map_type = self.instantiate_generics(&flat_map_type);

                let flat_map_type = match *flat_map_type {
                    Type::Function(ArgType::Implicit, ref arg_type, ref r) => {
                        let name = self.implicit_resolver.make_implicit_ident(arg_type);
                        *flat_map_id = Some(Box::new(pos::spanned(
                            id.span,
                            Expr::App {
                                func: flat_map_id.take().unwrap(),
                                args: vec![
                                    pos::spanned(
                                        id.span,
                                        Expr::Ident(TypedIdent {
                                            name,
                                            typ: arg_type.clone(),
                                        }),
                                    ),
                                ],
                                implicit_args: Vec::new(),
                            },
                        )));
                        r.clone()
                    }
                    _ => flat_map_type.clone(),
                };

                id.value.typ = self.subs.new_var();
                let arg1 = self.type_cache
                    .function(Some(id.value.typ.clone()), self.subs.new_var());

                let arg2 = self.subs.new_var();
                let ret = expected_type
                    .cloned()
                    .unwrap_or_else(|| self.subs.new_var());
                let func_type = self.type_cache
                    .function(vec![arg1.clone(), arg2.clone()], ret.clone());

                self.unify_span(expr.span, &flat_map_type, func_type);

                let bound_type = self.typecheck(bound, &arg2);

                self.unify_span(bound.span, &arg2, bound_type);

                self.stack_var(id.value.name.clone(), id.value.typ.clone());

                let body_type = self.typecheck(body, &ret);

                let ret = self.unify_span(body.span, &ret, body_type);

                Ok(TailCall::Type(ret))
            }
            Expr::Error(ref typ) => Ok(TailCall::Type(
                typ.clone().unwrap_or_else(|| self.subs.new_var()),
            )),
        }
    }

    fn typecheck_application<'e, I>(
        &mut self,
        span: Span<BytePos>,
        mut func_type: ArcType,
        implicit_args: &mut Vec<SpannedExpr<Symbol>>,
        args: I,
    ) -> Result<TailCall, TypeError<Symbol>>
    where
        I: IntoIterator<Item = &'e mut SpannedExpr<Symbol>>,
    {
        let mut prev_arg_end = span.end;

        func_type = self.new_skolem_scope(&func_type);
        for arg in &mut **implicit_args {
            let f = self.type_cache
                .function_implicit(once(self.subs.new_var()), self.subs.new_var());
            func_type = self.instantiate_generics(&func_type);
            let level = self.subs.var_id();

            self.subsumes(arg.span, level, &f, func_type.clone());

            func_type = match f.as_function() {
                Some((arg_ty, ret_ty)) => {
                    let arg_ty = self.subs.real(arg_ty).clone();
                    let actual = self.typecheck(arg, &arg_ty);
                    let actual = self.instantiate_generics(&actual);

                    let level = self.subs.var_id();
                    self.subsumes_expr(expr_check_span(arg), level, &arg_ty, actual, arg);

                    ret_ty.clone()
                }
                None => return Err(TypeError::NotAFunction(func_type.clone())),
            };
            prev_arg_end = arg.span.end;
        }

        for arg in args {
            let f = self.type_cache
                .function(once(self.subs.new_var()), self.subs.new_var());
            func_type = self.instantiate_generics(&func_type);
            let level = self.subs.var_id();
            self.subsumes_implicit(span, level, &f, func_type.clone(), &mut |implicit_arg| {
                implicit_args.push(pos::spanned2(prev_arg_end, arg.span.start, implicit_arg));
            });

            func_type = match f.as_function() {
                Some((arg_ty, ret_ty)) => {
                    let arg_ty = self.subs.real(arg_ty).clone();
                    let actual = self.typecheck(arg, &arg_ty);
                    let actual = self.instantiate_generics(&actual);

                    let level = self.subs.var_id();
                    self.subsumes_expr(expr_check_span(arg), level, &arg_ty, actual, arg);

                    ret_ty.clone()
                }
                None => return Err(TypeError::NotAFunction(func_type.clone())),
            };

            prev_arg_end = arg.span.end;
        }
        Ok(TailCall::Type(func_type))
    }

    fn typecheck_lambda<'i>(
        &mut self,
        mut function_type: ArcType,
        before_args_pos: BytePos,
        args: &mut Vec<Argument<Symbol>>,
        body: &mut SpannedExpr<Symbol>,
    ) -> ArcType {
        self.enter_scope();
        function_type = self.skolemize(&function_type);
        let mut arg_types = Vec::new();

        let body_type = {
            let mut return_type = function_type.clone();
            let mut iter1 = function_arg_iter(self, function_type);

            let mut next_type_arg = iter1.next();

            let make_new_arg = |tc: &mut Self, span: Span<BytePos>, typ: &mut ArcType| {
                let arg = tc.subs.new_var();
                let ret = tc.subs.new_var();
                let f = tc.type_cache.function(Some(arg.clone()), ret.clone());
                if let Err(err) = tc.unify(typ, f) {
                    tc.errors.push(Spanned {
                        span,
                        value: err.into(),
                    });
                }
                *typ = ret;
                arg
            };

            let mut i = 0;

            while i < args.len() || next_type_arg.is_some() {
                let (type_implicit, arg_type) = match next_type_arg.take() {
                    Some((type_implicit, arg_type)) => (type_implicit, Some(arg_type)),
                    None => (ArgType::Explicit, None),
                };

                match type_implicit {
                    ArgType::Implicit => {
                        let arg_type = arg_type.unwrap();
                        let id = match args.get(i).map(|t| t.arg_type) {
                            Some(ArgType::Implicit) => {
                                i += 1;
                                args[i - 1].name.value.name.clone()
                            }
                            _ => {
                                let id = Symbol::from(format!("implicit_arg"));
                                let pos = if i == 0 {
                                    before_args_pos
                                } else {
                                    args.get(i - 1)
                                        .map(|arg| arg.name.span.end)
                                        .unwrap_or(before_args_pos)
                                };
                                args.insert(
                                    i,
                                    Argument::implicit(pos::spanned2(
                                        pos,
                                        pos,
                                        TypedIdent {
                                            typ: arg_type.clone(),
                                            name: id.clone(),
                                        },
                                    )),
                                );
                                i += 1;
                                id
                            }
                        };
                        arg_types.push(arg_type.clone());
                        iter1.tc.implicit_resolver.add_implicits_of_record(
                            &iter1.tc.subs,
                            &id,
                            &arg_type,
                        );
                        iter1.tc.stack_var(id, arg_type.clone());
                    }
                    ArgType::Explicit => match args.get_mut(i) {
                        Some(&mut Argument {
                            arg_type: ArgType::Implicit,
                            name: ref arg,
                        }) => {
                            i += 1;
                            iter1.tc.error(
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
                            let arg_type = arg_type.unwrap_or_else(|| {
                                make_new_arg(iter1.tc, arg.span, &mut iter1.typ)
                            });
                            let arg = &mut arg.value;

                            arg.typ = arg_type;
                            arg_types.push(arg.typ.clone());
                            iter1.tc.stack_var(arg.name.clone(), arg.typ.clone());
                        }
                        None => break,
                    },
                }
                return_type = iter1.typ.clone();
                next_type_arg = iter1.next();
            }

            return_type
        };

        let body_type = self.typecheck(body, &body_type);
        self.exit_scope();
        self.type_cache.function(arg_types, body_type)
    }

    fn typecheck_pattern(
        &mut self,
        pattern: &mut SpannedPattern<Symbol>,
        mut match_type: ArcType,
    ) -> ArcType {
        let span = pattern.span;
        match pattern.value {
            Pattern::As(ref id, ref mut pat) => {
                self.stack_var(id.clone(), match_type.clone());
                self.typecheck_pattern(pat, match_type.clone());
                match_type
            }
            Pattern::Constructor(ref mut id, ref mut args) => {
                match_type = self.new_skolem_scope(&match_type);
                match_type = self.subs.real(&match_type).clone();
                match_type = self.instantiate_generics(&match_type);
                if let Some(new) = self.original_symbols.get(&id.name) {
                    id.name = new.clone();
                }
                // Find the enum constructor and return the types for its arguments
                let ctor_type = self.find_at(span, &id.name);
                id.typ = ctor_type.clone();
                let return_type = match self.typecheck_pattern_rec(args, ctor_type) {
                    Ok(return_type) => return_type,
                    Err(err) => self.error(span, err),
                };
                let return_type = self.instantiate_generics(&return_type);
                self.unify_span(span, &match_type, return_type)
            }
            Pattern::Record {
                typ: ref mut curr_typ,
                types: ref mut associated_types,
                ref mut fields,
                ref implicit_import,
            } => {
                let uninstantiated_match_type = match_type.clone();
                match_type = self.new_skolem_scope(&match_type);
                match_type = self.instantiate_generics(&match_type);
                *curr_typ = match_type.clone();

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

                let mut typ = {
                    // HACK Since there is no way to unify just the name of the 'type field's we
                    // need to take the types from the matched type. This leaves the `types`
                    // list incomplete however since it may miss some fields defined in the
                    // pattern. These are catched later in this function.
                    let x = self.remove_alias(match_type.clone());
                    let types = x.type_field_iter()
                        .filter(|field| {
                            associated_types
                                .iter()
                                .any(|other| other.name.value.name_eq(&field.name))
                        })
                        .cloned()
                        .collect();

                    let fields = fields
                        .iter()
                        .map(|field| Field::new(field.name.value.clone(), self.subs.new_var()))
                        .collect();
                    Type::poly_record(types, fields, self.subs.new_var())
                };
                typ = self.top_skolem_scope(&typ);
                self.unify_span(span, &typ, match_type.clone());

                for field in fields {
                    let name = &field.name.value;
                    // The field should always exist since the type was constructed from the pattern
                    let field_type = typ
                        .row_iter()
                        .find(|f| f.name.name_eq(name))
                        .expect("ICE: Expected field to exist in type")
                        .typ
                        .clone();
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
                    let field_type = typ
                        .type_field_iter()
                        .find(|field| field.name.name_eq(&name));

                    let alias;
                    let alias = match field_type {
                        Some(field_type) => {
                            // This forces refresh_type to remap the name a type was given
                            // in this module to its actual name
                            self.original_symbols
                                .insert(name.clone(), field_type.typ.name.clone());

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
                            alias = Alias::new(name.clone(), self.type_cache.hole());
                            &alias
                        }
                    };

                    self.stack_type(name, &alias);
                }

                if let Some(ref implicit_import) = *implicit_import {
                    self.implicit_resolver.add_implicits_of_record(
                        &self.subs,
                        &implicit_import.value,
                        &uninstantiated_match_type,
                    );
                }

                typ
            }
            Pattern::Tuple {
                ref mut typ,
                ref mut elems,
            } => {
                match_type = self.new_skolem_scope(&match_type);
                let tuple_type = {
                    let subs = &mut self.subs;
                    self.type_cache
                        .tuple(&mut self.symbols, (0..elems.len()).map(|_| subs.new_var()))
                };
                *typ = self.unify_span(span, &tuple_type, match_type);
                for (elem, field) in elems.iter_mut().zip(tuple_type.row_iter()) {
                    self.typecheck_pattern(elem, field.typ.clone());
                }
                tuple_type
            }
            Pattern::Ident(ref mut id) => {
                self.stack_var(id.name.clone(), match_type.clone());
                id.typ = match_type.clone();
                match_type
            }
            Pattern::Literal(ref l) => {
                let typ = l.env_type_of(&self.environment);
                self.unify_span(span, &match_type, typ);
                match_type
            }
            Pattern::Error => self.subs.new_var(),
        }
    }

    fn typecheck_pattern_rec(
        &mut self,
        args: &mut [SpannedPattern<Symbol>],
        typ: ArcType,
    ) -> TcResult<ArcType> {
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

    fn translate_projected_type(&mut self, id: &Symbol) -> TcResult<ArcType> {
        let mut lookup_type: Option<ArcType> = None;
        for component in id.name().module().components() {
            let symbol = self.symbols.symbol(component);
            lookup_type = match lookup_type {
                Some(typ) => Some(self.remove_aliases(typ.clone())
                    .row_iter()
                    .find(|field| field.name.name_eq(&symbol))
                    .map(|field| field.typ.clone())
                    .ok_or_else(|| TypeError::UndefinedField(typ, symbol))?),
                None => Some(self.find(&symbol)?),
            };
        }
        let typ = lookup_type.unwrap();
        let type_symbol = self.symbols.symbol(id.name().name());
        self.remove_aliases(typ.clone())
            .type_field_iter()
            .find(|field| field.name.name_eq(&type_symbol))
            .map(|field| field.typ.clone().into_type())
            .ok_or_else(|| TypeError::UndefinedField(typ, type_symbol))
    }

    fn translate_ast_type(
        &mut self,
        type_cache: &TypeCache<Symbol, ArcType>,
        ast_type: &AstType<Symbol>,
    ) -> ArcType {
        use base::pos::HasSpan;

        match **ast_type {
            Type::Ident(ref id) if id.name().module().as_str() != "" => {
                match self.translate_projected_type(id) {
                    Ok(typ) => typ,
                    Err(err) => self.error(ast_type.span(), err),
                }
            }
            _ => types::translate_type_with(type_cache, ast_type, |typ| {
                self.translate_ast_type(type_cache, typ)
            }),
        }
    }

    fn typecheck_bindings(&mut self, bindings: &mut [ValueBinding<Symbol>]) -> TcResult<()> {
        self.enter_scope();
        self.type_variables.enter_scope();
        let level = self.subs.var_id();

        let is_recursive = bindings.iter().all(|bind| !bind.args.is_empty());
        // When the definitions are allowed to be mutually recursive
        if is_recursive {
            for bind in bindings.iter_mut() {
                self.type_variables.enter_scope();

                match bind.name.value {
                    Pattern::Constructor(ref id, _) | Pattern::Ident(ref id)
                        if id.name.declared_name().starts_with(char::is_uppercase) =>
                    {
                        self.error(
                            bind.name.span,
                            TypeError::Message(format!(
                                "Unexpected type constructor `{}`",
                                id.name
                            )),
                        );
                    }
                    _ => (),
                }
                let typ = {
                    if let Some(ref mut typ) = bind.typ {
                        self.kindcheck(typ);

                        let type_cache = self.type_cache.clone();
                        bind.resolved_type = self.translate_ast_type(&type_cache, typ);
                    }

                    let typ = self.create_unifiable_signature(&bind.resolved_type);
                    if let Some(typ) = typ {
                        bind.resolved_type = typ;
                    }

                    self.new_skolem_scope_signature(&bind.resolved_type)
                };
                self.typecheck_pattern(&mut bind.name, typ);
                if let Expr::Lambda(ref mut lambda) = bind.expr.value {
                    if let Pattern::Ident(ref name) = bind.name.value {
                        lambda.id.name = name.name.clone();
                    }
                }

                self.type_variables.exit_scope();
            }
        }

        let mut types = Vec::new();
        for bind in bindings.iter_mut() {
            self.type_variables.enter_scope();

            // Functions which are declared as `let f x = ...` are allowed to be self
            // recursive
            let mut typ = if bind.args.is_empty() {
                if let Some(ref mut typ) = bind.typ {
                    self.kindcheck(typ);

                    let type_cache = self.type_cache.clone();
                    bind.resolved_type = self.translate_ast_type(&type_cache, typ);
                }

                let typ = self.create_unifiable_signature(&bind.resolved_type);
                if let Some(typ) = typ {
                    bind.resolved_type = typ;
                }

                let typ = self.new_skolem_scope_signature(&bind.resolved_type);
                self.typecheck_lambda(typ, bind.name.span.end, &mut bind.args, &mut bind.expr)
            } else {
                let typ = self.new_skolem_scope_signature(&bind.resolved_type);
                let function_type = self.skolemize(&typ);

                self.typecheck_lambda(
                    function_type,
                    bind.name.span.end,
                    &mut bind.args,
                    &mut bind.expr,
                )
            };

            debug!("let {:?} : {}", bind.name, typ);

            if !is_recursive {
                // Merge the type declaration and the actual type
                debug!("Generalize at {} = {}", level, bind.resolved_type);
                self.generalize_binding(level, bind);
                self.typecheck_pattern(&mut bind.name, bind.resolved_type.clone());
                debug!("Generalized to {}", bind.resolved_type);
                self.finish_pattern(level, &mut bind.name, &bind.resolved_type);
            } else {
                types.push(typ);
            }

            self.type_variables.exit_scope();
        }

        if is_recursive {
            // Once all variables inside the let has been unified we can quantify them
            debug!("Generalize at {}", level);
            for bind in bindings.iter_mut() {
                debug!("Generalize {}", bind.resolved_type);
                self.generalize_binding(level, bind);
                self.finish_pattern(level, &mut bind.name, &bind.resolved_type);
                debug!("Generalized to {}", bind.resolved_type);
            }

            // Update the implicit bindings with the generalized types we just created
            let mut bindings = self.implicit_resolver
                .implicit_bindings
                .last()
                .unwrap()
                .clone();
            for i in 0..bindings.len() {
                let opt = {
                    let bind = bindings.get(i).unwrap();
                    if bind.0.len() == 1 {
                        let typ = self.environment
                            .stack
                            .get(&bind.0[0].name)
                            .unwrap()
                            .typ
                            .clone();
                        Some((bind.0.clone(), typ))
                    } else {
                        None
                    }
                };
                if let Some(new) = opt {
                    bindings = bindings.set(i, new).unwrap();
                }
            }
            *self.implicit_resolver.implicit_bindings.last_mut().unwrap() = bindings;
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
            self.check_undefined_variables(
                bind.alias.value.params(),
                bind.alias.value.unresolved_type(),
            );
        }

        {
            let mut check =
                KindCheck::new(&self.environment, &self.symbols, self.kind_cache.clone());

            // Setup kind variables for all holes and insert the types in the
            // the type expression into the kindcheck environment
            for bind in &mut *bindings {
                // Create the kind for this binding
                // Test a b : 2 -> 1 -> Type
                // and bind the same variables to the arguments of the type binding
                // ('a' and 'b' in the example)
                let mut id_kind = check.type_kind();
                for generic in bind.alias
                    .value
                    .unresolved_type_mut()
                    .params_mut()
                    .iter_mut()
                    .rev()
                {
                    check.instantiate_kinds(&mut generic.kind);
                    id_kind = Kind::function(generic.kind.clone(), id_kind);
                }
                check.add_local(bind.alias.value.name.clone(), id_kind);
            }

            // Kindcheck all the types in the environment
            for bind in &mut *bindings {
                check.set_variables(bind.alias.value.params());

                let typ = bind.alias
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
                let typ = bind.alias.value.unresolved_type_mut();
                check.finalize_type(typ);
                for arg in typ.params_mut() {
                    *arg = check.finalize_generic(arg);
                }
            }
        }

        for bind in &mut *bindings {
            let s = String::from(self.symbols.string(&bind.alias.value.name));
            let new = self.symbols.scoped_symbol(&s);
            self.original_symbols
                .insert(bind.alias.value.name.clone(), new.clone());

            if let Some(meta) = self.implicit_resolver
                .metadata
                .remove(&bind.alias.value.name)
            {
                self.implicit_resolver.metadata.insert(new.clone(), meta);
            }

            // Rename the aliase's name to its global name
            bind.alias.value.name = new;
        }

        let mut resolved_aliases = Vec::new();
        for bind in &mut *bindings {
            let mut alias = types::translate_alias(&bind.alias.value, |typ| {
                let type_cache = self.type_cache.clone();
                self.translate_ast_type(&type_cache, typ)
            });

            // alias.unresolved_type() is a dummy in this context
            self.named_variables.extend(
                alias
                    .params()
                    .iter()
                    .map(|param| (param.id.clone(), alias.unresolved_type().clone())),
            );

            let replacement =
                self.create_unifiable_signature2(alias.unresolved_type().remove_forall());
            if let Some(typ) = replacement {
                *alias.unresolved_type_mut() = Type::forall(alias.params().to_owned(), typ);
            }
            resolved_aliases.push(alias);
        }

        let alias_group = Alias::group(resolved_aliases);
        for (bind, alias) in bindings.iter_mut().zip(alias_group) {
            bind.finalized_alias = Some(alias);
        }

        // Finally insert the declared types into the global scope
        for bind in bindings {
            if self.environment.stack_types.get(&bind.name.value).is_some() {
                self.errors.push(Spanned {
                    span: expr_check_span(expr),
                    // TODO Help to the position of the other field
                    value: TypeError::DuplicateTypeDefinition(bind.name.value.clone()).into(),
                });
            } else {
                self.stack_type(
                    bind.name.value.clone(),
                    &bind.finalized_alias.as_ref().unwrap(),
                );
            }
        }
    }

    fn kindcheck(&mut self, typ: &mut AstType<Symbol>) {
        let result = {
            let mut check =
                KindCheck::new(&self.environment, &self.symbols, self.kind_cache.clone());
            check.kindcheck_type(typ)
        };
        if let Err(err) = result {
            self.errors
                .push(pos::spanned(err.span, TypeError::from(err.value).into()));
        }
    }

    fn check_undefined_variables(&mut self, args: &[Generic<Symbol>], typ: &AstType<Symbol>) {
        use base::pos::HasSpan;
        match **typ {
            Type::Generic(ref id) => if args.iter().all(|arg| arg.id != id.id) {
                self.error(typ.span(), TypeError::UndefinedVariable(id.id.clone()));
            },
            Type::Record(_) => {
                // Inside records variables are bound implicitly to the closest field
                // so variables are allowed to be undefined/implicit
            }
            _ => {
                types::walk_move_type_opt(
                    typ,
                    &mut types::ControlVisitation(|typ: &AstType<_>| {
                        self.check_undefined_variables(args, typ);
                        None
                    }),
                );
            }
        }
    }

    fn finish_pattern(
        &mut self,
        level: u32,
        pattern: &mut SpannedPattern<Symbol>,
        final_type: &ArcType,
    ) {
        match pattern.value {
            Pattern::As(ref mut id, ref mut pat) => {
                self.finish_pattern(level, pat, &final_type);

                self.environment
                    .stack
                    .get_mut(id)
                    .expect("ICE: Variable no inserted")
                    .typ = final_type.clone();
                debug!("{}: {}", self.symbols.string(&id), final_type);
            }
            Pattern::Ident(ref mut id) => {
                id.typ = final_type.clone();
                self.environment
                    .stack
                    .get_mut(&id.name)
                    .expect("ICE: Variable no inserted")
                    .typ = id.typ.clone();
                debug!("{}: {}", self.symbols.string(&id.name), id.typ);
                debug!("{}: {:?}", self.symbols.string(&id.name), id.typ);
            }
            Pattern::Record {
                ref mut typ,
                ref mut fields,
                ..
            } => {
                *typ = final_type.clone();
                debug!("{{ .. }}: {}", final_type);
                self.generalize_type(level, typ);
                let typ = self.top_skolem_scope(typ);
                let typ = self.instantiate_generics(&typ);
                let record_type = self.remove_alias(typ.clone());
                with_pattern_types(fields, &record_type, |field_name, binding, field_type| {
                    let mut field_type = field_type.clone();
                    self.generalize_type(level, &mut field_type);
                    match *binding {
                        Some(ref mut pat) => {
                            self.finish_pattern(level, pat, &field_type);
                        }
                        None => {
                            self.environment
                                .stack
                                .get_mut(field_name)
                                .expect("ICE: Variable no inserted")
                                .typ = field_type.clone();
                            debug!("{}: {}", field_name, field_type);
                        }
                    }
                });
            }
            Pattern::Tuple {
                ref mut typ,
                ref mut elems,
            } => {
                *typ = final_type.clone();

                let typ = self.top_skolem_scope(typ);
                let typ = self.instantiate_generics(&typ);
                for (elem, field) in elems.iter_mut().zip(typ.row_iter()) {
                    let mut field_type = field.typ.clone();
                    self.generalize_type(level, &mut field_type);
                    self.finish_pattern(level, elem, &field_type);
                }
            }
            Pattern::Constructor(ref id, ref mut args) => {
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

    fn generalize_type(&mut self, level: u32, typ: &mut ArcType) {
        debug!("Start generalize {}", typ);
        self.type_variables.enter_scope();

        let mut generalizer = TypeGeneralizer::new(level, self, typ);
        let mut result_type = generalizer.generalize_type(typ);

        generalizer.type_variables.exit_scope();

        if result_type.is_none() && !generalizer.unbound_variables.is_empty() {
            result_type = Some(typ.clone());
        }

        result_type = result_type.map(|typ| {
            let mut params = generalizer
                .unbound_variables
                .into_iter()
                .map(|(_, generic)| generic)
                .collect::<Vec<_>>();
            params.sort_unstable_by(|l, r| l.id.declared_name().cmp(r.id.declared_name()));

            Type::forall(params, typ)
        });
        if let Some(finished) = result_type {
            debug!("End generalize {}", finished);
            *typ = finished;
        }
    }

    fn generalize_type_without_forall(&mut self, level: u32, typ: &mut ArcType) {
        self.type_variables.enter_scope();

        let mut generalizer = TypeGeneralizer::new(level, self, typ);
        let result_type = generalizer.generalize_type(typ);

        generalizer.type_variables.exit_scope();

        if let Some(finished) = result_type {
            *typ = finished;
        }
    }

    fn new_skolem_scope_signature(&mut self, typ: &ArcType) -> ArcType {
        let typ = self.new_skolem_scope(typ);
        // Put all new generic variable names into scope
        if let Type::Forall(ref params, _, Some(ref vars)) = *typ {
            self.type_variables
                .extend(params.iter().zip(vars).map(|(param, var)| {
                    (
                        param.id.clone(),
                        Type::skolem(Skolem {
                            id: var.as_variable().unwrap().id,
                            name: param.id.clone(),
                            kind: param.kind.clone(),
                        }),
                    )
                }));
        }
        typ
    }

    // Replaces `Type::Id` types with the actual `Type::Alias` type it refers to
    // Replaces variant names with the actual symbol they should refer to
    // Instantiates Type::Hole with a fresh type variable to ensure the hole only ever refers to a
    // single type variable.
    //
    // Also inserts a `forall` for any implicitly declared variables.
    fn create_unifiable_signature(&mut self, typ: &ArcType) -> Option<ArcType> {
        self.named_variables.clear();
        self.create_unifiable_signature2(typ)
    }

    fn create_unifiable_signature2(&mut self, typ: &ArcType) -> Option<ArcType> {
        self.type_variables.enter_scope();
        let result_type = self.create_unifiable_signature_(typ);

        let params = self.type_variables
            .exit_scope()
            .map(|(id, var)| {
                let kind = var.kind().into_owned();
                Generic::new(id, kind)
            })
            .collect::<Vec<_>>();

        if params.is_empty() {
            result_type
        } else {
            Some(ArcType::new(Type::Forall(
                params,
                result_type.unwrap_or_else(|| typ.clone()),
                None,
            )))
        }
    }

    fn create_unifiable_signature_(&mut self, typ: &ArcType) -> Option<ArcType> {
        match **typ {
            Type::Ident(ref id) => {
                // Substitute the Id by its alias if possible
                let new_id = self.original_symbols.get(id).unwrap_or(id);
                self.environment
                    .find_type_info(new_id)
                    .map(|alias| alias.clone().into_type())
                    .or_else(|| {
                        if id == new_id {
                            None
                        } else {
                            Some(Type::ident(new_id.clone()))
                        }
                    })
            }
            Type::Variant(ref row) => {
                let replacement = types::visit_type_opt(
                    row,
                    &mut types::ControlVisitation(|typ: &ArcType| {
                        self.create_unifiable_signature_(typ)
                    }),
                );
                let row = replacement.as_ref().unwrap_or(row);
                let iter = || {
                    row.row_iter()
                        .map(|var| self.original_symbols.get(&var.name))
                };
                if iter().any(|opt| opt.is_some()) {
                    // If any of the variants requires a symbol replacement
                    // we create a new type
                    Some(
                        self.type_cache.variant(
                            iter()
                                .zip(row.row_iter())
                                .map(|(new, old)| match new {
                                    Some(new) => Field::new(new.clone(), old.typ.clone()),
                                    None => old.clone(),
                                })
                                .collect(),
                        ),
                    )
                } else {
                    replacement
                        .clone()
                        .map(|row| ArcType::from(Type::Variant(row)))
                }
            }
            Type::Hole => Some(self.subs.new_var()),
            Type::ExtendRow {
                ref types,
                ref fields,
                ref rest,
            } => {
                let new_fields = types::walk_move_types(fields, |field| {
                    self.create_unifiable_signature2(&field.typ)
                        .map(|typ| Field::new(field.name.clone(), typ))
                });
                let new_rest = self.create_unifiable_signature_(rest);
                merge::merge(fields, new_fields, rest, new_rest, |fields, rest| {
                    Type::extend_row(types.clone(), fields, rest)
                })
            }
            Type::Forall(ref params, ref typ, _) => {
                for param in params {
                    self.named_variables.insert(param.id.clone(), typ.clone());
                }
                let result = self.create_unifiable_signature_(typ);
                // Remove any implicit variables inserted inside the forall since
                // they were actually bound at this stage
                for param in params {
                    self.named_variables.remove(&param.id);
                }
                result.map(|typ| Type::forall(params.clone(), typ))
            }
            Type::Generic(ref generic) if self.named_variables.get(&generic.id).is_none() => {
                match self.type_variables.get(&generic.id).cloned() {
                    Some(typ) => match *typ {
                        Type::Variable(_) => None,
                        _ => Some(typ),
                    },
                    None => {
                        let kind = typ.kind().into_owned();
                        let var = self.subs.new_var_fn(|id| {
                            Type::variable(TypeVariable {
                                kind: kind.clone(),
                                id: id,
                            })
                        });
                        self.type_variables.insert(generic.id.clone(), var);
                        None
                    }
                }
            }
            _ => types::walk_move_type_opt(
                typ,
                &mut types::ControlVisitation(|typ: &ArcType| {
                    self.create_unifiable_signature_(typ)
                }),
            ),
        }
    }

    fn subsumes_expr(
        &mut self,
        span: Span<BytePos>,
        level: u32,
        expected: &ArcType,
        actual: ArcType,
        expr: &mut SpannedExpr<Symbol>,
    ) -> ArcType {
        self.subsumes_implicit(span, level, expected, actual, &mut |arg| {
            match expr.value {
                Expr::App { .. } => (),
                _ => {
                    let dummy = Expr::Literal(Literal::Int(0));
                    let func = mem::replace(&mut expr.value, dummy);
                    expr.value = Expr::App {
                        func: Box::new(pos::spanned(expr.span, func)),
                        implicit_args: Vec::new(),
                        args: vec![],
                    }
                }
            }

            match expr.value {
                Expr::App { ref mut args, .. } => args.push(pos::spanned(expr.span, arg)),
                _ => (),
            }
        })
    }

    fn subsumes_implicit(
        &mut self,
        span: Span<BytePos>,
        level: u32,
        expected: &ArcType,
        mut actual: ArcType,
        receiver: &mut FnMut(Expr<Symbol>),
    ) -> ArcType {
        debug!("Subsume expr {} <=> {}", expected, actual);
        // Act as the implicit arguments of `actual` has been supplied (unless `expected` is
        // specified to have implicit arguments)
        loop {
            let temp = self.instantiate_generics(&actual);
            actual = match *temp {
                Type::Function(ArgType::Implicit, ref arg_type, ref r_ret) => {
                    match **self.subs.real(expected) {
                        Type::Variable(_) | Type::Function(ArgType::Implicit, _, _) => break,
                        _ => {
                            let name = self.implicit_resolver.make_implicit_ident(arg_type);

                            receiver(Expr::Ident(TypedIdent {
                                name,
                                typ: arg_type.clone(),
                            }));

                            r_ret.clone()
                        }
                    }
                }
                _ => break,
            };
        }
        self.subsumes(span, level, expected, actual)
    }

    fn subsumes(
        &mut self,
        span: Span<BytePos>,
        level: u32,
        expected: &ArcType,
        mut actual: ArcType,
    ) -> ArcType {
        debug!("Merge {} : {}", expected, actual);
        let expected = self.skolemize(&expected);
        let state = unify_type::State::new(&self.environment, &self.subs);
        match unify_type::subsumes(
            &self.subs,
            &mut self.type_variables,
            level,
            state,
            &expected,
            &actual,
        ) {
            Ok(typ) => self.subs.set_type(typ),
            Err(errors) => {
                let mut expected = expected.clone();
                expected = self.subs.set_type(expected);
                actual = self.subs.set_type(actual);
                debug!(
                    "Error '{:?}' between:\n>> {}\n>> {}",
                    errors, expected, actual
                );
                let err = TypeError::Unification(expected, actual, apply_subs(&self.subs, errors));
                self.errors.push(Spanned {
                    span: span,
                    // TODO Help what caused this unification failure
                    value: err.into(),
                });
                self.subs.new_var()
            }
        }
    }

    fn unify_span(&mut self, span: Span<BytePos>, expected: &ArcType, actual: ArcType) -> ArcType {
        match self.unify(expected, actual) {
            Ok(typ) => typ,
            Err(err) => {
                self.errors.push(Spanned {
                    span: span,
                    // TODO Help what caused this unification failure
                    value: err.into(),
                });
                self.subs.new_var()
            }
        }
    }

    fn unify(&self, expected: &ArcType, mut actual: ArcType) -> TcResult<ArcType> {
        debug!("Unify start {} <=> {}", expected, actual);
        let state = unify_type::State::new(&self.environment, &self.subs);
        match unify::unify(&self.subs, state, expected, &actual) {
            Ok(typ) => Ok(self.subs.set_type(typ)),
            Err(errors) => {
                let mut expected = expected.clone();
                expected = self.subs.set_type(expected);
                actual = self.subs.set_type(actual);
                debug!(
                    "Error '{:?}' between:\n>> {}\n>> {}",
                    errors, expected, actual
                );
                Err(TypeError::Unification(
                    expected,
                    actual,
                    apply_subs(&self.subs, errors),
                ))
            }
        }
    }

    fn remove_alias(&self, typ: ArcType) -> ArcType {
        resolve::remove_alias(&self.environment, &typ)
            .unwrap_or(None)
            .unwrap_or(typ)
    }

    fn remove_aliases(&self, typ: ArcType) -> ArcType {
        resolve::remove_aliases(&self.environment, typ)
    }

    fn skolemize(&mut self, typ: &ArcType) -> ArcType {
        self.named_variables.clear();
        self.named_variables.extend(
            self.type_variables
                .iter()
                .map(|(k, v)| (k.clone(), v.clone())),
        );
        typ.skolemize(&mut self.named_variables)
    }

    pub(crate) fn instantiate_generics(&mut self, typ: &ArcType) -> ArcType {
        self.named_variables.clear();
        typ.instantiate_generics(&mut self.named_variables)
    }

    pub(crate) fn new_skolem_scope(&mut self, typ: &ArcType) -> ArcType {
        new_skolem_scope(&self.subs, typ)
    }

    fn top_skolem_scope(&mut self, typ: &ArcType) -> ArcType {
        ::unify_type::top_skolem_scope(&self.subs, typ)
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
}

fn with_pattern_types<F>(
    fields: &mut [PatternField<Symbol, SpannedPattern<Symbol>>],
    typ: &ArcType,
    mut f: F,
) where
    F: FnMut(&Symbol, &mut Option<SpannedPattern<Symbol>>, &ArcType),
{
    for field in fields {
        // If the field in the pattern does not exist (undefined field error) then skip it as
        // the error itself will already have been reported
        let opt = typ.row_iter()
            .find(|type_field| type_field.name.name_eq(&field.name.value));
        if let Some(associated_type) = opt {
            f(&field.name.value, &mut field.value, &associated_type.typ);
        }
    }
}

fn apply_subs(
    subs: &Substitution<ArcType>,
    errors: Errors<UnifyTypeError<Symbol>>,
) -> Vec<UnifyTypeError<Symbol>> {
    use unify::Error::*;
    errors
        .into_iter()
        .map(|error| match error {
            TypeMismatch(expected, actual) => {
                TypeMismatch(subs.set_type(expected), subs.set_type(actual))
            }
            Substitution(err) => Substitution(match err {
                substitution::Error::Occurs(var, typ) => {
                    substitution::Error::Occurs(var, subs.set_type(typ))
                }
            }),
            Other(err) => Other(err),
        })
        .collect()
}

pub fn extract_generics(args: &[ArcType]) -> Vec<Generic<Symbol>> {
    args.iter()
        .map(|arg| match **arg {
            Type::Generic(ref gen) => gen.clone(),
            _ => ice!("The type on the lhs of a type binding did not have all generic arguments"),
        })
        .collect()
}

fn get_alias_app<'a>(
    env: &'a TypeEnv,
    typ: &'a ArcType,
) -> Option<(&'a AliasRef<Symbol, ArcType>, Cow<'a, [ArcType]>)> {
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
    typ: ArcType,
}

impl<'a, 'b> Iterator for FunctionArgIter<'a, 'b> {
    type Item = (ArgType, ArcType);
    fn next(&mut self) -> Option<Self::Item> {
        let mut last_alias = None;
        loop {
            if let Type::Forall(_, _, None) = *self.typ {
                panic!("Found forall without scope in function argument iterator")
            }
            self.typ = self.tc.skolemize(&self.typ);
            let (arg, new) = match self.typ.as_function_with_type() {
                Some((arg_type, arg, ret)) => (Some((arg_type, arg.clone())), ret.clone()),
                None => match get_alias_app(&self.tc.environment, &self.typ) {
                    Some((alias, args)) => {
                        if Some(&alias.name) == last_alias.as_ref() {
                            return None;
                        }
                        last_alias = Some(alias.name.clone());
                        match alias.typ().apply_args(&args) {
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

fn function_arg_iter<'a, 'b>(tc: &'a mut Typecheck<'b>, typ: ArcType) -> FunctionArgIter<'a, 'b> {
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

/// Removes layers of `Type::App` and `Type::Record` by packing them into a single `Type::App` or
/// `Type::Record`
///
/// Example:
///
/// ```rust
/// #[macro_use]
/// extern crate collect_mac;
/// extern crate gluon_base;
/// extern crate gluon_check;
///
/// use gluon_base::types::{Type, ArcType, BuiltinType};
/// use gluon_check::typecheck::unroll_typ;
///
/// # fn main() {
/// let i: ArcType = Type::int();
/// let s: ArcType = Type::string();
/// assert_eq!(unroll_typ(&Type::app(Type::app(i.clone(), collect![s.clone()]), collect![i.clone()])),
///            Some(Type::app(i.clone(), collect![s.clone(), i.clone()])));
/// assert_eq!(unroll_typ(&Type::app(Type::app(i.clone(), collect![i.clone()]), collect![s.clone()])),
///            Some(Type::app(i.clone(), collect![i.clone(), s.clone()])));
/// let f: ArcType = Type::builtin(BuiltinType::Function);
/// assert_eq!(unroll_typ(&Type::app(Type::app(f.clone(), collect![i.clone()]), collect![s.clone()])),
///            Some(Type::function(collect![i.clone()], s.clone())));
/// # }
/// ```
pub fn unroll_typ(typ: &ArcType) -> Option<ArcType> {
    let mut args = AppVec::new();
    let mut current = match **typ {
        Type::App(ref l, ref rest) => {
            // No need to unroll if `l` is not an application as that will just result in returning
            // an application that is identical to `typ`
            match **l {
                Type::App(..) => (),
                _ => return None,
            }
            args.extend(rest.iter().rev().cloned());
            l
        }
        _ => return unroll_record(typ),
    };
    while let Type::App(ref l, ref rest) = **current {
        args.extend(rest.iter().rev().cloned());
        current = l;
    }
    if args.is_empty() {
        None
    } else {
        args.reverse();
        match **current {
            Type::Builtin(BuiltinType::Function) if args.len() == 2 => {
                let ret = args.pop().unwrap();
                Some(Type::function(args.into_iter().collect(), ret))
            }
            _ => Some(Type::app(current.clone(), args)),
        }
    }
}

fn unroll_record(typ: &Type<Symbol>) -> Option<ArcType> {
    let mut new_types = Vec::new();
    let mut new_fields = Vec::new();
    let mut current = match *typ {
        Type::ExtendRow {
            ref types,
            ref fields,
            ref rest,
        } => match **rest {
            Type::ExtendRow { .. } => {
                new_types.extend_from_slice(types);
                new_fields.extend_from_slice(fields);
                rest
            }
            _ => return None,
        },
        _ => return None,
    };
    while let Type::ExtendRow {
        ref types,
        ref fields,
        ref rest,
    } = **current
    {
        new_types.extend_from_slice(types);
        new_fields.extend_from_slice(fields);
        current = rest;
    }
    if new_types.is_empty() && new_fields.is_empty() {
        None
    } else {
        Some(Type::extend_row(new_types, new_fields, current.clone()))
    }
}

struct TypeGeneralizer<'a, 'b: 'a> {
    level: u32,
    unbound_variables: FnvMap<Symbol, Generic<Symbol>>,
    variable_generator: TypeVariableGenerator,
    tc: &'a mut Typecheck<'b>,
}

impl<'a, 'b> ::std::ops::Deref for TypeGeneralizer<'a, 'b> {
    type Target = Typecheck<'b>;
    fn deref(&self) -> &Typecheck<'b> {
        self.tc
    }
}

impl<'a, 'b> ::std::ops::DerefMut for TypeGeneralizer<'a, 'b> {
    fn deref_mut(&mut self) -> &mut Typecheck<'b> {
        self.tc
    }
}

impl<'a, 'b> TypeGeneralizer<'a, 'b> {
    fn new(level: u32, tc: &'a mut Typecheck<'b>, typ: &ArcType) -> TypeGeneralizer<'a, 'b> {
        TypeGeneralizer {
            level,
            unbound_variables: FnvMap::default(),
            variable_generator: TypeVariableGenerator::new(level, &tc.subs, typ),
            tc,
        }
    }

    fn generalize_type(&mut self, typ: &ArcType) -> Option<ArcType> {
        let replacement = self.subs
            .replace_variable(typ)
            .map(|t| self.generalize_type(&t).unwrap_or(t));
        let mut typ = typ;
        if let Some(ref t) = replacement {
            typ = t;
        }
        match **typ {
            Type::Variable(ref var) if self.subs.get_level(var.id) >= self.level => {
                // Create a prefix if none exists
                let id = self.variable_generator.next_variable(self.tc);

                let gen: ArcType = Type::generic(Generic::new(id.clone(), var.kind.clone()));
                debug!("Gen {} to {}", var.id, gen);
                self.subs.insert(var.id, gen.clone());

                self.unbound_variables
                    .insert(id.clone(), Generic::new(id, var.kind.clone()));

                Some(gen)
            }
            Type::ExtendRow {
                ref types,
                ref fields,
                ref rest,
            } => {
                let new_fields = types::walk_move_types(fields, |field| {
                    // Make a new name base for any unbound variables in the record field
                    // Gives { id : a0 -> a0, const : b0 -> b1 -> b1 }
                    // instead of { id : a0 -> a0, const : a1 -> a2 -> a2 }
                    self.generalize_type(&field.typ)
                        .map(|typ| Field::new(field.name.clone(), typ))
                });
                let new_rest = self.generalize_type(rest);
                merge::merge(fields, new_fields, rest, new_rest, |fields, rest| {
                    Type::extend_row(types.clone(), fields, rest)
                }).or_else(|| replacement.clone())
            }

            Type::Forall(ref params, ref typ, Some(ref vars)) => {
                use substitution::is_variable_unified;
                trace!("Generalize `{}` {:?}", typ, vars);
                let typ = {
                    let subs = &self.tc.subs;
                    self.tc.named_variables.clear();
                    self.tc.named_variables.extend(
                        params
                            .iter()
                            .zip(vars)
                            .filter(|&(_, var)| is_variable_unified(subs, var))
                            .map(|(param, var)| (param.id.clone(), var.clone())),
                    );;
                    typ.instantiate_generics_(&mut self.tc.named_variables)
                        .unwrap_or(typ.clone())
                };

                self.type_variables.enter_scope();
                self.type_variables.extend(
                    params
                        .iter()
                        .zip(vars)
                        .map(|(param, var)| (param.id.clone(), var.clone())),
                );

                trace!("Generalize forall `{}`", typ);

                let new_type = self.generalize_type(&typ);
                self.type_variables.exit_scope();

                Some(Type::forall(
                    params
                        .iter()
                        .zip(vars)
                        .filter(|&(_, var)| !is_variable_unified(&self.subs, var))
                        .map(|(param, _)| param.clone())
                        .collect(),
                    new_type.unwrap_or_else(|| typ.clone()),
                ))
            }

            Type::Skolem(ref skolem) if skolem.id >= self.level => {
                let generic = Generic {
                    id: skolem.name.clone(),
                    kind: skolem.kind.clone(),
                };

                if self.type_variables.get(&generic.id).is_none() {
                    self.unbound_variables
                        .insert(generic.id.clone(), generic.clone());
                }

                Some(Type::generic(generic))
            }

            _ => {
                if let Type::Forall(ref params, _, None) = **typ {
                    self.type_variables
                        .extend(params.iter().map(|param| (param.id.clone(), typ.clone())));
                }

                let new_type = types::walk_move_type_opt(
                    typ,
                    &mut types::ControlVisitation(|typ: &ArcType| self.generalize_type(typ)),
                );
                match **typ {
                    Type::Generic(ref generic)
                        if self.type_variables.get(&generic.id).is_none() =>
                    {
                        self.unbound_variables
                            .insert(generic.id.clone(), generic.clone());
                    }
                    _ => (),
                }
                new_type
                    .map(|t| unroll_typ(&t).unwrap_or(t))
                    .or_else(|| replacement.clone())
            }
        }
    }
}

struct TypeVariableGenerator {
    map: FnvSet<Symbol>,
    level: u32,
    name: String,
    i: u32,
}

impl TypeVariableGenerator {
    fn new(level: u32, subs: &Substitution<ArcType>, typ: &ArcType) -> TypeVariableGenerator {
        fn gather_foralls(map: &mut FnvSet<Symbol>, subs: &Substitution<ArcType>, typ: &ArcType) {
            let typ = subs.real(typ);
            if let Type::Forall(ref params, _, _) = **typ {
                map.extend(params.iter().map(|param| param.id.clone()));
            }
            types::walk_move_type_opt(
                typ,
                &mut types::ControlVisitation(|typ: &ArcType| {
                    gather_foralls(map, subs, typ);
                    None
                }),
            );
        }
        let mut map = FnvSet::default();
        gather_foralls(&mut map, subs, typ);
        TypeVariableGenerator {
            map,
            name: "".to_string(),
            i: 0,
            level,
        }
    }
    /// Generate a generic variable name which is not used in the current scope
    fn next_variable(&mut self, tc: &mut Typecheck) -> Symbol {
        let symbol = if self.name.is_empty() {
            self.next_variable_(tc)
        } else {
            let name = format!("{}{}", self.name, self.i);
            self.i += 1;
            tc.symbols.symbol(&name[..])
        };
        self.map.insert(symbol.clone());
        tc.type_variables.insert(
            symbol.clone(),
            Type::variable(TypeVariable {
                id: self.level,
                kind: tc.kind_cache.typ(),
            }),
        );
        symbol
    }

    fn next_variable_(&mut self, tc: &mut Typecheck) -> Symbol {
        for c in b'a'..(b'z' + 1) {
            self.name.push(c as char);
            let symbol = tc.symbols.symbol(&self.name[..]);
            if !self.map.contains(&symbol) && tc.type_variables.get(&symbol).is_none() {
                return symbol;
            }
            self.name.pop();
        }
        self.name.push('a');
        self.next_variable_(tc)
    }
}
