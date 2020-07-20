use std::{fmt, result::Result as StdResult};

use crate::base::{
    ast::{self, AstType},
    error::Errors,
    kind::{self, ArcKind, Kind, KindCache},
    merge,
    pos::{self, BytePos, HasSpan, Span, Spanned},
    scoped_map::{Entry, ScopedMap},
    symbol::Symbol,
    types::{self, BuiltinType, Generic, NullInterner, Type, TypeEnv, Walker},
};

use crate::{
    substitution::{Substitutable, Substitution},
    typ::RcType,
    unify::{self, Error as UnifyError, Unifiable, Unifier, UnifierState},
};

pub type Error<I, T = RcType<I>> = UnifyError<KindError<I, T>, ArcKind>;
pub type SpannedError<I, T> = Spanned<Error<I, T>, BytePos>;

pub type Result<T> = StdResult<T, SpannedError<Symbol, RcType<Symbol>>>;

/// Struct containing methods for kindchecking types
pub struct KindCheck<'a> {
    variables: ScopedMap<Symbol, ArcKind>,
    errors: Errors<SpannedError<Symbol, RcType<Symbol>>>,
    info: &'a (dyn TypeEnv<Type = RcType> + 'a),
    idents: &'a mut (dyn ast::IdentEnv<Ident = Symbol> + 'a),
    subs: Substitution<ArcKind>,
    kind_cache: KindCache,
    /// A cached one argument kind function, `Type -> Type`
    function1_kind: ArcKind,
    /// A cached two argument kind function, `Type -> Type -> Type`
    function2_kind: ArcKind,
    /// A cached effect field kind, `Row -> Type -> Type`
    effect_field_kind: ArcKind,
}

fn walk_move_kind<F>(kind: ArcKind, f: &mut F) -> ArcKind
where
    F: FnMut(&Kind) -> Option<ArcKind>,
{
    match walk_move_kind2(&kind, f) {
        Some(kind) => kind,
        None => kind,
    }
}
fn walk_move_kind2<F>(kind: &ArcKind, f: &mut F) -> Option<ArcKind>
where
    F: FnMut(&Kind) -> Option<ArcKind>,
{
    let new = f(kind);
    let new2 = {
        let kind = new.as_ref().unwrap_or(kind);
        match **kind {
            Kind::Function(ref arg, ref ret) => {
                let arg_new = walk_move_kind2(arg, f);
                let ret_new = walk_move_kind2(ret, f);
                merge::merge(arg, arg_new, ret, ret_new, Kind::function)
            }
            Kind::Hole | Kind::Error | Kind::Type | Kind::Variable(_) | Kind::Row => None,
        }
    };
    new2.or(new)
}

impl<'a> KindCheck<'a> {
    pub fn new(
        info: &'a (dyn TypeEnv<Type = RcType> + 'a),
        idents: &'a mut (dyn ast::IdentEnv<Ident = Symbol> + 'a),
        kind_cache: KindCache,
    ) -> KindCheck<'a> {
        let typ = kind_cache.typ();
        let function1_kind = Kind::function(typ.clone(), typ.clone());
        KindCheck {
            variables: Default::default(),
            info: info,
            idents: idents,
            subs: Substitution::new((), Default::default()),
            function1_kind: function1_kind.clone(),
            function2_kind: Kind::function(typ, function1_kind.clone()),
            effect_field_kind: Kind::function(kind_cache.row(), function1_kind),
            kind_cache,
            errors: Errors::new(),
        }
    }

    pub fn add_local(&mut self, name: Symbol, kind: ArcKind) {
        self.variables.insert(name, kind);
    }

    pub fn enter_scope_with(&mut self, variables: impl IntoIterator<Item = (Symbol, ArcKind)>) {
        self.variables.enter_scope();
        self.variables.extend(variables);
    }

    pub fn exit_scope(&mut self) {
        self.variables.exit_scope();
    }

    pub fn type_kind(&self) -> ArcKind {
        self.kind_cache.typ()
    }

    pub fn function1_kind(&self) -> ArcKind {
        self.function1_kind.clone()
    }

    pub fn effect_field_kind(&self) -> ArcKind {
        self.effect_field_kind.clone()
    }

    pub fn function2_kind(&self) -> ArcKind {
        self.function2_kind.clone()
    }

    pub fn row_kind(&self) -> ArcKind {
        self.kind_cache.row()
    }

    pub fn instantiate_kinds(&mut self, kind: &mut ArcKind) {
        match *ArcKind::make_mut(kind) {
            // Can't assign a new var to `kind` here because it is borrowed mutably...
            // We'll rely on fall-through instead.
            Kind::Hole => (),
            Kind::Variable(_) => ice!("Unexpected kind variable while instantiating"),
            Kind::Function(ref mut lhs, ref mut rhs) => {
                self.instantiate_kinds(lhs);
                self.instantiate_kinds(rhs);
                return;
            }
            Kind::Row | Kind::Error | Kind::Type => return,
        }
        *kind = self.subs.new_var();
    }

    fn find_at(&mut self, span: Span<BytePos>, id: &Symbol) -> ArcKind {
        self.find(span, id).unwrap_or_else(|err| {
            self.errors.push(err);
            self.kind_cache.error()
        })
    }
    fn find(&mut self, span: Span<BytePos>, id: &Symbol) -> Result<ArcKind> {
        let kind = match self.variables.entry(id.clone()) {
            Entry::Occupied(entry) => entry.get().clone(),
            Entry::Vacant(entry) => {
                let kind = match self.info.find_kind(id) {
                    Some(k) => k.clone(),
                    None => {
                        if self.idents.string(id).starts_with(char::is_uppercase) {
                            return Err(pos::spanned(
                                span,
                                UnifyError::Other(KindError::UndefinedType(id.clone())),
                            ));
                        } else {
                            self.subs.new_var()
                        }
                    }
                };
                entry.insert(kind.clone());
                kind
            }
        };

        debug!("Find kind: {} => {}", self.idents.string(&id), kind);

        Ok(match *kind {
            Kind::Hole => self.subs.new_var(),
            _ => kind,
        })
    }

    fn find_projection(&mut self, ids: &[Symbol]) -> Option<ArcKind> {
        // Errors get reported in typecheck as well so ignore them here
        crate::typecheck::translate_projected_type(self.info, self.idents, &mut NullInterner, ids)
            .ok()
            .map(|typ| typ.kind(&self.kind_cache).into_owned())
    }

    // Kindhecks `typ`, infering it to be of kind `Type`
    pub fn kindcheck_type(
        &mut self,
        typ: &mut AstType<Symbol>,
    ) -> StdResult<ArcKind, Errors<SpannedError<Symbol, RcType<Symbol>>>> {
        let any = self.subs.new_var();
        self.kindcheck_expected(typ, &any)
    }

    pub fn kindcheck_expected(
        &mut self,
        typ: &mut AstType<Symbol>,
        expected: &ArcKind,
    ) -> StdResult<ArcKind, Errors<SpannedError<Symbol, RcType<Symbol>>>> {
        info!("Kindchecking {}", typ);
        let kind = self.kindcheck(typ);
        let kind = self.unify(typ.span(), expected, kind);
        self.finalize_type(typ);

        if self.errors.has_errors() {
            return Err(std::mem::take(&mut self.errors));
        }
        trace!("Kindchecked {:#?}", typ);
        Ok(kind)
    }

    fn builtin_kind(&self, typ: BuiltinType) -> ArcKind {
        match typ {
            BuiltinType::String
            | BuiltinType::Byte
            | BuiltinType::Char
            | BuiltinType::Int
            | BuiltinType::Float => self.type_kind(),
            BuiltinType::Array => self.function1_kind(),
            BuiltinType::Function => self.function2_kind(),
        }
    }

    fn scope<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.variables.enter_scope();
        let r = f(self);
        self.variables.exit_scope();
        r
    }

    fn kindcheck(&mut self, typ: &mut AstType<Symbol>) -> ArcKind {
        let span = typ.span();
        match **typ {
            Type::Error => self.kind_cache.error(),

            Type::Hole | Type::Opaque | Type::Variable(_) => self.subs.new_var(),

            Type::Skolem(ref mut skolem) => {
                skolem.kind = self.find_at(span, &skolem.name);
                skolem.kind.clone()
            }

            Type::Generic(ref mut gen) => {
                gen.kind = self.find_at(span, &gen.id);
                gen.kind.clone()
            }

            Type::Builtin(builtin_typ) => self.builtin_kind(builtin_typ),

            Type::Forall(ref mut params, ref mut typ) => self.scope(|self_| {
                for param in &mut **params {
                    param.kind = self_.subs.new_var();
                    self_.variables.insert(param.id.clone(), param.kind.clone());
                }
                self_.kindcheck(typ)
            }),

            Type::Function(_, ref mut arg, ref mut ret) => {
                let arg_kind = self.kindcheck(arg);
                let ret_kind = self.kindcheck(ret);

                let type_kind = self.type_kind();
                self.unify(span, &type_kind, arg_kind);
                self.unify(span, &type_kind, ret_kind);

                type_kind
            }

            Type::App(ref mut ctor, ref mut args) => {
                let mut kind = self.kindcheck(ctor);

                let mut prev_span = ctor.span();

                for arg in &mut **args {
                    let (arg_kind, ret) = self.unify_function(prev_span, kind);

                    let actual = self.kindcheck(arg);
                    self.unify(arg.span(), &arg_kind, actual);

                    kind = ret;
                    prev_span = arg.span();
                }
                kind
            }

            Type::Variant(ref mut row) => {
                match **row {
                    Type::ExtendRow { .. } => {
                        let mut fields = types::row_iter_mut(row);
                        for field in &mut fields {
                            let kind = self.kindcheck(&mut field.typ);
                            let type_kind = self.type_kind();
                            self.unify(field.typ.span(), &type_kind, kind);
                        }

                        let rest_kind = self.kindcheck(fields.current_type());
                        let row_kind = self.row_kind();
                        self.unify(span, &row_kind, rest_kind);
                    }
                    _ => {
                        let rest_kind = self.kindcheck(row);
                        let row_kind = self.row_kind();
                        self.unify(span, &row_kind, rest_kind);
                    }
                }

                self.type_kind()
            }

            Type::Record(ref mut row) => {
                let kind = self.kindcheck(row);
                let row_kind = self.row_kind();
                self.unify(span, &row_kind, kind);
                self.type_kind()
            }

            Type::Effect(ref mut row) => {
                let mut iter = types::row_iter_mut(row);
                for field in &mut iter {
                    let kind = self.kindcheck(&mut field.typ);
                    let effect_field_kind = self.effect_field_kind();
                    self.unify(field.typ.span(), &effect_field_kind, kind);
                }
                let kind = self.kindcheck(iter.current_type());
                let row_kind = self.row_kind();
                self.unify(span, &row_kind, kind);
                self.function1_kind()
            }

            Type::ExtendRow {
                ref mut fields,
                ref mut rest,
            } => {
                for field in &mut **fields {
                    let kind = self.kindcheck(&mut field.typ);
                    let type_kind = self.type_kind();
                    self.unify(field.typ.span(), &type_kind, kind);
                }

                let kind = self.kindcheck(rest);
                let row_kind = self.row_kind();
                self.unify(rest.span(), &row_kind, kind);

                row_kind
            }

            Type::ExtendTypeRow {
                ref mut types,
                ref mut rest,
            } => {
                for field in &mut **types {
                    if let Some(alias) = field.typ.try_get_alias_mut() {
                        self.scope(|self_| {
                            for param in alias.params_mut() {
                                param.kind = self_.subs.new_var();
                                self_.variables.insert(param.id.clone(), param.kind.clone());
                            }

                            let field_type = alias.unresolved_type_mut();
                            let kind = self_.kindcheck(field_type);
                            let type_kind = self_.type_kind();

                            self_.unify(field_type.span(), &type_kind, kind)
                        });
                    }
                }

                let kind = self.kindcheck(rest);
                let row_kind = self.row_kind();
                self.unify(rest.span(), &row_kind, kind);

                row_kind
            }

            Type::EmptyRow => self.row_kind(),

            Type::Ident(ref mut id) => {
                id.typ = self.find_at(span, &id.name);
                id.typ.clone()
            }

            Type::Projection(ref ids) => self
                .find_projection(ids)
                .unwrap_or_else(|| self.subs.new_var()),

            Type::Alias(ref alias) => self.find_at(span, &alias.name),
        }
    }

    fn unify_function(&mut self, span: Span<BytePos>, actual: ArcKind) -> (ArcKind, ArcKind) {
        if let Kind::Function(arg, ret) = &**self.subs.real(&actual) {
            return (arg.clone(), ret.clone());
        }

        let arg = self.subs.new_var();
        let ret = self.subs.new_var();
        let f = Kind::function(arg.clone(), ret.clone());

        self.unify(span, &f, actual);

        (arg, ret)
    }

    fn unify(&mut self, span: Span<BytePos>, expected: &ArcKind, mut actual: ArcKind) -> ArcKind {
        debug!("Unify {:?} <=> {:?}", expected, actual);
        let result = unify::unify(&self.subs, &self.kind_cache, expected, &actual);
        match result {
            Ok(k) => k,
            Err(_errors) => {
                let mut expected = expected.clone();
                expected = update_kind(&self.subs, expected, None);
                actual = update_kind(&self.subs, actual, None);
                let err = pos::spanned(span, UnifyError::TypeMismatch(expected, actual));
                debug!("Kind unify error: {}", err);
                self.errors.push(err);
                self.kind_cache.error()
            }
        }
    }

    pub fn finalize_type(&mut self, typ: &mut AstType<Symbol>) {
        self.finalize_type_(typ);
        types::walk_type_mut(typ, &mut |typ: &mut AstType<Symbol>| {
            self.finalize_type_(typ);
        });
    }
    fn finalize_type_(&mut self, typ: &mut AstType<Symbol>) {
        match &mut **typ {
            Type::ExtendTypeRow { types, .. } => types.iter_mut().for_each(|field| {
                if let Some(alias) = field.typ.try_get_alias_mut() {
                    alias
                        .params_mut()
                        .iter_mut()
                        .for_each(|var| *var = self.finalize_generic(var))
                }
            }),
            Type::Variable(var) => {
                let default = Some(&self.kind_cache.typ);
                var.kind = update_kind(&self.subs, var.kind.clone(), default);
            }
            Type::Generic(var) => *var = self.finalize_generic(var),
            Type::Alias(alias) => alias
                .try_get_alias_mut()
                .expect("ICE: AstType did not provide mutable alias")
                .params_mut()
                .iter_mut()
                .for_each(|var| *var = self.finalize_generic(var)),
            Type::Forall(params, _) => {
                for param in &mut **params {
                    *param = self.finalize_generic(&param);
                }
            }
            Type::Ident(id) => {
                id.typ = update_kind(&self.subs, id.typ.clone(), Some(&self.kind_cache.typ));
            }
            _ => (),
        }
    }
    pub fn finalize_generic(&self, var: &Generic<Symbol>) -> Generic<Symbol> {
        let mut kind = var.kind.clone();
        kind = update_kind(&self.subs, kind, Some(&self.kind_cache.typ));
        Generic::new(var.id.clone(), kind)
    }
}

fn update_kind(subs: &Substitution<ArcKind>, kind: ArcKind, default: Option<&ArcKind>) -> ArcKind {
    walk_move_kind(kind, &mut |kind| match *kind {
        Kind::Variable(id) => subs
            .find_type_for_var(id)
            .map(|kind| update_kind(subs, kind.clone(), default))
            .or_else(|| default.cloned()),
        _ => None,
    })
}

/// Enumeration possible errors other than mismatch and occurs when kindchecking
#[derive(Debug, Eq, PartialEq, Hash, Clone, Functor)]
pub enum KindError<I, T> {
    /// The type is not defined in the current scope
    UndefinedType(I),
    UndefinedField(T, I),
}

impl<I, T> fmt::Display for KindError<I, T>
where
    I: fmt::Display + AsRef<str>,
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            KindError::UndefinedType(ref name) => write!(f, "Type '{}' is not defined", name),
            KindError::UndefinedField(ref typ, ref name) => {
                write!(f, "Type '{}' does not have the field '{}'", typ, name)
            }
        }
    }
}

pub fn fmt_kind_error<I, T>(error: &Error<I, T>, f: &mut fmt::Formatter) -> fmt::Result
where
    I: fmt::Display + AsRef<str>,
    T: fmt::Display,
{
    use crate::unify::Error::*;
    match *error {
        TypeMismatch(ref expected, ref actual) => write!(
            f,
            "Kind mismatch\nExpected: {}\nFound: {}",
            expected, actual
        ),
        Substitution(ref err) => write!(f, "{}", err),
        Other(ref err) => write!(f, "{}", err),
    }
}

impl Substitutable for ArcKind {
    type Variable = u32;

    type Factory = ();

    type Interner = NullInterner;

    fn from_variable(_: &Substitution<Self>, x: u32) -> ArcKind {
        Kind::variable(x)
    }

    fn into_variable(&mut self, x: Self::Variable) {
        *ArcKind::make_mut(self) = Kind::Variable(x);
    }

    fn is_unique(self_: &Self) -> bool {
        ArcKind::strong_count(self_) == 1
    }

    fn get_var(&self) -> Option<&u32> {
        match **self {
            Kind::Variable(ref var) => Some(var),
            _ => None,
        }
    }

    fn traverse<'a, F>(&'a self, f: &mut F)
    where
        F: Walker<'a, ArcKind>,
    {
        kind::walk_kind(self, f);
    }
    fn instantiate(&self, _subs: &Substitution<Self>) -> Self {
        self.clone()
    }
}

impl<'a> Unifiable<&'a KindCache> for ArcKind {
    type Error = KindError<Symbol, RcType>;

    fn zip_match<U>(
        &self,
        other: &Self,
        unifier: &mut UnifierState<&'a KindCache, U>,
    ) -> StdResult<Option<Self>, Error<Symbol, RcType>>
    where
        UnifierState<&'a KindCache, U>: Unifier<&'a KindCache, Self>,
    {
        match (&**self, &**other) {
            (_, &Kind::Error) => Ok(None),
            (&Kind::Error, _) => Ok(Some(other.clone())),
            (&Kind::Function(ref l1, ref l2), &Kind::Function(ref r1, ref r2)) => {
                let a = unifier.try_match(l1, r1);
                let r = unifier.try_match(l2, r2);
                Ok(merge::merge(l1, a, l2, r, Kind::function))
            }
            (l, r) => {
                if l == r {
                    Ok(None)
                } else {
                    Err(UnifyError::TypeMismatch(self.clone(), other.clone()))
                }
            }
        }
    }

    fn error_type(state: &&'a KindCache) -> Self {
        state.error()
    }
}
