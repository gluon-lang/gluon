use std::fmt;

use base::ast;
use base::kind::{self, ArcKind, Kind, KindEnv};
use base::symbol::Symbol;
use base::types::{self, ArcType, BuiltinType, Field, Generic, Type, Walker};

use substitution::{Substitution, Substitutable};
use unify;

use unify::Error as UnifyError;

pub type Error<I> = UnifyError<ArcKind, KindError<I>>;

pub type Result<T> = ::std::result::Result<T, Error<Symbol>>;


/// Struct containing methods for kindchecking types
pub struct KindCheck<'a> {
    variables: Vec<Generic<Symbol>>,
    /// Type bindings local to the current kindcheck invocation
    locals: Vec<(Symbol, ArcKind)>,
    info: &'a (KindEnv + 'a),
    idents: &'a (ast::IdentEnv<Ident = Symbol> + 'a),
    pub subs: Substitution<ArcKind>,
    /// A cached type kind, `Type`
    type_kind: ArcKind,
    /// A cached one argument kind function, `Type -> Type`
    function1_kind: ArcKind,
    /// A cached two argument kind function, `Type -> Type -> Type`
    function2_kind: ArcKind,
    /// A cached row kind: `Row`
    row_kind: ArcKind,
}

fn walk_move_kind<F>(kind: ArcKind, f: &mut F) -> ArcKind
    where F: FnMut(&Kind) -> Option<ArcKind>,
{
    match walk_move_kind2(&kind, f) {
        Some(kind) => kind,
        None => kind,
    }
}
fn walk_move_kind2<F>(kind: &ArcKind, f: &mut F) -> Option<ArcKind>
    where F: FnMut(&Kind) -> Option<ArcKind>,
{
    let new = f(kind);
    let new2 = {
        let kind = new.as_ref().unwrap_or(kind);
        match **kind {
            Kind::Function(ref arg, ref ret) => {
                let arg_new = walk_move_kind2(arg, f);
                let ret_new = walk_move_kind2(ret, f);
                types::merge(arg, arg_new, ret, ret_new, Kind::function)
            }
            Kind::Type |
            Kind::Variable(_) |
            Kind::Row => None,
        }
    };
    new2.or(new)
}

impl<'a> KindCheck<'a> {
    pub fn new(info: &'a (KindEnv + 'a),
               idents: &'a (ast::IdentEnv<Ident = Symbol> + 'a))
               -> KindCheck<'a> {
        let typ = Kind::typ();
        let function1_kind = Kind::function(typ.clone(), typ.clone());
        KindCheck {
            variables: Vec::new(),
            locals: Vec::new(),
            info: info,
            idents: idents,
            subs: Substitution::new(),
            type_kind: typ.clone(),
            function1_kind: function1_kind.clone(),
            function2_kind: Kind::function(typ, function1_kind),
            row_kind: Kind::row(),
        }
    }

    pub fn add_local(&mut self, name: Symbol, kind: ArcKind) {
        self.locals.push((name, kind));
    }

    pub fn set_variables(&mut self, variables: &[Generic<Symbol>]) {
        self.variables.clear();
        self.variables.extend(variables.iter().cloned());
    }

    pub fn type_kind(&self) -> ArcKind {
        self.type_kind.clone()
    }

    pub fn function1_kind(&self) -> ArcKind {
        self.function1_kind.clone()
    }

    pub fn function2_kind(&self) -> ArcKind {
        self.function2_kind.clone()
    }

    pub fn row_kind(&self) -> ArcKind {
        self.row_kind.clone()
    }

    fn find(&mut self, id: &Symbol) -> Result<ArcKind> {
        let kind = self.variables
            .iter()
            .find(|var| var.id == *id)
            .map(|t| t.kind.clone())
            .or_else(|| {
                self.locals
                    .iter()
                    .find(|t| t.0 == *id)
                    .map(|t| t.1.clone())
            })
            .or_else(|| self.info.find_kind(id))
            .map_or_else(|| {
                let id_str = self.idents.string(id);
                if id_str.starts_with(char::is_uppercase) {
                    Err(UnifyError::Other(KindError::UndefinedType(id.clone())))
                } else {
                    // Create a new variable
                    self.locals.push((id.clone(), self.subs.new_var()));
                    Ok(self.locals.last().unwrap().1.clone())
                }
            },
                         Ok);

        if let Ok(ref kind) = kind {
            debug!("Find kind: {} => {}", self.idents.string(&id), kind);
        }

        kind
    }

    // Kindhecks `typ`, infering it to be of kind `Type`
    pub fn kindcheck_type(&mut self, typ: &mut ArcType) -> Result<ArcKind> {
        let type_kind = self.type_kind();
        self.kindcheck_expected(typ, &type_kind)
    }

    pub fn kindcheck_expected(&mut self, typ: &mut ArcType, expected: &ArcKind) -> Result<ArcKind> {
        debug!("Kindcheck {:?}", typ);
        let (kind, t) = try!(self.kindcheck(typ));
        let kind = try!(self.unify(expected, kind));
        *typ = self.finalize_type(t);
        debug!("Done {:?}", typ);
        Ok(kind)
    }

    fn builtin_kind(&self, typ: BuiltinType) -> ArcKind {
        match typ {
            BuiltinType::String | BuiltinType::Byte | BuiltinType::Char | BuiltinType::Int |
            BuiltinType::Float | BuiltinType::Unit => self.type_kind(),
            BuiltinType::Array => self.function1_kind(),
            BuiltinType::Function => self.function2_kind(),
        }
    }

    fn kindcheck(&mut self, typ: &ArcType) -> Result<(ArcKind, ArcType)> {
        match **typ {
            Type::Hole | Type::Opaque => Ok((self.subs.new_var(), typ.clone())),
            Type::Generic(ref gen) => {
                let mut gen = gen.clone();
                gen.kind = try!(self.find(&gen.id));
                Ok((gen.kind.clone(), Type::generic(gen)))
            }
            Type::Variable(_) => Ok((self.subs.new_var(), typ.clone())),
            Type::Builtin(builtin_typ) => Ok((self.builtin_kind(builtin_typ), typ.clone())),
            Type::App(ref ctor, ref args) => {
                let (mut kind, ctor) = try!(self.kindcheck(ctor));
                let mut new_args = Vec::new();
                for arg in args {
                    let f = Kind::function(self.subs.new_var(), self.subs.new_var());
                    kind = try!(self.unify(&f, kind));
                    kind = match *kind {
                        Kind::Function(ref arg_kind, ref ret) => {
                            let (actual, new_arg) = try!(self.kindcheck(arg));
                            new_args.push(new_arg);
                            try!(self.unify(arg_kind, actual));
                            ret.clone()
                        }
                        _ => {
                            return Err(UnifyError::TypeMismatch(self.function1_kind(),
                                                                kind.clone()))
                        }
                    };
                }
                Ok((kind, Type::app(ctor, new_args)))
            }
            Type::Variant(ref row) => {
                let row = try!(row.field_iter()
                    .map(|field| {
                        let (kind, typ) = try!(self.kindcheck(&field.typ));
                        let type_kind = self.type_kind();
                        try!(self.unify(&type_kind, kind));
                        Ok(Field {
                            name: field.name.clone(),
                            typ: typ,
                        })
                    })
                    .collect());
                Ok((self.type_kind(), Type::variant(row)))
            }
            Type::Record(ref row) => {
                let (kind, row) = try!(self.kindcheck(row));
                let row_kind = self.row_kind();
                try!(self.unify(&row_kind, kind));
                Ok((self.type_kind(), ArcType::from(Type::Record(row))))
            }
            Type::ExtendRow { ref types, ref fields, ref rest } => {
                let fields = try!(fields.iter()
                    .map(|field| {
                        let (kind, typ) = try!(self.kindcheck(&field.typ));
                        let type_kind = self.type_kind();
                        try!(self.unify(&type_kind, kind));
                        Ok(types::Field {
                            name: field.name.clone(),
                            typ: typ,
                        })
                    })
                    .collect());
                let (kind, rest) = try!(self.kindcheck(rest));
                let row_kind = self.row_kind();
                try!(self.unify(&row_kind, kind));
                Ok((row_kind, Type::extend_row(types.clone(), fields, rest)))
            }
            Type::EmptyRow => Ok((self.row_kind(), typ.clone())),
            Type::Ident(ref id) => self.find(id).map(|kind| (kind, typ.clone())),
            Type::Alias(ref alias) => self.find(&alias.name).map(|kind| (kind, typ.clone())),
        }
    }

    fn unify(&mut self, expected: &ArcKind, mut actual: ArcKind) -> Result<ArcKind> {
        debug!("Unify {:?} <=> {:?}", expected, actual);
        let result = unify::unify(&self.subs, &mut (), expected, &actual);
        match result {
            Ok(k) => Ok(k),
            Err(_errors) => {
                let mut expected = expected.clone();
                expected = update_kind(&self.subs, expected, None);
                actual = update_kind(&self.subs, actual, None);
                Err(UnifyError::TypeMismatch(expected, actual))
            }
        }
    }

    pub fn finalize_type(&self, typ: ArcType) -> ArcType {
        let default = Some(&self.type_kind);
        types::walk_move_type(typ,
                              &mut |typ| {
            match *typ {
                Type::Variable(ref var) => {
                    let mut kind = var.kind.clone();
                    kind = update_kind(&self.subs, kind, default);
                    Some(Type::variable(types::TypeVariable {
                        id: var.id,
                        kind: kind,
                    }))
                }
                Type::Generic(ref var) => Some(Type::generic(self.finalize_generic(var))),
                _ => None,
            }
        })
    }
    pub fn finalize_generic(&self, var: &Generic<Symbol>) -> Generic<Symbol> {
        let mut kind = var.kind.clone();
        kind = update_kind(&self.subs, kind, Some(&self.type_kind));
        types::Generic {
            id: var.id.clone(),
            kind: kind,
        }
    }
}

fn update_kind(subs: &Substitution<ArcKind>, kind: ArcKind, default: Option<&ArcKind>) -> ArcKind {
    walk_move_kind(kind,
                   &mut |kind| {
        match *kind {
            Kind::Variable(id) => subs.find_type_for_var(id).cloned().or_else(|| default.cloned()),
            _ => None,
        }
    })
}

/// Enumeration possible errors other than mismatch and occurs when kindchecking
#[derive(Debug, PartialEq)]
pub enum KindError<I> {
    /// The type is not defined in the current scope
    UndefinedType(I),
}

pub fn fmt_kind_error<I>(error: &Error<I>, f: &mut fmt::Formatter) -> fmt::Result
    where I: fmt::Display,
{
    use unify::Error::*;
    match *error {
        TypeMismatch(ref expected, ref actual) => {
            write!(f,
                   "Kind mismatch\nExpected: {}\nFound: {}",
                   expected,
                   actual)
        }
        Occurs(ref var, ref typ) => write!(f, "Variable `{}` occurs in `{}`.", var, typ),
        Other(KindError::UndefinedType(ref name)) => write!(f, "Type '{}' is not defined", name),
    }
}

impl Substitutable for ArcKind {
    type Variable = u32;

    fn new(x: u32) -> ArcKind {
        Kind::variable(x)
    }

    fn from_variable(x: u32) -> ArcKind {
        Kind::variable(x)
    }

    fn get_var(&self) -> Option<&u32> {
        match **self {
            Kind::Variable(ref var) => Some(var),
            _ => None,
        }
    }

    fn traverse<F>(&self, f: &mut F)
        where F: Walker<ArcKind>,
    {
        kind::walk_kind(self, f);
    }
}

impl<S> unify::Unifiable<S> for ArcKind {
    type Error = KindError<Symbol>;

    fn zip_match<U>(&self,
                    other: &Self,
                    unifier: &mut unify::UnifierState<S, U>)
                    -> ::std::result::Result<Option<Self>, Error<Symbol>>
        where U: unify::Unifier<S, Self>,
    {
        match (&**self, &**other) {
            (&Kind::Function(ref l1, ref l2), &Kind::Function(ref r1, ref r2)) => {
                let a = unifier.try_match(l1, r1);
                let r = unifier.try_match(l2, r2);
                Ok(types::merge(l1, a, l2, r, Kind::function))
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
}
