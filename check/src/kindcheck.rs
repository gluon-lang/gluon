use std::fmt;

use base::ast;
use base::types::{self, BuiltinType, Generic, TcType, Type, walk_move_type};
use base::symbol::Symbol;
use base::types::TypeEnv;

use substitution::Substitution;
use unify_type::State;
use unify;

use unify::Error as UnifyError;

pub type RcKind = TcType;
pub type Kind = Type<Symbol, TcType>;

pub type Error<I> = UnifyError<RcKind, KindError<I>>;

pub type Result<T> = ::std::result::Result<T, Error<Symbol>>;


/// Struct containing methods for kindchecking types
pub struct KindCheck<'a> {
    variables: Vec<Generic<Symbol, TcType>>,
    /// Type bindings local to the current kindcheck invocation
    locals: Vec<(Symbol, RcKind)>,
    info: &'a (TypeEnv + 'a),
    idents: &'a (ast::IdentEnv<Ident = Symbol> + 'a),
    pub subs: Substitution<RcKind>,
    /// A cached type kind, `Type`
    type_kind: RcKind,
    /// A cached one argument kind function, `Type -> Type`
    function1_kind: RcKind,
    /// A cached two argument kind function, `Type -> Type -> Type`
    function2_kind: RcKind,
}

impl<'a> KindCheck<'a> {
    pub fn new(info: &'a (TypeEnv + 'a),
               idents: &'a (ast::IdentEnv<Ident = Symbol> + 'a),
               subs: Substitution<RcKind>)
               -> KindCheck<'a> {
        let typ = Kind::typ();
        let function1_kind = Kind::function(vec![typ.clone()], typ.clone());
        KindCheck {
            variables: Vec::new(),
            locals: Vec::new(),
            info: info,
            idents: idents,
            subs: subs,
            type_kind: typ.clone(),
            function1_kind: function1_kind.clone(),
            function2_kind: Kind::function(vec![typ], function1_kind),
        }
    }

    pub fn add_local(&mut self, name: Symbol, kind: RcKind) {
        self.locals.push((name, kind));
    }

    pub fn set_variables(&mut self, variables: &[Generic<Symbol, TcType>]) {
        self.variables.clear();
        self.variables.extend(variables.iter().cloned());
    }

    pub fn type_kind(&self) -> RcKind {
        self.type_kind.clone()
    }

    pub fn function1_kind(&self) -> RcKind {
        self.function1_kind.clone()
    }

    pub fn function2_kind(&self) -> RcKind {
        self.function2_kind.clone()
    }

    fn find(&mut self, id: &Symbol) -> Result<RcKind> {
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
                if id_str.chars().next().map_or(false, |c| c.is_uppercase()) {
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
    pub fn kindcheck_type(&mut self, typ: &mut TcType) -> Result<RcKind> {
        debug!("Kindcheck {:?}", typ);
        let (kind, t) = try!(self.kindcheck(typ));
        let type_kind = self.type_kind();
        let kind = try!(self.unify(&type_kind, kind));
        *typ = self.finalize_type(t);
        debug!("Done {:?}", typ);
        Ok(kind)
    }

    fn builtin_kind(&self, typ: BuiltinType) -> RcKind {
        match typ {
            BuiltinType::String | BuiltinType::Byte | BuiltinType::Char | BuiltinType::Int |
            BuiltinType::Float | BuiltinType::Unit | BuiltinType::Type => self.type_kind(),
            BuiltinType::Array => self.function1_kind(),
            BuiltinType::Function => self.function2_kind(),
        }
    }

    fn kindcheck(&mut self, typ: &TcType) -> Result<(RcKind, TcType)> {
        match **typ {
            Type::Hole => Ok((self.subs.new_var(), typ.clone())),
            Type::Generic(ref gen) => {
                let mut gen = gen.clone();
                gen.kind = try!(self.find(&gen.id));
                Ok((gen.kind.clone(), Type::generic(gen)))
            }
            Type::Variable(_) => panic!("kindcheck called on variable"),
            Type::Builtin(builtin_typ) => Ok((self.builtin_kind(builtin_typ), typ.clone())),
            Type::App(ref ctor, ref args) => {
                let (mut kind, ctor) = try!(self.kindcheck(ctor));
                let mut new_args = Vec::new();
                for arg in args {
                    let f = Kind::function(vec![self.subs.new_var()], self.subs.new_var());
                    kind = try!(self.unify(&f, kind));
                    kind = match kind.as_function() {
                        Some((arg_kind, ret)) => {
                            let (actual, new_arg) = try!(self.kindcheck(arg));
                            new_args.push(new_arg);
                            try!(self.unify(arg_kind, actual));
                            ret.clone()
                        }
                        None => {
                            return Err(UnifyError::TypeMismatch(self.function1_kind(),
                                                                kind.clone()))
                        }
                    };
                }
                Ok((kind, Type::app(ctor, new_args)))
            }
            Type::Variants(ref variants) => {
                let variants = try!(variants.iter()
                    .map(|variant| {
                        let (kind, typ) = try!(self.kindcheck(&variant.1));
                        let type_kind = self.type_kind();
                        try!(self.unify(&type_kind, kind));
                        Ok((variant.0.clone(), typ))
                    })
                    .collect());
                Ok((self.type_kind(), Type::variants(variants)))
            }
            Type::Record { ref types, ref fields } => {
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
                Ok((self.type_kind(), Type::record(types.clone(), fields)))
            }
            Type::Id(ref id) => self.find(id).map(|kind| (kind, typ.clone())),
            Type::Alias(ref alias) => self.find(&alias.name).map(|kind| (kind, typ.clone())),
        }
    }

    fn unify(&mut self, expected: &RcKind, mut actual: RcKind) -> Result<RcKind> {
        debug!("Unify {:?} <=> {:?}", expected, actual);
        let state = State::new(self.info);
        let result = unify::unify(&self.subs, state, expected, &actual);
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

    pub fn finalize_type(&self, typ: TcType) -> TcType {
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
    pub fn finalize_generic(&self, var: &Generic<Symbol, TcType>) -> Generic<Symbol, TcType> {
        let mut kind = var.kind.clone();
        kind = update_kind(&self.subs, kind, Some(&self.type_kind));
        types::Generic {
            id: var.id.clone(),
            kind: kind,
        }
    }
}

fn update_kind(subs: &Substitution<RcKind>, kind: RcKind, default: Option<&RcKind>) -> RcKind {
    walk_move_type(kind,
                   &mut |kind| {
        match *kind {
            Type::Variable(ref id) => {
                subs.find_type_for_var(id.id)
                    .map(|kind| update_kind(subs, kind.clone(), default))
                    .or_else(|| default.cloned())
            }
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
    where I: fmt::Display
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