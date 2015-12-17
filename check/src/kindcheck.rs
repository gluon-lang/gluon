use std::rc::Rc;
use std::fmt;

use base::ast::{Type, Kind};
use typecheck::TcType;
use base::ast;
use base::symbol::Symbol;
use substitution::{Substitution, Substitutable};

#[derive(Debug, PartialEq)]
pub enum Error<I> {
    KindMismatch(Rc<Kind>, Rc<Kind>),
    UndefinedType(I),
    StringError(&'static str),
}
use self::Error::*;

impl<I: fmt::Display> fmt::Display for Error<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            KindMismatch(ref expected, ref actual) => {
                write!(f,
                       "Kind mismatch\nExpected: {}\nFound: {}",
                       expected,
                       actual)
            }
            UndefinedType(ref name) => write!(f, "Type '{}' is not defined", name),
            StringError(s) => write!(f, "{}", s),
        }
    }
}

pub type Result<T> = ::std::result::Result<T, Error<Symbol>>;

impl Substitutable for Kind {
    type Variable = u32;

    fn new(x: u32) -> Kind {
        Kind::Variable(x)
    }

    fn from_variable(x: u32) -> Kind {
        Kind::Variable(x)
    }

    fn get_var(&self) -> Option<&u32> {
        match *self {
            Kind::Variable(ref var) => Some(var),
            _ => None,
        }
    }

    fn occurs(&self, subs: &Substitution<Kind>, var: &u32) -> bool {
        let kind = subs.real(self);
        match *kind {
            Kind::Variable(other) => *var == other,
            Kind::Function(ref a, ref r) => a.occurs(subs, var) || r.occurs(subs, var),
            Kind::Star => false,
        }
    }
}

pub trait KindEnv {
    fn find_kind(&self, type_name: Symbol) -> Option<Rc<Kind>>;
}

impl<'a, T: ?Sized + KindEnv> KindEnv for &'a T {
    fn find_kind(&self, id: Symbol) -> Option<Rc<Kind>> {
        (**self).find_kind(id)
    }
}

impl<T: KindEnv, U: KindEnv> KindEnv for (T, U) {
    fn find_kind(&self, id: Symbol) -> Option<Rc<Kind>> {
        let &(ref outer, ref inner) = self;
        inner.find_kind(id)
             .or_else(|| outer.find_kind(id))
    }
}

pub struct KindCheck<'a> {
    variables: Vec<TcType>,
    ///Type bindings local to the current kindcheck invocation
    locals: Vec<(Symbol, Rc<Kind>)>,
    info: &'a (KindEnv + 'a),
    idents: &'a (ast::IdentEnv<Ident = Symbol> + 'a),
    pub subs: Substitution<Kind>,
    star: Rc<Kind>,
}

fn walk_move_kind<F>(kind: Rc<Kind>, f: &mut F) -> Rc<Kind>
    where F: FnMut(&Kind) -> Option<Rc<Kind>>
{
    match walk_move_kind2(&kind, f) {
        Some(kind) => kind,
        None => kind,
    }
}
fn walk_move_kind2<F>(kind: &Rc<Kind>, f: &mut F) -> Option<Rc<Kind>>
    where F: FnMut(&Kind) -> Option<Rc<Kind>>
{
    let new = f(kind);
    let new2 = {
        let kind = new.as_ref().map(|k| &**k).unwrap_or(kind);
        match *kind {
            Kind::Function(ref a, ref r) => {
                match (walk_move_kind2(a, f), walk_move_kind2(r, f)) {
                    (Some(a), Some(r)) => Some(Rc::new(Kind::Function(a, r))),
                    (Some(a), None) => Some(Rc::new(Kind::Function(a, r.clone()))),
                    (None, Some(r)) => Some(Rc::new(Kind::Function(a.clone(), r))),
                    (None, None) => None,
                }
            }
            Kind::Star | Kind::Variable(_) => None,
        }
    };
    new2.or(new)
}

impl<'a> KindCheck<'a> {
    pub fn new(info: &'a (KindEnv + 'a),
               idents: &'a (ast::IdentEnv<Ident = Symbol> + 'a),
               subs: Substitution<Kind>)
               -> KindCheck<'a> {
        KindCheck {
            variables: Vec::new(),
            locals: Vec::new(),
            info: info,
            idents: idents,
            subs: subs,
            star: Rc::new(Kind::Star),
        }
    }

    pub fn add_local(&mut self, name: Symbol, kind: Rc<Kind>) {
        self.locals.push((name, kind));
    }

    pub fn set_variables(&mut self, variables: &[TcType]) {
        self.variables.clear();
        self.variables.extend(variables.iter().cloned());
    }

    pub fn star(&self) -> Rc<Kind> {
        self.star.clone()
    }

    fn find(&mut self, id: Symbol) -> Result<Rc<Kind>> {
        let kind = self.variables
                       .iter()
                       .find(|var| {
                           match ***var {
                               Type::Generic(ref other) => other.id == id,
                               _ => false,
                           }
                       })
                       .map(|t| t.kind().clone())
                       .or_else(|| {
                           self.locals
                               .iter()
                               .find(|t| t.0 == id)
                               .map(|t| t.1.clone())
                       })
                       .or_else(|| self.info.find_kind(id))
                       .map(|t| Ok(t))
                       .unwrap_or_else(|| {
                           let id_str = self.idents.string(&id);
                           if id_str.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) {
                               Err(UndefinedType(id))
                           } else {
                               // Create a new variable
                               self.locals.push((id, Rc::new(self.subs.new_var())));
                               Ok(self.locals.last().unwrap().1.clone())
                           }
                       });
        debug!("Find kind: {} => {}",
               self.idents.string(&id),
               kind.as_ref().unwrap());
        kind
    }

    // Kindhecks `typ`, infering it to be of kind `*`
    pub fn kindcheck_type(&mut self, typ: &mut TcType) -> Result<Kind> {
        debug!("Kindcheck {:?}", typ);
        let (kind, t) = try!(self.kindcheck(typ));
        let star = self.star.clone();
        let kind = try!(self.unify(&star, kind));
        *typ = self.finalize_type(t);
        debug!("Done {:?}", typ);
        Ok((*kind).clone())
    }

    fn kindcheck(&mut self, typ: &TcType) -> Result<(Rc<Kind>, TcType)> {
        match **typ {
            Type::Generic(ref gen) => {
                let mut gen = gen.clone();
                gen.kind = try!(self.find(gen.id));
                Ok((gen.kind.clone(), Type::generic(gen)))
            }
            Type::Variable(_) => panic!("kindcheck called on variable"),
            Type::Builtin(_) => Ok((self.star.clone(), typ.clone())),
            Type::Array(ref typ) => {
                let (kind, typ) = try!(self.kindcheck(typ));
                let star = self.star.clone();
                try!(self.unify(&star, kind));
                Ok((self.star.clone(), Type::array(typ)))
            }
            Type::App(ref f, ref r) => {
                let (kind, f) = try!(self.kindcheck(f));
                let kind_fn = Rc::new(Kind::Function(self.subs.new_kind(), self.subs.new_kind()));
                let kind = try!(self.unify(&kind_fn, kind));
                match *kind {
                    Kind::Function(ref arg, ref ret) => {
                        let (arg_kind, r) = try!(self.kindcheck(r));
                        try!(self.unify(&arg, arg_kind));
                        Ok((ret.clone(), Type::app(f, r)))
                    }
                    _ => panic!("Expected kind function"),
                }
            }
            Type::Data(ast::TypeConstructor::Builtin(_), _) => panic!("Builtin with arguments"),
            Type::Data(ast::TypeConstructor::Data(ctor), ref args) => {
                let mut kind = try!(self.find(ctor));
                let mut new_args = Vec::new();
                for arg in args {
                    let f = Rc::new(Kind::Function(self.subs.new_kind(), self.subs.new_kind()));
                    kind = try!(self.unify(&f, kind));
                    kind = match *kind {
                        Kind::Function(ref arg_kind, ref ret) => {
                            let (actual, new_arg) = try!(self.kindcheck(arg));
                            new_args.push(new_arg);
                            try!(self.unify(arg_kind, actual));
                            ret.clone()
                        }
                        _ => return Err(StringError("Expected kind: a -> a")),
                    };
                }
                Ok((kind, Type::data(ast::TypeConstructor::Data(ctor), new_args)))
            }
            Type::Function(ref args, ref ret) => {
                let (kind, arg) = try!(self.kindcheck(&args[0]));
                let star = self.star.clone();
                try!(self.unify(&star, kind));
                let (kind, ret) = try!(self.kindcheck(ret));
                let star = self.star.clone();
                let new_kind = try!(self.unify(&star, kind));
                Ok((new_kind, Type::function(vec![arg], ret)))
            }
            Type::Variants(ref variants) => {
                let variants = try!(variants.iter()
                                            .map(|variant| {
                                                let (kind, typ) = try!(self.kindcheck(&variant.1));
                                                let star = self.star.clone();
                                                try!(self.unify(&star, kind));
                                                Ok((variant.0, typ))
                                            })
                                            .collect());
                Ok((self.star.clone(), Type::variants(variants)))
            }
            Type::Record { ref types, ref fields } => {
                let fields = try!(fields.iter()
                                        .map(|field| {
                                            let (kind, typ) = try!(self.kindcheck(&field.typ));
                                            let star = self.star.clone();
                                            try!(self.unify(&star, kind));
                                            Ok(ast::Field {
                                                name: field.name,
                                                typ: typ,
                                            })
                                        })
                                        .collect());
                Ok((self.star.clone(), Type::record(types.clone(), fields)))
            }
        }
    }

    fn unify(&mut self, expected: &Rc<Kind>, mut actual: Rc<Kind>) -> Result<Rc<Kind>> {
        debug!("Unify {:?} <=> {:?}", expected, actual);
        if self.unify_(expected, &actual) {
            Ok(self.subs.update_kind(actual))
        } else {
            let mut expected = expected.clone();
            expected = self.subs.update_kind(expected);
            actual = self.subs.update_kind(actual);
            Err(KindMismatch(expected, actual))
        }
    }
    fn unify_(&self, expected: &Kind, actual: &Kind) -> bool {
        match (self.subs.real(expected), self.subs.real(actual)) {
            (&Kind::Variable(l), &Kind::Variable(r)) if l == r => true,
            (&Kind::Variable(ref l), r) => {
                self.subs
                    .union(l, r)
                    .is_ok()
            }
            (l, &Kind::Variable(ref r)) => {
                self.subs
                    .union(r, l)
                    .is_ok()
            }
            (&Kind::Function(ref l1, ref l2),
             &Kind::Function(ref r1, ref r2)) => self.unify_(l1, r1) && self.unify_(l2, r2),
            (l, r) => l == r,
        }
    }

    pub fn finalize_type(&self, typ: TcType) -> TcType {
        ast::walk_move_type(typ,
                            &mut |typ| {
                                match *typ {
                                    Type::Variable(ref var) => {
                                        let mut kind = var.kind.clone();
                                        kind = self.subs.update_kind(kind);
                                        Some(Type::variable(ast::TypeVariable {
                                            id: var.id,
                                            kind: kind,
                                        }))
                                    }
                                    Type::Generic(ref var) => {
                                        let mut kind = var.kind.clone();
                                        kind = self.subs.update_kind(kind);
                                        Some(Type::generic(ast::Generic {
                                            id: var.id,
                                            kind: kind,
                                        }))
                                    }
                                    _ => None,
                                }
                            })
    }
}

impl Substitution<Kind> {
    pub fn new_kind(&mut self) -> Rc<ast::Kind> {
        Rc::new(self.new_var())
    }

    fn update_kind(&self, kind: Rc<Kind>) -> Rc<Kind> {
        walk_move_kind(kind,
                       &mut |kind| {
                           match *kind {
                               Kind::Variable(id) => {
                                   self.find_type_for_var(id).map(|t| Rc::new(t.clone()))
                               }
                               _ => None,
                           }
                       })
    }
}
