use base::ast::{Type, Kind};
use typecheck::TcType;
use base::ast;
use base::interner::InternedStr;
use substitution::{Substitution, Substitutable};

#[derive(Debug, PartialEq)]
pub enum Error {
    KindMismatch(Kind, Kind),
    StringError(&'static str)
}
use self::Error::*;

type Result<T> = ::std::result::Result<T, Error>;

impl Substitutable for Kind {
    fn new(x: u32) -> Kind {
        Kind::Variable(x)
    }
    fn get_var(&self) -> Option<u32> {
        match *self {
            Kind::Variable(var) => Some(var),
            _ => None
        }
    }
}

pub struct KindCheck<'a> {
    variables: &'a mut [TcType],
    info: &'a (Fn(InternedStr) -> Option<&'a TcType> + 'a),
    subs: Substitution<Kind>
}

fn walk_mut_kind<F>(kind: &mut Kind, f: &mut F)
    where F: FnMut(&mut Kind) {
    f(kind);
    match *kind {
        Kind::Function(ref mut a, ref mut r) => {
            walk_mut_kind(a, f);
            walk_mut_kind(r, f);
        }
        Kind::Star | Kind::Variable(_) => (),
    }
}

impl <'a> KindCheck<'a> {

    pub fn new(info: &'a Fn(InternedStr) -> Option<&'a TcType>, variables: &'a mut [TcType], id: u32) -> KindCheck<'a> {
        let mut subs = Substitution::new();
        subs.var_id = id;
        KindCheck { variables: variables, info: info, subs: subs }
    }

    fn find(&mut self, id: InternedStr) -> Result<Kind> {
        let kind = self.variables.iter()
            .find(|var| match ***var { Type::Generic(ref other) => other.id == id, _ => false })
            .map(|t| t.kind().clone())
            .or_else(|| {
                (self.info)(id)
                    .and_then(|typ| {
                        match **typ {
                            Type::Data(_, ref args) => {
                                let mut kind = Kind::Star;
                                for arg in args.iter().rev() {
                                    kind = Kind::Function(Box::new(arg.kind().clone()), Box::new(kind));
                                }
                                Some(kind)
                            }
                            _ => None
                        }
                    })
            })
            .map(|t| Ok(t))
            .unwrap_or_else(|| Ok(self.subs.variable_for(id)));
        debug!("Find kind: {} => {}", id, kind.as_ref().unwrap());
        kind
    }

    pub fn kindcheck_type(&mut self, typ: &mut TcType) -> Result<Kind> {
        let (kind, t) = try!(self.kindcheck(typ));
        let subs = &mut self.subs;
        let mut f = |typ| ast::walk_move_type(typ, &mut |typ| {
            match *typ {
                Type::Variable(ref var) => {
                    let mut kind = var.kind.clone();
                    subs.set_kind(&mut kind);
                    Some(Type::variable(ast::TypeVariable { id: var.id, kind: kind }))
                }
                Type::Generic(ref var) => {
                    let mut kind = var.kind.clone();
                    subs.set_kind(&mut kind);
                    Some(Type::generic(ast::Generic { id: var.id, kind: kind }))
                }
                _ => None
            }
        });
        *typ  = f(t);
        for typ in self.variables.iter_mut() {
            *typ = f(typ.clone());
        }
        Ok(kind)
    }

    fn kindcheck(&mut self, typ: &TcType) -> Result<(Kind, TcType)> {
        match **typ {
            Type::Generic(ref gen) => {
                let mut gen = gen.clone();
                gen.kind = try!(self.find(gen.id));
                Ok((gen.kind.clone(), Type::generic(gen)))
            }
            Type::Variable(_) => {
                panic!("kindcheck called on variable")
            }
            Type::Builtin(_) => Ok((Kind::Star, typ.clone())),
            Type::Array(ref typ) => {
                let (kind, typ) = try!(self.kindcheck(typ));
                try!(self.unify(&Kind::Star, kind));
                Ok((Kind::Star, Type::array(typ)))
            }
            Type::App(ref f, ref r) => {
                let (kind, f) = try!(self.kindcheck(f));
                let kind_fn = Kind::Function(Box::new(self.subs.new_kind()), Box::new(self.subs.new_kind()));
                let kind = try!(self.unify(&kind_fn, kind));
                match kind {
                    Kind::Function(arg, ret) => {
                        let (arg_kind, r) = try!(self.kindcheck(r));
                        try!(self.unify(&arg, arg_kind));
                        Ok((*ret, Type::app(f, r)))
                    }
                    _ => panic!("Expected kind function")
                }
            }
            Type::Data(ast::TypeConstructor::Builtin(_), _) => {
                panic!("Builtin with arguments")
            }
            Type::Data(ast::TypeConstructor::Data(ctor), ref args) => {
                let mut kind = try!(self.find(ctor));
                let mut new_args = Vec::new();
                for arg in args {
                    let f = Kind::Function(Box::new(self.subs.new_kind()), Box::new(self.subs.new_kind()));
                    kind = try!(self.unify(&f, kind));
                    match kind {
                        Kind::Function(arg_kind, ret) => {
                            let (actual, new_arg) = try!(self.kindcheck(arg));
                            new_args.push(new_arg);
                            try!(self.unify(&arg_kind, actual));
                            kind = *ret;
                        }
                        _ => return Err(StringError("Expected kind: a -> a"))
                    }
                }
                Ok((kind, Type::data(ast::TypeConstructor::Data(ctor), new_args)))
            }
            Type::Function(ref args, ref ret) => {
                let (kind, arg) = try!(self.kindcheck(&args[0]));
                try!(self.unify(&Kind::Star, kind));
                let (kind, ret) = try!(self.kindcheck(ret));
                let new_kind = try!(self.unify(&Kind::Star, kind));
                Ok((new_kind, Type::function(vec![arg], ret)))
            }
            Type::Variants(ref variants) => {
                let variants = try!(variants.iter().map(|variant| {
                    let (kind, typ) = try!(self.kindcheck(&variant.1));
                    try!(self.unify(&Kind::Star, kind));
                    Ok((variant.0, typ))
                }).collect());
                Ok((Kind::Star, Type::variants(variants)))
            }
            Type::Record(ref fields) => {
                let fields = try!(fields.iter().map(|field| {
                    let (kind, typ) = try!(self.kindcheck(&field.typ));
                    try!(self.unify(&Kind::Star, kind));
                    Ok(ast::Field { name: field.name, typ: typ })
                }).collect());
                Ok((Kind::Star, Type::record(fields)))
            }
        }
    }

    fn unify(&mut self, expected: &Kind, mut actual: Kind) -> Result<Kind> {
        debug!("Unify {:?} <=> {:?}", expected, actual);
        if self.unify_(expected, &actual) {
            self.subs.set_kind(&mut actual);
            Ok(actual)
        }
        else {
            let mut expected = expected.clone();
            self.subs.set_kind(&mut expected);
            self.subs.set_kind(&mut actual);
            Err(KindMismatch(expected, actual))
        }
    }
    fn unify_(&self, expected: &Kind, actual: &Kind) -> bool {
        match (expected, actual) {
            (&Kind::Variable(l), r) => {
                self.union(l, r);
                true
            }
            (l, &Kind::Variable(r)) => {
                self.union(r, l);
                true
            }
            (&Kind::Function(ref l1, ref l2), &Kind::Function(ref r1, ref r2)) => {
                self.unify_(l1, r1) && self.unify_(l2, r2)
            }
            (l, r) => l == r
        }
    }

    fn union(&self, id: u32, typ: &Kind) {
        {
            let id_type = self.subs.find_type_for_var(id);
            let other_type = self.subs.real(typ);
            if id_type.map(|x| x == other_type).unwrap_or(Kind::Variable(id.clone()) == *other_type) {
                return
            }
        }
        let map: &mut _ = unsafe { &mut *self.subs.map.get() };
        //Always make sure the mapping is from a higher variable to a lower
        //This way the resulting variables are always equal to any variables in the globals
        //declaration
        match *typ {
            Kind::Variable(other_id) if id < other_id => map.insert(other_id, box Kind::Variable(id)),
            _ => map.insert(id, box typ.clone())
        };
    }
}

impl Substitution<Kind> {
    fn new_kind(&mut self) -> ast::Kind {
        self.new_var()
    }

    fn set_kind(&mut self, kind: &mut Kind) {
        walk_mut_kind(kind, &mut |kind| {
            *kind = match *kind {
                Kind::Variable(id) =>
                    match self.find_type_for_var(id).map(|t| t.clone()) {
                        Some(k) => k,
                        None => return
                    },
                _ => return
            }
        });
    }
}
