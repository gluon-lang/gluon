use base::ast::{Type, TcType, Kind};
use base::ast;
use base::interner::InternedStr;
use typecheck::TypeEnv;
use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt;

#[derive(Debug, PartialEq)]
pub enum Error {
    KindMismatch(Kind, Kind),
    UndefinedVariable(InternedStr),
    StringError(&'static str)
}
use self::Error::*;

type Result<T> = ::std::result::Result<T, Error>;

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
            .find(|var| match **var { Type::Generic(ref other) => other.id == id, _ => false })
            .map(|t| t.kind().clone())
            .or_else(|| {
                (self.info)(id)
                    .and_then(|typ| {
                        match *typ {
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
        let kind = try!(self.kindcheck(typ));
        let subs = &mut self.subs;
        let mut f = |typ| ast::walk_mut_type(typ, &mut |typ| {
            match *typ {
                Type::Variable(ref mut var) => subs.set_kind(&mut var.kind),
                Type::Generic(ref mut var) => subs.set_kind(&mut var.kind),
                _ => ()
            };
        });
        f(typ);
        for typ in self.variables.iter_mut() {
            f(typ);
        }
        Ok(kind)
    }

    fn kindcheck(&mut self, typ: &mut TcType) -> Result<Kind> {
        match *typ {
            Type::Generic(ref mut gen) => {
                gen.kind = try!(self.find(gen.id));
                Ok(gen.kind.clone())
            }
            Type::Variable(ref mut var) => {
                panic!("kindcheck called on variable")
            }
            Type::Builtin(_) => Ok(Kind::Star),
            Type::Array(ref mut typ) => {
                let kind = try!(self.kindcheck(typ));
                try!(self.unify(&Kind::Star, kind));
                Ok(Kind::Star)
            }
            Type::App(ref mut f, ref mut r) => {
                let kind = try!(self.kindcheck(f));
                let f = Kind::Function(Box::new(self.subs.new_kind()), Box::new(self.subs.new_kind()));
                let kind = try!(self.unify(&f, kind));
                match kind {
                    Kind::Function(arg, ret) => {
                        let arg_kind = try!(self.kindcheck(r));
                        try!(self.unify(&arg, arg_kind));
                        Ok(*ret)
                    }
                    _ => panic!("Expected kind function")
                }
            }
            Type::Data(ast::TypeConstructor::Builtin(_), _) => {
                panic!("Builtin with arguments")
            }
            Type::Data(ast::TypeConstructor::Data(ctor), ref mut args) => {
                let mut kind = try!(self.find(ctor));
                for arg in args {
                    let f = Kind::Function(Box::new(self.subs.new_kind()), Box::new(self.subs.new_kind()));
                    kind = try!(self.unify(&f, kind));
                    match kind {
                        Kind::Function(arg_kind, ret) => {
                            let actual = try!(self.kindcheck(arg));
                            try!(self.unify(&arg_kind, actual));
                            kind = *ret;
                        }
                        _ => return Err(StringError("Expected kind: a -> a"))
                    }
                }
                Ok(kind)
            }
            Type::Function(ref mut args, ref mut ret) => {
                let kind = try!(self.kindcheck(&mut args[0]));
                try!(self.unify(&Kind::Star, kind));
                let kind = try!(self.kindcheck(ret));
                self.unify(&Kind::Star, kind)
            }
            Type::Variants(ref mut variants) => {
                for variant in variants {
                    let kind = try!(self.kindcheck(&mut variant.1));
                    try!(self.unify(&Kind::Star, kind));
                }
                Ok(Kind::Star)
            }
            Type::Record(ref mut fields) => {
                for field in fields {
                    let kind = try!(self.kindcheck(&mut field.typ));
                    try!(self.unify(&Kind::Star, kind));
                }
                Ok(Kind::Star)
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
            Kind::Variable(other_id) if id < other_id => map.insert(other_id, box Kind::Variable(id.clone())),
            _ => map.insert(id, box typ.clone())
        };
    }
}


struct Substitution<T> {
    map: UnsafeCell<HashMap<u32, Box<T>>>,
    variables: HashMap<InternedStr, Kind>,
    var_id: u32
}

trait Substitutable: Clone {
    fn get_var(&self) -> Option<u32>;
}

impl Substitutable for Kind {
    fn get_var(&self) -> Option<u32> {
        match *self {
            Kind::Variable(var) => Some(var),
            _ => None
        }
    }
}

impl <T: fmt::Debug> fmt::Debug for Substitution<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let map: &_ = unsafe { &*self.map.get() };
        write!(f, "Substitution {{ map: {:?}, variables: {:?}, var_id: {:?} }}",
               map, self.variables, self.var_id)
    }
}

impl <T: Substitutable> Substitution<T> {
    fn new() -> Substitution<T> {
        Substitution {
            map: UnsafeCell::new(HashMap::new()),
            variables: HashMap::new(),
            var_id: 1
        }
    }

    fn variable_for(&mut self, id: InternedStr) -> Kind {
        match self.variables.entry(id) {
            Entry::Vacant(entry) => {
                self.var_id += 1;
                entry.insert(Kind::Variable(self.var_id)).clone()
            }
            Entry::Occupied(entry) => entry.get().clone()
        }
    }

    fn clear(&mut self) {
        unsafe { (*self.map.get()).clear(); }
        self.variables.clear();
        self.var_id = 1;
    }

    unsafe fn insert(&mut self, var: u32, t: T) {
        (*self.map.get()).insert(var, Box::new(t));
    }

    fn real<'r>(&'r self, typ: &'r T) -> &'r T {
        match typ.get_var() {
            Some(var) => match self.find_type_for_var(var) {
                Some(t) => t,
                None => typ
            },
            _ => typ
        }
    }

    fn find_type_for_var(&self, var: u32) -> Option<&T> {
        //Use unsafe so that we can hold a reference into the map and continue
        //to look for parents
        //Since we never have a cycle in the map we will never hold a &mut
        //to the same place
        let map = unsafe { &mut *self.map.get() };
        map.get_mut(&var).map(|typ| {
            let new_type = match typ.get_var() {
                Some(parent_var) if parent_var != var => {
                    match self.find_type_for_var(parent_var) {
                        Some(other) => Some(other.clone()),
                        None => None
                    }
                }
                _ => None
            };
            if let Some(new_type) = new_type {
                **typ = new_type;
            }
            &**typ
        })
    }

    fn new_var(&mut self) -> TcType {
        self.var_id += 1;
        Type::Variable(ast::TypeVariable { kind: ast::Kind::Star, id: self.var_id })
    }
    fn new_kind(&mut self) -> ast::Kind {
        self.var_id += 1;
        ast::Kind::Variable(self.var_id)
    }
}

impl Substitution<Kind> {
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
