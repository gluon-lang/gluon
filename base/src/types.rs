//! Module containing types representing embed_lang's type system
use std::fmt;
use std::ops::Deref;
use std::rc::Rc;

use ast;
use ast::{ASTType, DisplayEnv};
use symbol::Symbol;

pub type TcType = ast::ASTType<Symbol>;
pub type TcIdent = ast::TcIdent<Symbol>;

pub trait KindEnv {
    fn find_kind(&self, type_name: &Symbol) -> Option<RcKind>;
}

impl KindEnv for () {
    fn find_kind(&self, _type_name: &Symbol) -> Option<RcKind> {
        None
    }
}

impl<'a, T: ?Sized + KindEnv> KindEnv for &'a T {
    fn find_kind(&self, id: &Symbol) -> Option<RcKind> {
        (**self).find_kind(id)
    }
}

impl<T: KindEnv, U: KindEnv> KindEnv for (T, U) {
    fn find_kind(&self, id: &Symbol) -> Option<RcKind> {
        let &(ref outer, ref inner) = self;
        inner.find_kind(id)
             .or_else(|| outer.find_kind(id))
    }
}

pub trait TypeEnv: KindEnv {
    fn find_type(&self, id: &Symbol) -> Option<&TcType>;
    fn find_type_info(&self, id: &Symbol) -> Option<(&[Generic<Symbol>], Option<&TcType>)>;
    fn find_record(&self, fields: &[Symbol]) -> Option<(&TcType, &TcType)>;
}

impl TypeEnv for () {
    fn find_type(&self, _id: &Symbol) -> Option<&TcType> {
        None
    }
    fn find_type_info(&self, _id: &Symbol) -> Option<(&[Generic<Symbol>], Option<&TcType>)> {
        None
    }
    fn find_record(&self, _fields: &[Symbol]) -> Option<(&TcType, &TcType)> {
        None
    }
}

impl<'a, T: ?Sized + TypeEnv> TypeEnv for &'a T {
    fn find_type(&self, id: &Symbol) -> Option<&TcType> {
        (**self).find_type(id)
    }
    fn find_type_info(&self, id: &Symbol) -> Option<(&[Generic<Symbol>], Option<&TcType>)> {
        (**self).find_type_info(id)
    }
    fn find_record(&self, fields: &[Symbol]) -> Option<(&TcType, &TcType)> {
        (**self).find_record(fields)
    }
}

impl<T: TypeEnv, U: TypeEnv> TypeEnv for (T, U) {
    fn find_type(&self, id: &Symbol) -> Option<&TcType> {
        let &(ref outer, ref inner) = self;
        inner.find_type(id)
             .or_else(|| outer.find_type(id))
    }
    fn find_type_info(&self, id: &Symbol) -> Option<(&[Generic<Symbol>], Option<&TcType>)> {
        let &(ref outer, ref inner) = self;
        inner.find_type_info(id)
             .or_else(|| outer.find_type_info(id))
    }
    fn find_record(&self, fields: &[Symbol]) -> Option<(&TcType, &TcType)> {
        let &(ref outer, ref inner) = self;
        inner.find_record(fields)
             .or_else(|| outer.find_record(fields))
    }
}

pub fn instantiate<F>(typ: TcType, mut f: F) -> TcType
    where F: FnMut(&Generic<Symbol>) -> Option<TcType>
{
    walk_move_type(typ,
                   &mut |typ| {
                       match *typ {
                           Type::Generic(ref x) => f(x),
                           _ => None,
                       }
                   })
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Type<Id, T = ASTType<Id>> {
    App(T, T),
    Data(TypeConstructor<Id>, Vec<T>),
    Variants(Vec<(Id, T)>),
    Variable(TypeVariable),
    Generic(Generic<Id>),
    Function(Vec<T>, T),
    Builtin(BuiltinType),
    Array(T),
    Record {
        types: Vec<Field<Id, Alias<Id, T>>>,
        fields: Vec<Field<Id, T>>,
    },
}

impl<Id, T> Type<Id, T> where T: Deref<Target = Type<Id, T>>
{
    pub fn map<F, R, T2>(&self, mut f: F) -> T2
        where F: FnMut(&Id) -> R,
              T2: From<Type<R, T2>>
    {
        self.map_(&mut f)
    }

    fn map_<R, T2>(&self, f: &mut FnMut(&Id) -> R) -> T2
        where T2: From<Type<R, T2>>
    {
        let typ = match *self {
            Type::Data(ref ctor, ref args) => {
                let ctor = match *ctor {
                    TypeConstructor::Data(ref id) => TypeConstructor::Data(f(id)),
                    TypeConstructor::Builtin(b) => TypeConstructor::Builtin(b),
                };
                Type::Data(ctor, args.iter().map(|t| t.map_(f)).collect())
            }
            Type::Array(ref inner) => Type::Array(inner.map_(f)),
            Type::Function(ref args, ref ret) => {
                Type::Function(args.iter().map(|t| t.map_(f)).collect(), ret.map_(f))
            }
            Type::Record { ref types, ref fields } => {
                let types = types.iter()
                                 .map(|field| {
                                     Field {
                                         name: f(&field.name),
                                         typ: Alias::<R, T2> {
                                             name: f(&field.typ.name),
                                             args: field.typ
                                                        .args
                                                        .iter()
                                                        .map(|g| {
                                                            Generic {
                                                                id: f(&g.id),
                                                                kind: g.kind.clone(),
                                                            }
                                                        })
                                                        .collect(),
                                             typ: field.typ.typ.map_(f),
                                         },
                                     }
                                 })
                                 .collect();
                let fields = fields.iter()
                                   .map(|field| {
                                       Field {
                                           name: f(&field.name),
                                           typ: field.typ.map_(f),
                                       }
                                   })
                                   .collect();
                Type::Record {
                    types: types,
                    fields: fields,
                }
            }
            Type::App(ref l, ref r) => Type::App(l.map_(f), r.map_(f)),
            Type::Variants(ref variants) => {
                Type::Variants(variants.iter()
                                       .map(|t| (f(&t.0), t.1.map_(f)))
                                       .collect())
            }
            Type::Builtin(x) => Type::Builtin(x),
            Type::Variable(ref v) => {
                Type::Variable(TypeVariable {
                    kind: v.kind.clone(),
                    id: v.id,
                })
            }
            Type::Generic(ref g) => {
                Type::Generic(Generic {
                    id: f(&g.id),
                    kind: g.kind.clone(),
                })
            }
        };
        T2::from(typ)
    }

    pub fn is_uninitialized(&self) -> bool {
        match *self {
            Type::Variable(ref id) if id.id == 0 => true,
            _ => false,
        }
    }

    pub fn kind(&self) -> RcKind {
        use self::Type::*;
        match *self {
            App(ref arg, _) => {
                match *arg.kind() {
                    Kind::Function(_, ref ret) => ret.clone(),
                    _ => panic!("Expected function kind"),
                }
            }
            Variable(ref var) => var.kind.clone(),
            Generic(ref gen) => gen.kind.clone(),
            Data(_, _) | Variants(..) | Builtin(_) | Function(_, _) | Array(_) | Record { .. } => {
                RcKind::new(Kind::Star)
            }
        }
    }
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct RcType<Id> {
    typ: Rc<Type<Id, ASTType<Id>>>,
}

impl<Id: fmt::Debug> fmt::Debug for RcType<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<Id: Deref<Target = str>> fmt::Display for RcType<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<Id> Deref for RcType<Id> {
    type Target = Type<Id, RcType<Id>>;
    fn deref(&self) -> &Type<Id, RcType<Id>> {
        &self.typ
    }
}

impl<Id> RcType<Id> {
    pub fn new(typ: Type<Id, RcType<Id>>) -> RcType<Id> {
        RcType { typ: Rc::new(typ) }
    }
}

impl<Id: Clone> RcType<Id> {
    pub fn into_inner(self) -> Type<Id, RcType<Id>> {
        (*self.typ).clone()
    }
}

impl<Id> From<Type<Id, RcType<Id>>> for RcType<Id> {
    fn from(typ: Type<Id, RcType<Id>>) -> RcType<Id> {
        RcType::new(typ)
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub enum BuiltinType {
    String,
    Char,
    Int,
    Float,
    Bool,
    Unit,
    Function,
}

impl ::std::str::FromStr for BuiltinType {
    type Err = ();
    fn from_str(x: &str) -> Result<BuiltinType, ()> {
        let t = match x {
            "Int" => BuiltinType::Int,
            "Float" => BuiltinType::Float,
            "String" => BuiltinType::String,
            "Char" => BuiltinType::Char,
            "Bool" => BuiltinType::Bool,
            _ => return Err(()),
        };
        Ok(t)
    }
}

impl BuiltinType {
    pub fn to_str(self) -> &'static str {
        match self {
            BuiltinType::String => "String",
            BuiltinType::Char => "Char",
            BuiltinType::Int => "Int",
            BuiltinType::Float => "Float",
            BuiltinType::Bool => "Bool",
            BuiltinType::Unit => "()",
            BuiltinType::Function => "->",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum TypeConstructor<Id> {
    Data(Id),
    Builtin(BuiltinType),
}

impl<I: fmt::Display> fmt::Display for TypeConstructor<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            TypeConstructor::Data(ref d) => d.fmt(f),
            TypeConstructor::Builtin(b) => b.fmt(f),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Kind {
    Variable(u32),
    Star,
    Function(RcKind, RcKind),
}

impl Kind {
    pub fn variable(v: u32) -> RcKind {
        RcKind::new(Kind::Variable(v))
    }
    pub fn star() -> RcKind {
        RcKind(Rc::new(Kind::Star))
    }
    pub fn function(l: RcKind, r: RcKind) -> RcKind {
        RcKind(Rc::new(Kind::Function(l, r)))
    }
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct RcKind(Rc<Kind>);

impl Deref for RcKind {
    type Target = Kind;
    fn deref(&self) -> &Kind {
        &self.0
    }
}

impl fmt::Debug for RcKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::Display for RcKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl RcKind {
    pub fn new(k: Kind) -> RcKind {
        RcKind(Rc::new(k))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct TypeVariable {
    pub kind: RcKind,
    pub id: u32,
}
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Generic<Id> {
    pub kind: RcKind,
    pub id: Id,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Alias<Id, T> {
    pub name: Id,
    pub args: Vec<Generic<Id>>,
    pub typ: T,
}

#[derive(Clone, Hash, Eq, PartialEq, Debug)]
pub struct Field<Id, T = ASTType<Id>> {
    pub name: Id,
    pub typ: T,
}

#[derive(Clone, PartialEq, Debug)]
pub enum ConstructorType<Id> {
    Tuple(Vec<ASTType<Id>>),
    Record(Vec<Field<Id>>),
}

impl<Id> ConstructorType<Id> {
    pub fn each_type<F>(&self, mut f: F)
        where F: FnMut(&Type<Id>)
    {
        match *self {
            ConstructorType::Tuple(ref args) => {
                for t in args.iter() {
                    f(t);
                }
            }
            ConstructorType::Record(ref fields) => {
                for field in fields.iter() {
                    f(&field.typ);
                }
            }
        }
    }
    pub fn len(&self) -> usize {
        match *self {
            ConstructorType::Tuple(ref args) => args.len(),
            ConstructorType::Record(ref fields) => fields.len(),
        }
    }
}

pub fn type_con<I, T>(s: I, args: Vec<T>) -> Type<I, T>
    where I: Deref<Target = str>
{
    assert!(s.len() != 0);
    let is_var = s.chars().next().unwrap().is_lowercase();
    match s.parse() {
        Ok(b) => Type::Builtin(b),
        Err(()) if is_var => {
            Type::Generic(Generic {
                kind: RcKind::new(Kind::Star),
                id: s,
            })
        }
        Err(()) => Type::Data(TypeConstructor::Data(s), args),
    }
}

impl<Id, T> Type<Id, T> where T: From<Type<Id, T>>
{
    pub fn app(l: T, r: T) -> T {
        T::from(Type::App(l, r))
    }

    pub fn array(typ: T) -> T {
        T::from(Type::Array(typ))
    }

    pub fn data(id: TypeConstructor<Id>, args: Vec<T>) -> T {
        T::from(Type::Data(id, args))
    }

    pub fn variants(vs: Vec<(Id, T)>) -> T {
        T::from(Type::Variants(vs))
    }

    pub fn record(types: Vec<Field<Id, Alias<Id, T>>>, fields: Vec<Field<Id, T>>) -> T {
        T::from(Type::Record {
            types: types,
            fields: fields,
        })
    }

    pub fn function(args: Vec<T>, ret: T) -> T {
        args.into_iter()
            .rev()
            .fold(ret, |body, arg| T::from(Type::Function(vec![arg], body)))
    }

    pub fn generic(typ: Generic<Id>) -> T {
        T::from(Type::Generic(typ))
    }

    pub fn builtin(typ: BuiltinType) -> T {
        T::from(Type::Builtin(typ))
    }

    pub fn variable(typ: TypeVariable) -> T {
        T::from(Type::Variable(typ))
    }

    pub fn string() -> T {
        Type::builtin(BuiltinType::String)
    }

    pub fn char() -> T {
        Type::builtin(BuiltinType::Char)
    }

    pub fn int() -> T {
        Type::builtin(BuiltinType::Int)
    }

    pub fn float() -> T {
        Type::builtin(BuiltinType::Float)
    }

    pub fn bool() -> T {
        Type::builtin(BuiltinType::Bool)
    }

    pub fn unit() -> T {
        Type::builtin(BuiltinType::Unit)
    }
}

pub struct ArgIterator<'a, T: 'a> {
    pub typ: &'a T,
}

pub fn arg_iter<Id, T>(typ: &T) -> ArgIterator<T>
    where T: Deref<Target = Type<Id, T>>
{
    ArgIterator { typ: typ }
}

impl<'a, Id, T> Iterator for ArgIterator<'a, T>
    where Id: 'a,
          T: Deref<Target = Type<Id, T>>
{
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> {
        match **self.typ {
            Type::Function(ref arg, ref return_type) => {
                self.typ = return_type;
                Some(&arg[0])
            }
            _ => None,
        }
    }
}

impl<Id> RcType<Id> {
    pub fn return_type(&self) -> &RcType<Id> {
        match **self {
            Type::Function(_, ref return_type) => return_type.return_type(),
            _ => self,
        }
    }

    ///Returns the inner most application of a type application
    pub fn inner_app(&self) -> &RcType<Id> {
        match **self {
            Type::App(ref a, _) => a.inner_app(),
            _ => self,
        }
    }

    pub fn level(&self) -> u32 {
        use std::cmp::min;
        fold_type(self,
                  |typ, level| {
                      match **typ {
                          Type::Variable(ref var) => min(var.id, level),
                          _ => level,
                      }
                  },
                  u32::max_value())
    }
}

impl TypeVariable {
    pub fn new(var: u32) -> TypeVariable {
        TypeVariable::with_kind(Kind::Star, var)
    }
    pub fn with_kind(kind: Kind, var: u32) -> TypeVariable {
        TypeVariable {
            kind: RcKind::new(kind),
            id: var,
        }
    }
}

struct DisplayKind<'a>(Prec, &'a Kind);

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", DisplayKind(Prec::Top, self))
    }
}
impl<'a> fmt::Display for DisplayKind<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self.1 {
            Kind::Variable(i) => i.fmt(f),
            Kind::Star => '*'.fmt(f),
            Kind::Function(ref arg, ref ret) => {
                match self.0 {
                    Prec::Function => write!(f, "({} -> {})", DisplayKind(Prec::Function, arg), ret),
                    Prec::Top | Prec::Constructor => write!(f, "{} -> {}", DisplayKind(Prec::Function, arg), ret)
                }
            }
        }
    }
}

impl fmt::Display for TypeVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.id.fmt(f)
    }
}

impl<Id: fmt::Display> fmt::Display for Generic<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.id.fmt(f)
    }
}

impl fmt::Display for BuiltinType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.to_str().fmt(f)
    }
}

fn dt<'a, I, T, E>(env: &'a E, prec: Prec, typ: &'a Type<I, T>) -> DisplayType<'a, I, T, E> {
    DisplayType {
        env: env,
        prec: prec,
        typ: typ,
    }
}

fn top<'a, I, T, E>(env: &'a E, typ: &'a Type<I, T>) -> DisplayType<'a, I, T, E> {
    dt(env, Prec::Top, typ)
}

pub fn display_type<'a, I, T, E>(env: &'a E, typ: &'a Type<I, T>) -> DisplayType<'a, I, T, E> {
    top(env, typ)
}

pub struct DisplayType<'a, I: 'a, T: 'a, E: 'a> {
    prec: Prec,
    typ: &'a Type<I, T>,
    env: &'a E,
}

impl<'a, I, T, E> fmt::Display for DisplayType<'a, I, T, E>
    where E: DisplayEnv<Ident = I> + 'a,
          T: Deref<Target = Type<I, T>> + 'a
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let p = self.prec;
        match *self.typ {
            Type::Variable(ref var) => write!(f, "{}", var),
            Type::Generic(ref gen) => write!(f, "{}", self.env.string(&gen.id)),
            Type::Function(ref args, ref result) => {
                if p >= Prec::Function {
                    write!(f,
                           "({} -> {})",
                           top(self.env, &*args[0]),
                           top(self.env, &**result))
                } else {
                    write!(f,
                           "{} -> {}",
                           dt(self.env, Prec::Function, &args[0]),
                           top(self.env, &**result))
                }
            }
            Type::App(ref lhs, ref rhs) => {
                if p >= Prec::Constructor {
                    write!(f,
                           "({} {})",
                           dt(self.env, Prec::Function, &lhs),
                           dt(self.env, Prec::Constructor, &rhs))
                } else {
                    write!(f,
                           "{} {}",
                           dt(self.env, Prec::Function, &lhs),
                           dt(self.env, Prec::Constructor, &rhs))
                }
            }
            Type::Data(ref t, ref args) => {
                if p >= Prec::Constructor {
                    try!(write!(f, "("));
                }
                match *t {
                    TypeConstructor::Data(ref d) => try!(write!(f, "{}", self.env.string(d))),
                    TypeConstructor::Builtin(ref b) => try!(write!(f, "{}", b)),
                }
                for arg in args {
                    try!(write!(f, " {}", dt(self.env, Prec::Constructor, arg)));
                }
                if p >= Prec::Constructor {
                    try!(write!(f, ")"));
                }
                Ok(())
            }
            Type::Variants(ref variants) => {
                if p >= Prec::Constructor {
                    try!(write!(f, "("));
                }
                for variant in variants {
                    try!(write!(f, "| {}", self.env.string(&variant.0)));
                    for arg in arg_iter(&variant.1) {
                        try!(write!(f, " {}", dt(self.env, Prec::Constructor, &arg)));
                    }
                }
                if p >= Prec::Constructor {
                    try!(write!(f, ")"));
                }
                Ok(())
            }
            Type::Builtin(ref t) => t.fmt(f),
            Type::Array(ref t) => write!(f, "[{}]", top(self.env, &**t)),
            Type::Record { ref types, ref fields } => {
                try!(write!(f, "{{"));
                if types.len() > 0 {
                    try!(write!(f, " {} ", self.env.string(&types[0].name)));
                    for arg in &types[0].typ.args {
                        try!(write!(f, "{} ", self.env.string(&arg.id)));
                    }
                    try!(write!(f, "= {}", top(self.env, &*types[0].typ.typ)));
                    for field in &types[1..] {
                        try!(write!(f, " {} ", self.env.string(&field.name)));
                        for arg in &field.typ.args {
                            try!(write!(f, "{} ", self.env.string(&arg.id)));
                        }
                        try!(write!(f, "= {}", top(self.env, &*field.typ.typ)));
                    }
                    if fields.len() == 0 {
                        try!(write!(f, " "));
                    }
                }
                if fields.len() > 0 {
                    if types.len() > 0 {
                        try!(write!(f, ","));
                    }
                    try!(write!(f,
                                " {}: {}",
                                self.env.string(&fields[0].name),
                                top(self.env, &*fields[0].typ)));
                    for field in &fields[1..] {
                        try!(write!(f,
                                    ", {}: {}",
                                    self.env.string(&field.name),
                                    top(self.env, &*field.typ)));
                    }
                    try!(write!(f, " "));
                }
                write!(f, "}}")
            }
        }
    }
}

#[derive(PartialEq, Copy, Clone, PartialOrd)]
enum Prec {
    Top,
    Function,
    Constructor,
}

impl<I, T> fmt::Display for Type<I, T>
    where I: Deref<Target = str>,
          T: Deref<Target = Type<I, T>>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", dt(&ast::EmptyEnv::new(), Prec::Top, self))
    }
}

pub fn walk_type<'t, I: 't, T, F>(typ: &'t T, f: &mut F)
    where F: FnMut(&'t T) -> &'t T,
          T: Deref<Target = Type<I, T>>
{
    let typ = f(typ);
    match **typ {
        Type::Data(_, ref args) => {
            for a in args {
                walk_type(a, f);
            }
        }
        Type::Array(ref inner) => {
            walk_type(inner, f);
        }
        Type::Function(ref args, ref ret) => {
            for a in args {
                walk_type(a, f);
            }
            walk_type(ret, f);
        }
        Type::Record { ref types, ref fields } => {
            for field in types {
                walk_type(&field.typ.typ, f);
            }
            for field in fields {
                walk_type(&field.typ, f);
            }
        }
        Type::App(ref l, ref r) => {
            walk_type(l, f);
            walk_type(r, f);
        }
        Type::Variants(ref variants) => {
            for variant in variants {
                walk_type(&variant.1, f);
            }
        }
        Type::Builtin(_) | Type::Variable(_) | Type::Generic(_) => (),
    }
}

pub fn fold_type<I, T, F, A>(typ: &T, mut f: F, a: A) -> A
    where F: FnMut(&T, A) -> A,
          T: Deref<Target = Type<I, T>>
{
    let mut a = Some(a);
    walk_type(typ,
              &mut |t| {
                  a = Some(f(t, a.take().expect("None in fold_type")));
                  t
              });
    a.expect("fold_type")
}

pub fn walk_move_type<F, I, T>(typ: T, f: &mut F) -> T
    where F: FnMut(&Type<I, T>) -> Option<T>,
          T: Deref<Target = Type<I, T>> + From<Type<I, T>> + Clone,
          I: Clone
{
    walk_move_type2(&typ, f).unwrap_or(typ)
}

/// Merges two values using `f` if either or both them is `Some(..)`.
/// If both are `None`, `None` is returned.
pub fn merge<F, A, B, R>(a_original: &A,
                         a: Option<A>,
                         b_original: &B,
                         b: Option<B>,
                         f: F)
                         -> Option<R>
    where A: Clone,
          B: Clone,
          F: FnOnce(A, B) -> R
{
    match (a, b) {
        (Some(a), Some(b)) => Some(f(a, b)),
        (Some(a), None) => Some(f(a, b_original.clone())),
        (None, Some(b)) => Some(f(a_original.clone(), b)),
        (None, None) => None,
    }
}

fn walk_move_type2<F, I, T>(typ: &Type<I, T>, f: &mut F) -> Option<T>
    where F: FnMut(&Type<I, T>) -> Option<T>,
          T: Deref<Target = Type<I, T>> + From<Type<I, T>> + Clone,
          I: Clone
{
    let new = f(typ);
    let result = {
        let typ = new.as_ref().map(|t| &**t).unwrap_or(typ);
        match *typ {
            Type::Data(ref id, ref args) => {
                walk_move_types(args.iter(), |t| walk_move_type2(t, f))
                    .map(|args| Type::Data(id.clone(), args))
                    .map(From::from)
            }
            Type::Array(ref inner) => {
                walk_move_type2(&**inner, f)
                    .map(Type::Array)
                    .map(From::from)
            }
            Type::Function(ref args, ref ret) => {
                let new_args = walk_move_types(args.iter(), |t| walk_move_type2(t, f));
                merge(args, new_args, ret, walk_move_type2(ret, f), Type::Function).map(From::from)
            }
            Type::Record { ref types, ref fields } => {
                let new_types = None;
                let new_fields = walk_move_types(fields.iter(), |field| {
                    walk_move_type2(&field.typ, f).map(|typ| {
                        Field {
                            name: field.name.clone(),
                            typ: typ,
                        }
                    })
                });
                merge(types, new_types, fields, new_fields, |types, fields| {
                    Type::Record {
                        types: types,
                        fields: fields,
                    }
                })
                    .map(From::from)
            }
            Type::App(ref l, ref r) => {
                merge(l,
                      walk_move_type2(l, f),
                      r,
                      walk_move_type2(r, f),
                      Type::App)
                    .map(From::from)
            }
            Type::Variants(ref variants) => {
                walk_move_types(variants.iter(),
                                |v| walk_move_type2(&v.1, f).map(|t| (v.0.clone(), t)))
                    .map(Type::Variants)
                    .map(From::from)
            }
            Type::Builtin(_) | Type::Variable(_) | Type::Generic(_) => None,
        }
    };
    result.or(new)
}
fn walk_move_types<'a, I, F, T>(types: I, mut f: F) -> Option<Vec<T>>
    where I: Iterator<Item = &'a T>,
          F: FnMut(&'a T) -> Option<T>,
          T: Clone + 'a
{
    let mut out = Vec::new();
    walk_move_types2(types, false, &mut out, &mut f);
    if out.len() == 0 {
        None
    } else {
        out.reverse();
        Some(out)
    }
}
fn walk_move_types2<'a, I, F, T>(mut types: I, replaced: bool, output: &mut Vec<T>, f: &mut F)
    where I: Iterator<Item = &'a T>,
          F: FnMut(&'a T) -> Option<T>,
          T: Clone + 'a
{
    match types.next() {
        Some(typ) => {
            let new = f(typ);
            walk_move_types2(types, replaced || new.is_some(), output, f);
            match new {
                Some(typ) => {
                    output.push(typ);
                }
                None if replaced || output.len() > 0 => {
                    output.push(typ.clone());
                }
                None => (),
            }
        }
        None => (),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use ast::ASTType;

    #[test]
    fn show_record() {
        assert_eq!(format!("{}", Type::<&str, ASTType<&str>>::record(vec![], vec![])), "{}");
        let typ = Type::record(vec![],
                               vec![Field {
                                        name: "x",
                                        typ: Type::<&str, ASTType<&str>>::int(),
                                    }]);
        assert_eq!(format!("{}", typ), "{ x: Int }");

        let data = |s, a| RcType::from(type_con(s, a));
        let f = Type::function(vec![data("a", vec![])], Type::string());
        let test = data("Test", vec![data("a", vec![])]);
        let typ = Type::record(vec![Field {
                                        name: "Test",
                                        typ: Alias {
                                            name: "Test",
                                            args: vec![Generic {
                                                           kind: Kind::star(),
                                                           id: "a",
                                                       }],
                                            typ: f.clone(),
                                        },
                                    }],
                               vec![Field {
                                        name: "x",
                                        typ: Type::int(),
                                    }]);
        assert_eq!(format!("{}", typ), "{ Test a = a -> String, x: Int }");
        let typ = Type::record(vec![Field {
                                        name: "Test",
                                        typ: Alias {
                                            name: "Test",
                                            args: vec![Generic {
                                                           kind: Kind::star(),
                                                           id: "a",
                                                       }],
                                            typ: f.clone(),
                                        },
                                    }],
                               vec![Field {
                                        name: "x",
                                        typ: Type::int(),
                                    },
                                    Field {
                                        name: "test",
                                        typ: test.clone(),
                                    }]);
        assert_eq!(format!("{}", typ),
                   "{ Test a = a -> String, x: Int, test: Test a }");
        let typ = Type::record(vec![Field {
                                        name: "Test",
                                        typ: Alias {
                                            name: "Test",
                                            args: vec![Generic {
                                                           kind: Kind::star(),
                                                           id: "a",
                                                       }],
                                            typ: f.clone(),
                                        },
                                    }],
                               vec![]);
        assert_eq!(format!("{}", typ), "{ Test a = a -> String }");
    }

    #[test]
    fn show_kind() {
        let two_args = Kind::function(Kind::star(), Kind::function(Kind::star(), Kind::star()));
        assert_eq!(format!("{}", two_args), "* -> * -> *");
        let function_arg = Kind::function(Kind::function(Kind::star(), Kind::star()), Kind::star());
        assert_eq!(format!("{}", function_arg), "(* -> *) -> *");
    }
}
