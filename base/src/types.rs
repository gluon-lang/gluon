//! Module containing types representing `gluon`'s type system
use std::fmt;
use std::ops::Deref;
use std::sync::Arc;
use std::marker::PhantomData;
use std::rc::Rc;

use ast;
use ast::{ASTType, DisplayEnv};
use symbol::Symbol;

pub type TcType = ast::ASTType<Symbol>;
pub type TcIdent = ast::TcIdent<Symbol>;

/// Trait for values which contains kinded values which can be refered by name
pub trait KindEnv {
    /// Returns the kind of the type `type_name`
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

/// Trait for values which contains typed values which can be refered by name
pub trait TypeEnv: KindEnv {
    /// Returns the type of the value bound at `id`
    fn find_type(&self, id: &Symbol) -> Option<&TcType>;
    /// Returns information about the type `id`
    fn find_type_info(&self, id: &Symbol) -> Option<&Alias<Symbol, TcType>>;
    /// Returns a record which contains all `fields`. The first element is the record type and the
    /// second is the alias type.
    fn find_record(&self, fields: &[Symbol]) -> Option<(&TcType, &TcType)>;
}

impl TypeEnv for () {
    fn find_type(&self, _id: &Symbol) -> Option<&TcType> {
        None
    }
    fn find_type_info(&self, _id: &Symbol) -> Option<&Alias<Symbol, TcType>> {
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
    fn find_type_info(&self, id: &Symbol) -> Option<&Alias<Symbol, TcType>> {
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
    fn find_type_info(&self, id: &Symbol) -> Option<&Alias<Symbol, TcType>> {
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

/// Trait which is a `TypeEnv` which also provides access to the type representation of some
/// primitive types
pub trait PrimitiveEnv: TypeEnv {
    fn get_bool(&self) -> &TcType;
}

impl<'a, T: ?Sized + PrimitiveEnv> PrimitiveEnv for &'a T {
    fn get_bool(&self) -> &TcType {
        (**self).get_bool()
    }
}

impl<'a, T: PrimitiveEnv, U: TypeEnv> PrimitiveEnv for (T, U) {
    fn get_bool(&self) -> &TcType {
        self.0.get_bool()
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

/// The representation of gluon's types.
///
/// For efficency this enum is not stored directly but instead a pointer wrapper which derefs to
/// `Type` is used to enable types to be shared. It is recommended to use the static functions on
/// `Type` such as `Type::app` and `Type::record` when constructing types as those will construct
/// the pointer wrapper directly.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Type<Id, T = ASTType<Id>> {
    /// An application which applies the first argument on the second.
    /// `Option Int` would be represented as `App(Option, Int)`
    App(T, T),
    /// An application with multiple arguments
    Data(T, Vec<T>),
    /// A variant type `| A Int Float | B`.
    /// The second element of the tuple is the function type which the constructor has which in the
    /// above example means that A's type is `Int -> Float -> A` and B's is `B`
    Variants(Vec<(Id, T)>),
    /// Representation for type variables
    Variable(TypeVariable),
    /// Variant for "generic" variables. These occur in signatures as lowercase identifers `a`, `b`
    /// etc and are what unbound type variables are eventually made into.
    Generic(Generic<Id>),
    /// A function type `<type> -> <type>`
    Function(Vec<T>, T),
    /// A builtin type
    Builtin(BuiltinType),
    /// An array type `Array T`
    Array(T),
    /// A record type
    Record {
        /// The associated types of this record type
        types: Vec<Field<Id, Alias<Id, T>>>,
        /// The fields of this record type
        fields: Vec<Field<Id, T>>,
    },
    /// An identifier type. Anything which is not a builting type.
    Id(Id),
    Alias(AliasData<Id, T>),
}

impl<Id, T> Type<Id, T>
    where T: Deref<Target = Type<Id, T>>
{
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
            Data(_, _) | Variants(..) | Builtin(_) | Function(_, _) | Array(_) |
            Record { .. } | Type::Id(_) | Type::Alias(_) => RcKind::new(Kind::Star),
        }
    }
}

/// A shared type which is atomically reference counted
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct ArcType<Id> {
    typ: Arc<Type<Id, ArcType<Id>>>,
}

impl<Id: fmt::Debug> fmt::Debug for ArcType<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<Id: AsRef<str>> fmt::Display for ArcType<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<Id> Deref for ArcType<Id> {
    type Target = Type<Id, ArcType<Id>>;
    fn deref(&self) -> &Type<Id, ArcType<Id>> {
        &self.typ
    }
}

impl<Id> ArcType<Id> {
    pub fn new(typ: Type<Id, ArcType<Id>>) -> ArcType<Id> {
        ArcType { typ: Arc::new(typ) }
    }
}

impl<Id: Clone> ArcType<Id> {
    pub fn into_inner(self) -> Type<Id, ArcType<Id>> {
        (*self.typ).clone()
    }
}

impl<Id> From<Type<Id, ArcType<Id>>> for ArcType<Id> {
    fn from(typ: Type<Id, ArcType<Id>>) -> ArcType<Id> {
        ArcType::new(typ)
    }
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct RcType<Id> {
    typ: Rc<Type<Id, RcType<Id>>>,
}

impl<Id: fmt::Debug> fmt::Debug for RcType<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<Id: AsRef<str>> fmt::Display for RcType<Id> {
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

/// All the builtin types of gluon
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub enum BuiltinType {
    String,
    Char,
    Int,
    Float,
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
            BuiltinType::Unit => "()",
            BuiltinType::Function => "->",
        }
    }
}

/// Kind representation
///
/// All types in gluon has a kind. Most types encountered are of the `Star` (*) kind which
/// includes things like `Int`, `String` and `Option Int`. There are however other types which
/// are said to be "higher kinded" and these use the `Function` (a -> b) variant.
/// These types include `Option` and `->` which both have the kind `* -> *` as well as `Functor`
/// which has the kind `(* -> *) -> *`.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Kind {
    /// Representation for a kind which is yet to be infered
    Variable(u32),
    /// The simplest possible kind. All values in a program have this kind.
    Star,
    /// Constructor which takes two kinds, taking the first as argument and returning the second
    Function(RcKind, RcKind),
}

impl Kind {
    pub fn variable(v: u32) -> RcKind {
        RcKind::new(Kind::Variable(v))
    }
    pub fn star() -> RcKind {
        RcKind::new(Kind::Star)
    }
    pub fn function(l: RcKind, r: RcKind) -> RcKind {
        RcKind::new(Kind::Function(l, r))
    }
}

/// Reference counted kind type.
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct RcKind(Arc<Kind>);

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
        RcKind(Arc::new(k))
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
    _typ: T,
    _marker: PhantomData<Id>,
}

impl<Id, T> Deref for Alias<Id, T>
    where T: Deref<Target = Type<Id, T>>
{
    type Target = AliasData<Id, T>;
    fn deref(&self) -> &AliasData<Id, T> {
        match *self._typ {
            Type::Alias(ref alias) => alias,
            _ => unreachable!(),
        }
    }
}

impl<Id, T> From<AliasData<Id, T>> for Alias<Id, T>
    where T: From<Type<Id, T>>
{
    fn from(data: AliasData<Id, T>) -> Alias<Id, T> {
        Alias {
            _typ: T::from(Type::Alias(data)),
            _marker: PhantomData,
        }
    }
}

impl<Id, T> AsRef<T> for Alias<Id, T> {
    fn as_ref(&self) -> &T {
        &self._typ
    }
}

impl<Id, T> Alias<Id, T>
    where T: From<Type<Id, T>>
{
    pub fn new(name: Id, args: Vec<Generic<Id>>, typ: T) -> Alias<Id, T> {
        Alias {
            _typ: Type::alias(name, args, typ),
            _marker: PhantomData,
        }
    }

    pub fn into_type(self) -> T {
        self._typ
    }
}

impl<Id> Alias<Id, ASTType<Id>>
    where Id: Clone
{
    pub fn make_mut(alias: &mut Alias<Id, ASTType<Id>>) -> &mut AliasData<Id, ASTType<Id>> {
        match *Arc::make_mut(&mut alias._typ.typ) {
            Type::Alias(ref mut alias) => alias,
            _ => unreachable!(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct AliasData<Id, T> {
    /// Name of the Alias
    pub name: Id,
    /// Arguments to the alias
    pub args: Vec<Generic<Id>>,
    /// The type which is being aliased or `None` if the type is abstract
    pub typ: Option<T>,
}

#[derive(Clone, Hash, Eq, PartialEq, Debug)]
pub struct Field<Id, T = ASTType<Id>> {
    pub name: Id,
    pub typ: T,
}

impl<Id, T> Type<Id, T>
    where T: From<Type<Id, T>>
{
    pub fn app(l: T, r: T) -> T {
        T::from(Type::App(l, r))
    }

    pub fn array(typ: T) -> T {
        T::from(Type::Array(typ))
    }

    pub fn data(id: T, args: Vec<T>) -> T {
        if args.is_empty() {
            id
        } else {
            T::from(Type::Data(id, args))
        }
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

    pub fn alias(name: Id, args: Vec<Generic<Id>>, typ: T) -> T {
        T::from(Type::Alias(AliasData {
            name: name,
            args: args,
            typ: Some(typ),
        }))
    }

    pub fn id(id: Id) -> T {
        T::from(Type::Id(id))
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

    pub fn unit() -> T {
        Type::builtin(BuiltinType::Unit)
    }
}

impl<Id, T> Type<Id, T>
    where T: Deref<Target = Type<Id, T>>
{
    pub fn as_alias(&self) -> Option<(&Id, &[T])> {
        match *self {
            Type::Data(ref id, ref args) => {
                match **id {
                    Type::Id(ref id) => Some((id, args)),
                    Type::Alias(ref alias) => Some((&alias.name, args)),
                    _ => None,
                }
            }
            Type::Id(ref id) => Some((id, &[][..])),
            Type::Alias(ref alias) => Some((&alias.name, &[][..])),
            _ => None,
        }
    }
}

pub struct ArgIterator<'a, T: 'a> {
    /// The current type being iterated over. After `None` has been returned this is the return
    /// type.
    pub typ: &'a T,
}

/// Constructs an iterator over a functions arguments
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

impl<Id> ASTType<Id> {
    /// Returns the type which this type would return if it was fully applied.
    pub fn return_type(&self) -> &ASTType<Id> {
        match **self {
            Type::Function(_, ref return_type) => return_type.return_type(),
            _ => self,
        }
    }

    ///Returns the inner most application of a type application
    pub fn inner_app(&self) -> &ASTType<Id> {
        match **self {
            Type::App(ref a, _) => a.inner_app(),
            _ => self,
        }
    }

    /// Returns the lowest level which this type contains. The level informs from where type
    /// variables where created.
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
                    Prec::Function => {
                        write!(f, "({} -> {})", DisplayKind(Prec::Function, arg), ret)
                    }
                    Prec::Top | Prec::Constructor => {
                        write!(f, "{} -> {}", DisplayKind(Prec::Function, arg), ret)
                    }
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
                try!(write!(f, "{}", dt(self.env, Prec::Top, t)));
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
                let mut first = true;
                for variant in variants {
                    if !first {
                        try!(write!(f, " "));
                    }
                    first = false;
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
                if !types.is_empty() {
                    try!(write!(f, " {} ", self.env.string(&types[0].name)));
                    for arg in &types[0].typ.args {
                        try!(write!(f, "{} ", self.env.string(&arg.id)));
                    }
                    match types[0].typ.typ {
                        Some(ref typ) => try!(write!(f, "= {}", top(self.env, typ))),
                        None => try!(write!(f, "= <abstract>")),
                    }
                    for field in &types[1..] {
                        try!(write!(f, " {} ", self.env.string(&field.name)));
                        for arg in &field.typ.args {
                            try!(write!(f, "{} ", self.env.string(&arg.id)));
                        }
                        match field.typ.typ {
                            Some(ref typ) => try!(write!(f, "= {}", top(self.env, typ))),
                            None => try!(write!(f, "= <abstract>")),
                        }
                    }
                    if fields.is_empty() {
                        try!(write!(f, " "));
                    }
                }
                if !fields.is_empty() {
                    if !types.is_empty() {
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
            Type::Id(ref id) => write!(f, "{}", self.env.string(id)),
            Type::Alias(ref alias) => write!(f, "{}", self.env.string(&alias.name)),
        }
    }
}

#[derive(PartialEq, Copy, Clone, PartialOrd)]
enum Prec {
    /// The type exists in the top context, no parentheses needed.
    Top,
    /// The type exists in a function argument `Type -> a`, parentheses are needed if the type is a
    /// function `(b -> c) -> a`
    Function,
    /// The type exists in a constructor argument `Option Type`, parentheses are needed for
    /// functions or other constructors `Option (a -> b)` `Option (Result a b)`
    Constructor,
}

impl<I, T> fmt::Display for Type<I, T>
    where I: AsRef<str>,
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
                if let Some(ref typ) = field.typ.typ {
                    walk_type(typ, f);
                }
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
        Type::Builtin(_) |
        Type::Variable(_) |
        Type::Generic(_) |
        Type::Id(_) |
        Type::Alias(_) => (),
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

/// Walks through a type calling `f` on each inner type. If `f` return `Some` the type is replaced.
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
        let typ = new.as_ref().map_or(typ, |t| &**t);
        match *typ {
            Type::Data(ref id, ref args) => {
                let new_args = walk_move_types(args.iter(), |t| walk_move_type2(t, f));
                merge(id, walk_move_type2(id, f), args, new_args, Type::data)
            }
            Type::Array(ref inner) => walk_move_type2(&**inner, f).map(Type::array),
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
            Type::Builtin(_) |
            Type::Variable(_) |
            Type::Generic(_) |
            Type::Id(_) |
            Type::Alias(_) => None,
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
    if out.is_empty() {
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
    if let Some(typ) = types.next() {
        let new = f(typ);
        walk_move_types2(types, replaced || new.is_some(), output, f);
        match new {
            Some(typ) => {
                output.push(typ);
            }
            None if replaced || !output.is_empty() => {
                output.push(typ.clone());
            }
            None => (),
        }
    }
}
