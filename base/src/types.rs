use std::borrow::Cow;
use std::fmt;
use std::ops::{Deref, DerefMut};
use std::sync::Arc;
use std::marker::PhantomData;

use pretty::{DocAllocator, Arena, DocBuilder};

use smallvec::{SmallVec, VecLike};

use ast::{self, DisplayEnv};
use kind::{ArcKind, Kind, KindEnv};
use merge::merge;
use symbol::{Symbol, SymbolRef};

/// Trait for values which contains typed values which can be refered by name
pub trait TypeEnv: KindEnv {
    /// Returns the type of the value bound at `id`
    fn find_type(&self, id: &SymbolRef) -> Option<&ArcType>;

    /// Returns information about the type `id`
    fn find_type_info(&self, id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>>;

    /// Returns a record which contains all `fields`. The first element is the record type and the
    /// second is the alias type.
    fn find_record(&self, fields: &[Symbol]) -> Option<(ArcType, ArcType)>;
}

impl<'a, T: ?Sized + TypeEnv> TypeEnv for &'a T {
    fn find_type(&self, id: &SymbolRef) -> Option<&ArcType> {
        (**self).find_type(id)
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>> {
        (**self).find_type_info(id)
    }

    fn find_record(&self, fields: &[Symbol]) -> Option<(ArcType, ArcType)> {
        (**self).find_record(fields)
    }
}

/// Trait which is a `TypeEnv` which also provides access to the type representation of some
/// primitive types
pub trait PrimitiveEnv: TypeEnv {
    fn get_bool(&self) -> &ArcType;
}

impl<'a, T: ?Sized + PrimitiveEnv> PrimitiveEnv for &'a T {
    fn get_bool(&self) -> &ArcType {
        (**self).get_bool()
    }
}

/// All the builtin types of gluon
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub enum BuiltinType {
    /// Unicode string
    String,
    /// Unsigned byte
    Byte,
    /// Character
    Char,
    /// Integer number
    Int,
    /// Floating point number
    Float,
    /// The unit type
    Unit,
    /// Type constructor for arrays, `Array a : Type -> Type`
    Array,
    /// Type constructor for functions, `(->) a b : Type -> Type -> Type`
    Function,
}

impl BuiltinType {
    pub fn symbol(self) -> &'static SymbolRef {
        unsafe { ::std::mem::transmute::<&'static str, &'static SymbolRef>(self.to_str()) }
    }
}

impl ::std::str::FromStr for BuiltinType {
    type Err = ();
    fn from_str(x: &str) -> Result<BuiltinType, ()> {
        let t = match x {
            "Int" => BuiltinType::Int,
            "Byte" => BuiltinType::Byte,
            "Float" => BuiltinType::Float,
            "String" => BuiltinType::String,
            "Char" => BuiltinType::Char,
            "Array" => BuiltinType::Array,
            "->" => BuiltinType::Function,
            _ => return Err(()),
        };
        Ok(t)
    }
}

impl BuiltinType {
    pub fn to_str(self) -> &'static str {
        match self {
            BuiltinType::String => "String",
            BuiltinType::Byte => "Byte",
            BuiltinType::Char => "Char",
            BuiltinType::Int => "Int",
            BuiltinType::Float => "Float",
            BuiltinType::Unit => "()",
            BuiltinType::Array => "Array",
            BuiltinType::Function => "->",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct TypeVariable {
    pub kind: ArcKind,
    pub id: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Generic<Id> {
    pub id: Id,
    pub kind: ArcKind,
}

impl<Id> Generic<Id> {
    pub fn new(id: Id, kind: ArcKind) -> Generic<Id> {
        Generic {
            id: id,
            kind: kind,
        }
    }
}

/// An alias is wrapper around `Type::Alias`, allowing it to be cheaply converted to a type and dereferenced
/// to `AliasRef`
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Alias<Id, T> {
    _typ: T,
    _marker: PhantomData<Id>,
}

impl<Id, T> Deref for Alias<Id, T>
    where T: Deref<Target = Type<Id, T>>,
{
    type Target = AliasData<Id, T>;

    fn deref(&self) -> &Self::Target {
        match *self._typ {
            Type::Alias(ref alias) => &alias.group[alias.index],
            _ => unreachable!(),
        }
    }
}

impl<Id, T> From<AliasData<Id, T>> for Alias<Id, T>
    where T: From<Type<Id, T>>,
{
    fn from(data: AliasData<Id, T>) -> Alias<Id, T> {
        Alias {
            _typ: Type::alias(data.name, data.args, data.typ),
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
    where T: From<Type<Id, T>>,
{
    pub fn new(name: Id, args: Vec<Generic<Id>>, typ: T) -> Alias<Id, T> {
        Alias {
            _typ: Type::alias(name, args, typ),
            _marker: PhantomData,
        }
    }

    pub fn group(group: Vec<AliasData<Id, T>>) -> Vec<Alias<Id, T>> {
        let group = Arc::new(group);
        (0..group.len())
            .map(|index| {
                Alias {
                    _typ: T::from(Type::Alias(AliasRef {
                        index: index,
                        group: group.clone(),
                    })),
                    _marker: PhantomData,
                }
            })
            .collect()
    }

    pub fn as_type(&self) -> &T {
        &self._typ
    }

    pub fn into_type(self) -> T {
        self._typ
    }
}

impl<Id, T> Alias<Id, T>
    where T: From<Type<Id, T>> + Deref<Target = Type<Id, T>> + Clone,
          Id: Clone + PartialEq,
{
    /// Returns the actual type of the alias
    pub fn typ(&self) -> Cow<T> {
        match *self._typ {
            Type::Alias(ref alias) => alias.typ(),
            _ => unreachable!(),
        }
    }
}

impl<Id> Alias<Id, ArcType<Id>>
    where Id: Clone,
{
    pub fn make_mut(alias: &mut Alias<Id, ArcType<Id>>) -> &mut AliasRef<Id, ArcType<Id>> {
        match *Arc::make_mut(&mut alias._typ.typ) {
            Type::Alias(ref mut alias) => alias,
            _ => unreachable!(),
        }
    }
}

/// Data for a type alias. Probably you want to use `Alias` instead of this directly as Alias allows for
/// cheap conversion back into a type as well.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct AliasRef<Id, T> {
    /// Name of the Alias
    index: usize,
    /// The other aliases defined in this group
    pub group: Arc<Vec<AliasData<Id, T>>>,
}

impl<Id, T> AliasRef<Id, T>
    where T: From<Type<Id, T>> + Deref<Target = Type<Id, T>> + Clone,
          Id: Clone + PartialEq,
{
    pub fn typ(&self) -> Cow<T> {
        let opt = walk_move_type_opt(&self.typ,
                                     &mut |typ: &Type<_, _>| {
            match *typ {
                Type::Ident(ref id) => {
                    // Replace `Ident` with the alias it resolves to so that a `TypeEnv` is not needed
                    // to resolve the type later on
                    let index = self.group
                        .iter()
                        .position(|alias| alias.name == *id)
                        .expect("ICE: Alias group were not able to resolve an identifier");
                    Some(T::from(Type::Alias(AliasRef {
                        index: index,
                        group: self.group.clone(),
                    })))
                }
                _ => None,
            }
        });
        match opt {
            Some(typ) => Cow::Owned(typ),
            None => Cow::Borrowed(&self.typ),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct AliasData<Id, T> {
    pub name: Id,
    /// Arguments to the alias
    pub args: Vec<Generic<Id>>,
    /// The type that is being aliased
    typ: T,
}

impl<Id, T> AliasData<Id, T> {
    pub fn new(name: Id, args: Vec<Generic<Id>>, typ: T) -> AliasData<Id, T> {
        AliasData {
            name: name,
            args: args,
            typ: typ,
        }
    }

    /// Returns the type aliased by `self` with out `Type::Ident` resolved to their actual
    /// `Type::Alias` representation
    pub fn unresolved_type(&self) -> &T {
        &self.typ
    }

    pub fn unresolved_type_mut(&mut self) -> &mut T {
        &mut self.typ
    }
}

impl<Id, T> Deref for AliasRef<Id, T> {
    type Target = AliasData<Id, T>;

    fn deref(&self) -> &Self::Target {
        &self.group[self.index]
    }
}


#[derive(Clone, Hash, Eq, PartialEq, Debug)]
pub struct Field<Id, T = ArcType<Id>> {
    pub name: Id,
    pub typ: T,
}

/// `SmallVec` used in the `Type::App` constructor to avoid alloacting a `Vec` for every applied
/// type. If `Type` is changed in a way that changes its size it is likely a good idea to change
/// the number of elements in the `SmallVec` so that it fills out the entire `Type` enum while not
/// increasing the size of `Type`.
pub type AppVec<T> = SmallVec<[T; 2]>;

impl<Id, T> Field<Id, T> {
    pub fn new(name: Id, typ: T) -> Field<Id, T> {
        Field {
            name: name,
            typ: typ,
        }
    }
}

/// The representation of gluon's types.
///
/// For efficency this enum is not stored directly but instead a pointer wrapper which derefs to
/// `Type` is used to enable types to be shared. It is recommended to use the static functions on
/// `Type` such as `Type::app` and `Type::record` when constructing types as those will construct
/// the pointer wrapper directly.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Type<Id, T = ArcType<Id>> {
    /// An unbound type `_`, awaiting ascription.
    Hole,
    /// An opaque type
    Opaque,
    /// A builtin type
    Builtin(BuiltinType),
    /// A type application with multiple arguments. For example,
    /// `Map String Int` would be represented as `App(Map, [String, Int])`.
    App(T, AppVec<T>),
    /// Record constructor, of kind `Row -> Type`
    Record(T),
    /// Variant constructor, of kind `Row -> Type`
    Variant(T),
    /// The empty row, of kind `Row`
    EmptyRow,
    /// Row extension, of kind `... -> Row -> Row`
    ExtendRow {
        /// The associated types of this record type
        types: Vec<Field<Id, Alias<Id, T>>>,
        /// The fields of this record type
        fields: Vec<Field<Id, T>>,
        /// The rest of the row
        rest: T,
    },
    /// An identifier type. These are created during parsing, but should all be
    /// resolved into `Type::Alias`es during type checking.
    ///
    /// Identifiers are also sometimes used inside aliased types to avoid cycles
    /// in reference counted pointers. This is a bit of a wart at the moment and
    /// _may_ cause spurious unification failures.
    Ident(Id),
    /// An unbound type variable that may be unified with other types. These
    /// will eventually be converted into `Type::Generic`s during generalization.
    Variable(TypeVariable),
    /// A variable that needs to be instantiated with a fresh type variable
    /// when the binding is refered to.
    Generic(Generic<Id>),
    Alias(AliasRef<Id, T>),
}

impl<Id, T> Type<Id, T>
    where T: From<Type<Id, T>>,
{
    pub fn hole() -> T {
        T::from(Type::Hole)
    }

    pub fn opaque() -> T {
        T::from(Type::Opaque)
    }

    pub fn array(typ: T) -> T {
        Type::app(Type::builtin(BuiltinType::Array), collect![typ])
    }

    pub fn app(id: T, args: AppVec<T>) -> T {
        if args.is_empty() {
            id
        } else {
            T::from(Type::App(id, args))
        }
    }

    pub fn variant(fields: Vec<Field<Id, T>>) -> T {
        Type::poly_variant(fields, Type::empty_row())
    }

    pub fn poly_variant(fields: Vec<Field<Id, T>>, rest: T) -> T {
        T::from(Type::Variant(Type::extend_row(Vec::new(), fields, rest)))
    }

    pub fn record(types: Vec<Field<Id, Alias<Id, T>>>, fields: Vec<Field<Id, T>>) -> T {
        Type::poly_record(types, fields, Type::empty_row())
    }

    pub fn poly_record(types: Vec<Field<Id, Alias<Id, T>>>,
                       fields: Vec<Field<Id, T>>,
                       rest: T)
                       -> T {
        T::from(Type::Record(Type::extend_row(types, fields, rest)))
    }

    pub fn extend_row(types: Vec<Field<Id, Alias<Id, T>>>,
                      fields: Vec<Field<Id, T>>,
                      rest: T)
                      -> T {
        if types.is_empty() && fields.is_empty() {
            rest
        } else {
            T::from(Type::ExtendRow {
                types: types,
                fields: fields,
                rest: rest,
            })
        }
    }

    pub fn empty_row() -> T {
        T::from(Type::EmptyRow)
    }

    pub fn function(args: Vec<T>, ret: T) -> T
        where T: Clone,
    {
        let function: T = Type::builtin(BuiltinType::Function);
        args.into_iter()
            .rev()
            .fold(ret,
                  |body, arg| Type::app(function.clone(), collect![arg, body]))
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
        T::from(Type::Alias(AliasRef {
            index: 0,
            group: Arc::new(vec![AliasData {
                                     name: name,
                                     args: args,
                                     typ: typ,
                                 }]),
        }))
    }

    pub fn ident(id: Id) -> T {
        T::from(Type::Ident(id))
    }

    pub fn string() -> T {
        Type::builtin(BuiltinType::String)
    }

    pub fn char() -> T {
        Type::builtin(BuiltinType::Char)
    }

    pub fn byte() -> T {
        Type::builtin(BuiltinType::Byte)
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
    where T: Deref<Target = Type<Id, T>>,
{
    pub fn as_function(&self) -> Option<(&T, &T)> {
        if let Type::App(ref app, ref args) = *self {
            if args.len() == 2 {
                if let Type::Builtin(BuiltinType::Function) = **app {
                    return Some((&args[0], &args[1]));
                }
            }
        }
        None
    }

    pub fn unapplied_args(&self) -> &[T] {
        match *self {
            Type::App(_, ref args) => args,
            _ => &[],
        }
    }

    pub fn alias_ident(&self) -> Option<&Id> {
        match *self {
            Type::App(ref id, _) => id.alias_ident(),
            Type::Ident(ref id) => Some(id),
            Type::Alias(ref alias) => Some(&alias.name),
            _ => None,
        }
    }
}

impl<T> Type<Symbol, T>
    where T: Deref<Target = Type<Symbol, T>>,
{
    /// Returns the name of `self`
    /// Example:
    /// Option a => Option
    /// Int => Int
    pub fn name(&self) -> Option<&SymbolRef> {
        if let Some(id) = self.alias_ident() {
            return Some(&**id);
        }

        match *self {
            Type::App(ref id, _) => {
                match **id {
                    Type::Builtin(b) => Some(b.symbol()),
                    _ => None,
                }
            }
            Type::Builtin(b) => Some(b.symbol()),
            _ => None,
        }
    }
}

/// A shared type which is atomically reference counted
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct ArcType<Id = Symbol> {
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

    /// Returns an iterator over all type fields in a record.
    /// `{ Test, Test2, x, y } => [Test, Test2]`
    pub fn type_field_iter(&self) -> TypeFieldIterator<Self> {
        TypeFieldIterator {
            typ: self,
            current: 0,
        }
    }

    /// Returns an iterator over all fields in a record.
    /// `{ Test, Test2, x, y } => [x, y]`
    pub fn row_iter(&self) -> RowIterator<Self> {
        RowIterator {
            typ: self,
            current: 0,
        }
    }
}

impl<Id> From<Type<Id, ArcType<Id>>> for ArcType<Id> {
    fn from(typ: Type<Id, ArcType<Id>>) -> ArcType<Id> {
        ArcType::new(typ)
    }
}

#[derive(Clone)]
pub struct TypeFieldIterator<'a, T: 'a> {
    typ: &'a T,
    current: usize,
}

impl<'a, Id: 'a, T> Iterator for TypeFieldIterator<'a, T>
    where T: Deref<Target = Type<Id, T>>,
{
    type Item = &'a Field<Id, Alias<Id, T>>;

    fn next(&mut self) -> Option<&'a Field<Id, Alias<Id, T>>> {
        match **self.typ {
            Type::Record(ref row) => {
                self.typ = row;
                self.next()
            }
            Type::ExtendRow { ref types, ref rest, .. } => {
                let current = self.current;
                self.current += 1;
                types.get(current)
                    .or_else(|| {
                        self.current = 0;
                        self.typ = rest;
                        self.next()
                    })
            }
            _ => None,
        }
    }
}

#[derive(Clone)]
pub struct RowIterator<'a, T: 'a> {
    typ: &'a T,
    current: usize,
}

impl<'a, T> RowIterator<'a, T> {
    pub fn current_type(&self) -> &'a T {
        self.typ
    }
}

impl<'a, Id: 'a, T> Iterator for RowIterator<'a, T>
    where T: Deref<Target = Type<Id, T>>,
{
    type Item = &'a Field<Id, T>;

    fn next(&mut self) -> Option<&'a Field<Id, T>> {
        match **self.typ {
            Type::Record(ref row) |
            Type::Variant(ref row) => {
                self.typ = row;
                self.next()
            }
            Type::ExtendRow { ref fields, ref rest, .. } => {
                let current = self.current;
                self.current += 1;
                fields.get(current)
                    .or_else(|| {
                        self.current = 0;
                        self.typ = rest;
                        self.next()
                    })
            }
            _ => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<'a, Id: 'a, T> ExactSizeIterator for RowIterator<'a, T>
    where T: Deref<Target = Type<Id, T>>,
{
    fn len(&self) -> usize {
        let mut typ = self.typ;
        let mut size = 0;
        loop {
            typ = match **typ {
                Type::Record(ref row) |
                Type::Variant(ref row) => row,
                Type::ExtendRow { ref fields, ref rest, .. } => {
                    size += fields.len();
                    rest
                }
                _ => break,
            };
        }
        size
    }
}

pub struct ArgIterator<'a, T: 'a> {
    /// The current type being iterated over. After `None` has been returned this is the return
    /// type.
    pub typ: &'a T,
}

/// Constructs an iterator over a functions arguments
pub fn arg_iter<Id, T>(typ: &T) -> ArgIterator<T>
    where T: Deref<Target = Type<Id, T>>,
{
    ArgIterator { typ: typ }
}

impl<'a, Id, T> Iterator for ArgIterator<'a, T>
    where Id: 'a,
          T: Deref<Target = Type<Id, T>>,
{
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> {
        self.typ.as_function().map(|(arg, ret)| {
            self.typ = ret;
            arg
        })
    }
}

impl<Id> ArcType<Id> {
    /// Returns the lowest level which this type contains. The level informs from where type
    /// variables where created.
    pub fn level(&self) -> u32 {
        use std::cmp::min;
        fold_type(self,
                  |typ, level| match **typ {
                      Type::Variable(ref var) => min(var.id, level),
                      _ => level,
                  },
                  u32::max_value())
    }
}

impl TypeVariable {
    pub fn new(var: u32) -> TypeVariable {
        TypeVariable::with_kind(Kind::Type, var)
    }

    pub fn with_kind(kind: Kind, var: u32) -> TypeVariable {
        TypeVariable {
            kind: ArcKind::new(kind),
            id: var,
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

#[derive(PartialEq, Copy, Clone, PartialOrd)]
enum Prec {
    /// The type exists in the top context, no parentheses needed.
    Top,
    /// The type exists in a function argument `Type -> a`, parentheses are
    /// needed if the type is a function `(b -> c) -> a`.
    Function,
    /// The type exists in a constructor argument `Option Type`, parentheses
    /// are needed for functions or other constructors `Option (a -> b)`
    /// `Option (Result a b)`.
    Constructor,
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
          T: Deref<Target = Type<I, T>> + 'a,
          I: AsRef<str>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Standard width for terminals are 80 characters
        const WIDTH: usize = 80;

        let arena = Arena::new();
        let mut s = Vec::new();
        self.pretty(&arena)
            .group()
            .1
            .render(WIDTH, &mut s)
            .map_err(|_| fmt::Error)?;
        write!(f, "{}", ::std::str::from_utf8(&s).expect("utf-8"))
    }
}

#[macro_export]
macro_rules! chain {
    ($alloc: expr; $first: expr, $($rest: expr),+) => {{
        let mut doc = ::pretty::DocBuilder($alloc, $first.into());
        $(
            doc = doc.append($rest);
        )*
        doc
    }}
}

impl<'a, I, T, E> DisplayType<'a, I, T, E>
    where E: DisplayEnv<Ident = I> + 'a,
          T: Deref<Target = Type<I, T>> + 'a,
{
    fn pretty(&self, arena: &'a Arena<'a>) -> DocBuilder<'a, Arena<'a>>
        where I: AsRef<str>,
    {
        fn ident<'b>(arena: &'b Arena<'b>, name: &'b str) -> DocBuilder<'b, Arena<'b>> {
            if name.starts_with(ast::is_operator_char) {
                chain![arena; "(", name, ")"]
            } else {
                arena.text(name)
            }
        }

        fn enclose<'a>(p: Prec,
                       limit: Prec,
                       arena: &'a Arena<'a>,
                       doc: DocBuilder<'a, Arena<'a>>)
                       -> DocBuilder<'a, Arena<'a>> {
            if p >= limit {
                chain![arena; "(", doc, ")"]
            } else {
                doc
            }
        }

        let p = self.prec;
        match *self.typ {
            Type::Hole => arena.text("_"),
            Type::Opaque => arena.text("<opaque>"),
            Type::Variable(ref var) => arena.text(format!("{}", var.id)),
            Type::Generic(ref gen) => arena.text(gen.id.as_ref()),
            Type::App(ref t, ref args) => {
                match self.typ.as_function() {
                    Some((arg, ret)) => {
                        let doc = chain![arena;
                                         dt(self.env, Prec::Function, arg).pretty(arena).group(),
                                         " ->",
                                         arena.space(),
                                         top(self.env, ret).pretty(arena)];

                        enclose(p, Prec::Function, arena, doc)
                    }
                    None => {
                        let mut doc = dt(self.env, Prec::Top, t).pretty(arena);
                        for arg in args {
                            doc = doc.append(arena.space())
                                .append(dt(self.env, Prec::Constructor, arg).pretty(arena));
                        }
                        enclose(p, Prec::Constructor, arena, doc).group()
                    }
                }
            }
            Type::Variant(ref row) => {
                let mut first = true;
                let mut doc = arena.nil();

                match **row {
                    Type::EmptyRow => (),
                    Type::ExtendRow { ref fields, .. } => {
                        for field in fields.iter() {
                            if !first {
                                doc = doc.append(arena.space());
                            }
                            first = false;
                            doc = doc.append("| ")
                                .append(field.name.as_ref());
                            for arg in arg_iter(&field.typ) {
                                doc = chain![arena;
                                            doc,
                                            " ",
                                            dt(self.env, Prec::Constructor, &arg).pretty(arena)];
                            }
                        }
                    }
                    ref typ => panic!("Unexpected type `{}` in variant", typ),
                };

                enclose(p, Prec::Constructor, arena, doc).group()
            }
            Type::Builtin(ref t) => arena.text(t.to_str()),
            Type::Record(ref row) => {
                let mut doc = arena.text("{");
                let empty_fields = match **row {
                    Type::ExtendRow { .. } => false,
                    _ => true,
                };

                doc = match **row {
                    Type::EmptyRow => doc,
                    Type::ExtendRow { .. } => doc.append(top(self.env, row).pretty(arena)).nest(4),
                    _ => {
                        doc.append(arena.space())
                            .append("| ")
                            .append(top(self.env, row).pretty(arena))
                            .nest(4)
                    }
                };
                if !empty_fields {
                    doc = doc.append(arena.space());
                }

                doc.append("}")
                    .group()
            }
            Type::ExtendRow { ref fields, .. } => {
                let mut doc = arena.nil();
                let mut typ = self.typ;

                while let Type::ExtendRow { ref types, ref rest, .. } = *typ {
                    for (i, field) in types.iter().enumerate() {
                        let f = chain![arena;
                            self.env.string(&field.name),
                            arena.space(),
                            arena.concat(field.typ.args.iter().map(|arg| {
                                arena.text(self.env.string(&arg.id)).append(" ")
                            })),
                            arena.text("= ")
                                 .append(top(self.env, &field.typ.typ).pretty(arena)),
                            if i + 1 != types.len() || !fields.is_empty() {
                                arena.text(",")
                            } else {
                                arena.nil()
                            }]
                            .group();
                        doc = doc.append(arena.space()).append(f);
                    }
                    typ = rest;
                }

                if !fields.is_empty() {
                    typ = self.typ;
                }

                while let Type::ExtendRow { ref fields, ref rest, .. } = *typ {
                    for (i, field) in fields.iter().enumerate() {
                        let mut rhs = top(self.env, &*field.typ).pretty(arena);
                        match *field.typ {
                            // Records handle nesting on their own
                            Type::Record(_) => (),
                            _ => rhs = rhs.nest(4),
                        }
                        let f = chain![arena;
                            ident(arena, self.env.string(&field.name)),
                            " : ",
                            rhs.group(),
                            if i + 1 != fields.len() {
                                arena.text(",")
                            } else {
                                arena.nil()
                            }]
                            .group();
                        doc = doc.append(arena.space()).append(f);
                        typ = rest;
                    }
                }
                match *typ {
                    Type::EmptyRow => doc,
                    _ => {
                        doc.append(arena.space())
                            .append("| ")
                            .append(top(self.env, typ).pretty(arena))
                    }
                }
            }
            // This should not be displayed normally as it should only exist in `ExtendRow`
            // which handles `EmptyRow` explicitly
            Type::EmptyRow => arena.text("EmptyRow"),
            Type::Ident(ref id) => arena.text(self.env.string(id)),
            Type::Alias(ref alias) => arena.text(self.env.string(&alias.name)),
        }
    }
}

impl<I, T> fmt::Display for Type<I, T>
    where I: AsRef<str>,
          T: Deref<Target = Type<I, T>>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use std::marker::PhantomData;

        pub struct EmptyEnv<T>(PhantomData<T>);

        impl<T: AsRef<str>> DisplayEnv for EmptyEnv<T> {
            type Ident = T;

            fn string<'a>(&'a self, ident: &'a Self::Ident) -> &'a str {
                ident.as_ref()
            }
        }

        write!(f, "{}", dt(&EmptyEnv(PhantomData), Prec::Top, self))
    }
}

pub fn walk_type<I, T, F>(typ: &T, mut f: F)
    where F: FnMut(&T),
          T: Deref<Target = Type<I, T>>,
{
    f.walk(typ)
}

pub fn walk_type_<I, T, F: ?Sized>(typ: &T, f: &mut F)
    where F: Walker<T>,
          T: Deref<Target = Type<I, T>>,
{
    match **typ {
        Type::App(ref t, ref args) => {
            f.walk(t);
            for a in args {
                f.walk(a);
            }
        }
        Type::Record(ref row) |
        Type::Variant(ref row) => f.walk(row),
        Type::ExtendRow { ref types, ref fields, ref rest } => {
            for field in types {
                f.walk(&field.typ.typ);
            }
            for field in fields {
                f.walk(&field.typ);
            }
            f.walk(rest);
        }
        Type::Hole |
        Type::Opaque |
        Type::Builtin(_) |
        Type::Variable(_) |
        Type::Generic(_) |
        Type::Ident(_) |
        Type::Alias(_) |
        Type::EmptyRow => (),
    }
}

pub fn fold_type<I, T, F, A>(typ: &T, mut f: F, a: A) -> A
    where F: FnMut(&T, A) -> A,
          T: Deref<Target = Type<I, T>>,
{
    let mut a = Some(a);
    walk_type(typ,
              |t| { a = Some(f(t, a.take().expect("None in fold_type"))); });
    a.expect("fold_type")
}

pub trait TypeVisitor<I, T> {
    fn visit(&mut self, typ: &Type<I, T>) -> Option<T>
        where T: Deref<Target = Type<I, T>> + From<Type<I, T>> + Clone,
              I: Clone,
    {
        walk_move_type_opt(typ, self)
    }
}

pub trait Walker<T> {
    fn walk(&mut self, typ: &T);
}

impl<I, T, F: ?Sized> TypeVisitor<I, T> for F
    where F: FnMut(&Type<I, T>) -> Option<T>,
{
    fn visit(&mut self, typ: &Type<I, T>) -> Option<T>
        where T: Deref<Target = Type<I, T>> + From<Type<I, T>> + Clone,
              I: Clone,
    {
        let new_type = walk_move_type_opt(typ, self);
        let new_type2 = self(new_type.as_ref().map_or(typ, |t| t));
        new_type2.or(new_type)
    }
}

/// Wrapper type which allows functions to control how to traverse the members of the type
pub struct ControlVisitation<F>(pub F);

impl<F, I, T> TypeVisitor<I, T> for ControlVisitation<F>
    where F: FnMut(&Type<I, T>) -> Option<T>,
{
    fn visit(&mut self, typ: &Type<I, T>) -> Option<T>
        where T: Deref<Target = Type<I, T>> + From<Type<I, T>> + Clone,
              I: Clone,
    {
        (self.0)(typ)
    }
}

impl<I, T, F: ?Sized> Walker<T> for F
    where F: FnMut(&T),
          T: Deref<Target = Type<I, T>>,
{
    fn walk(&mut self, typ: &T) {
        self(typ);
        walk_type_(typ, self)
    }
}

/// Walks through a type calling `f` on each inner type. If `f` return `Some` the type is replaced.
pub fn walk_move_type<F: ?Sized, I, T>(typ: T, f: &mut F) -> T
    where F: FnMut(&Type<I, T>) -> Option<T>,
          T: Deref<Target = Type<I, T>> + From<Type<I, T>> + Clone,
          I: Clone,
{
    f.visit(&typ).unwrap_or(typ)
}

pub fn walk_move_type_opt<F: ?Sized, I, T>(typ: &Type<I, T>, f: &mut F) -> Option<T>
    where F: TypeVisitor<I, T>,
          T: Deref<Target = Type<I, T>> + From<Type<I, T>> + Clone,
          I: Clone,
{
    match *typ {
        Type::App(ref id, ref args) => {
            let new_args = walk_move_types(args, |t| f.visit(t));
            merge(id, f.visit(id), args, new_args, Type::app)
        }
        Type::Record(ref row) => f.visit(row).map(|row| T::from(Type::Record(row))),
        Type::Variant(ref row) => f.visit(row).map(|row| T::from(Type::Variant(row))),
        Type::ExtendRow { ref types, ref fields, ref rest } => {
            let new_fields = walk_move_types(fields, |field| {
                f.visit(&field.typ).map(|typ| Field::new(field.name.clone(), typ))
            });
            let new_rest = f.visit(rest);
            merge(fields,
                  new_fields,
                  rest,
                  new_rest,
                  |fields, rest| Type::extend_row(types.clone(), fields, rest))
        }
        Type::Hole |
        Type::Opaque |
        Type::Builtin(_) |
        Type::Variable(_) |
        Type::Generic(_) |
        Type::Ident(_) |
        Type::Alias(_) |
        Type::EmptyRow => None,
    }
}

pub fn walk_move_types<'a, I, F, T, R>(types: I, mut f: F) -> Option<R>
    where I: IntoIterator<Item = &'a T>,
          F: FnMut(&'a T) -> Option<T>,
          T: Clone + 'a,
          R: Default + VecLike<T> + DerefMut<Target = [T]>,
{
    let mut out = R::default();
    walk_move_types2(types.into_iter(), false, &mut out, &mut f);
    if out.is_empty() {
        None
    } else {
        out.reverse();
        Some(out)
    }
}
fn walk_move_types2<'a, I, F, T, R>(mut types: I, replaced: bool, output: &mut R, f: &mut F)
    where I: Iterator<Item = &'a T>,
          F: FnMut(&'a T) -> Option<T>,
          T: Clone + 'a,
          R: VecLike<T> + DerefMut<Target = [T]>,
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
