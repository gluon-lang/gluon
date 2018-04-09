use std::borrow::Cow;
use std::fmt;
use std::hash::Hash;
use std::ops::{Deref, DerefMut};
use std::sync::Arc;
use std::marker::PhantomData;

use pretty::{Arena, DocAllocator, DocBuilder};

use smallvec::{SmallVec, VecLike};

use ast::{Comment, Commented, EmptyEnv, IdentEnv};
use fnv::FnvMap;
use kind::{ArcKind, Kind, KindEnv};
use merge::merge;
use pos::{BytePos, HasSpan, Span};
use source::Source;
use symbol::{Symbol, SymbolRef};

#[cfg(feature = "serde")]
use serialization::{SeSeed, Seed};
#[cfg(feature = "serde")]
use serde::de::DeserializeState;
#[cfg(feature = "serde")]
use serde::ser::SerializeState;

use self::pretty_print::Printer;
pub use self::pretty_print::{Filter, TypeFormatter};

pub mod pretty_print;

/// Trait for values which contains typed values which can be refered by name
pub trait TypeEnv: KindEnv {
    /// Returns the type of the value bound at `id`
    fn find_type(&self, id: &SymbolRef) -> Option<&ArcType>;

    /// Returns information about the type `id`
    fn find_type_info(&self, id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>>;
}

impl<'a, T: ?Sized + TypeEnv> TypeEnv for &'a T {
    fn find_type(&self, id: &SymbolRef) -> Option<&ArcType> {
        (**self).find_type(id)
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>> {
        (**self).find_type_info(id)
    }
}

impl TypeEnv for EmptyEnv<Symbol> {
    fn find_type(&self, _id: &SymbolRef) -> Option<&ArcType> {
        None
    }

    fn find_type_info(&self, _id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>> {
        None
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

type_cache! { TypeCache(Id, T) { T, Type }
    hole opaque int byte float string char
    function_builtin array_builtin unit empty_row
}

impl<Id, T> TypeCache<Id, T>
where
    T: From<Type<Id, T>> + Clone,
{
    pub fn function<I>(&self, args: I, ret: T) -> T
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: DoubleEndedIterator<Item = T>,
    {
        args.into_iter().rev().fold(ret, |body, arg| {
            T::from(Type::Function(ArgType::Explicit, arg, body))
        })
    }

    pub fn function_implicit<I>(&self, args: I, ret: T) -> T
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: DoubleEndedIterator<Item = T>,
    {
        args.into_iter().rev().fold(ret, |body, arg| {
            T::from(Type::Function(ArgType::Implicit, arg, body))
        })
    }

    pub fn tuple<S, I>(&self, symbols: &mut S, elems: I) -> T
    where
        S: ?Sized + IdentEnv<Ident = Id>,
        I: IntoIterator<Item = T>,
    {
        let fields: Vec<_> = elems
            .into_iter()
            .enumerate()
            .map(|(i, typ)| Field {
                name: symbols.from_str(&format!("_{}", i)),
                typ: typ,
            })
            .collect();
        if fields.is_empty() {
            self.unit()
        } else {
            self.record(vec![], fields)
        }
    }

    pub fn variant(&self, fields: Vec<Field<Id, T>>) -> T {
        Type::poly_variant(fields, self.empty_row())
    }

    pub fn record(&self, types: Vec<Field<Id, Alias<Id, T>>>, fields: Vec<Field<Id, T>>) -> T {
        Type::poly_record(types, fields, self.empty_row())
    }

    pub fn builtin_type(&self, typ: BuiltinType) -> T {
        match typ {
            BuiltinType::String => self.string(),
            BuiltinType::Byte => self.byte(),
            BuiltinType::Char => self.char(),
            BuiltinType::Int => self.int(),
            BuiltinType::Float => self.float(),
            BuiltinType::Array => self.array_builtin(),
            BuiltinType::Function => self.function_builtin(),
        }
    }

    pub fn array(&self, typ: T) -> T {
        Type::app(self.array_builtin(), collect![typ])
    }
}

/// All the builtin types of gluon
#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
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
            BuiltinType::Array => "Array",
            BuiltinType::Function => "->",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "SeSeed"))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "Seed<Id, T>"))]
#[cfg_attr(feature = "serde_derive", serde(de_parameters = "Id, T"))]
pub struct TypeVariable {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub kind: ArcKind,
    pub id: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "Seed<Id, T>"))]
#[cfg_attr(feature = "serde_derive",
           serde(bound(deserialize = "
           Id: DeserializeState<'de, Seed<Id, T>> + Clone + ::std::any::Any")))]
#[cfg_attr(feature = "serde_derive", serde(de_parameters = "T"))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "SeSeed"))]
#[cfg_attr(feature = "serde_derive", serde(bound(serialize = "Id: SerializeState<SeSeed>")))]
pub struct Skolem<Id> {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub name: Id,
    pub id: u32,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub kind: ArcKind,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "Seed<Id, T>"))]
#[cfg_attr(feature = "serde_derive",
           serde(bound(deserialize = "
           Id: DeserializeState<'de, Seed<Id, T>> + Clone + ::std::any::Any")))]
#[cfg_attr(feature = "serde_derive", serde(de_parameters = "T"))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "SeSeed"))]
#[cfg_attr(feature = "serde_derive", serde(bound(serialize = "Id: SerializeState<SeSeed>")))]
pub struct Generic<Id> {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub id: Id,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub kind: ArcKind,
}

impl<Id> Generic<Id> {
    pub fn new(id: Id, kind: ArcKind) -> Generic<Id> {
        Generic { id: id, kind: kind }
    }
}

/// An alias is wrapper around `Type::Alias`, allowing it to be cheaply converted to a type and
/// dereferenced to `AliasRef`
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "Seed<Id, T>"))]
#[cfg_attr(feature = "serde_derive",
           serde(bound(deserialize = "
           T: DeserializeState<'de, Seed<Id, T>> + Clone + From<Type<Id, T>> + ::std::any::Any,
           Id: DeserializeState<'de, Seed<Id, T>> + Clone + ::std::any::Any")))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "SeSeed"))]
#[cfg_attr(feature = "serde_derive", serde(bound(serialize = "T: SerializeState<SeSeed>")))]
pub struct Alias<Id, T> {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    _typ: T,
    #[cfg_attr(feature = "serde_derive", serde(skip))]
    _marker: PhantomData<Id>,
}

impl<Id, T> Deref for Alias<Id, T>
where
    T: Deref<Target = Type<Id, T>>,
{
    type Target = AliasRef<Id, T>;

    fn deref(&self) -> &Self::Target {
        match *self._typ {
            Type::Alias(ref alias) => alias,
            _ => unreachable!(),
        }
    }
}

impl<Id, T> From<AliasData<Id, T>> for Alias<Id, T>
where
    T: From<Type<Id, T>>,
{
    fn from(data: AliasData<Id, T>) -> Alias<Id, T> {
        Alias {
            _typ: Type::alias(data.name, data.typ),
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
where
    T: From<Type<Id, T>>,
{
    pub fn new(name: Id, typ: T) -> Alias<Id, T> {
        Alias {
            _typ: Type::alias(name, typ),
            _marker: PhantomData,
        }
    }

    pub fn group(group: Vec<AliasData<Id, T>>) -> Vec<Alias<Id, T>> {
        let group = Arc::new(group);
        (0..group.len())
            .map(|index| Alias {
                _typ: T::from(Type::Alias(AliasRef {
                    index: index,
                    group: group.clone(),
                })),
                _marker: PhantomData,
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
where
    T: From<Type<Id, T>> + Deref<Target = Type<Id, T>> + Clone,
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
where
    Id: Clone,
{
    pub fn make_mut(alias: &mut Alias<Id, ArcType<Id>>) -> &mut AliasRef<Id, ArcType<Id>> {
        match *Arc::make_mut(&mut alias._typ.typ) {
            Type::Alias(ref mut alias) => alias,
            _ => unreachable!(),
        }
    }
}

/// Data for a type alias. Probably you want to use `Alias` instead of this directly as Alias allows
/// for cheap conversion back into a type as well.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "Seed<Id, T>"))]
#[cfg_attr(feature = "serde_derive",
           serde(bound(deserialize = "
           T: DeserializeState<'de, Seed<Id, T>> + Clone + From<Type<Id, T>> + ::std::any::Any,
           Id: DeserializeState<'de, Seed<Id, T>> + Clone + ::std::any::Any")))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "SeSeed"))]
#[cfg_attr(feature = "serde_derive",
           serde(bound(serialize = "T: SerializeState<SeSeed>, Id: SerializeState<SeSeed>")))]
pub struct AliasRef<Id, T> {
    /// Name of the Alias
    index: usize,
    #[cfg_attr(feature = "serde_derive",
               serde(deserialize_state_with = "::serialization::deserialize_group"))]
    #[cfg_attr(feature = "serde_derive",
               serde(serialize_state_with = "::serialization::shared::serialize"))]
    /// The other aliases defined in this group
    pub group: Arc<Vec<AliasData<Id, T>>>,
}

impl<Id, T> AliasRef<Id, T>
where
    T: From<Type<Id, T>> + Deref<Target = Type<Id, T>> + Clone,
    Id: Clone + PartialEq,
{
    pub fn typ(&self) -> Cow<T> {
        let opt = walk_move_type_opt(&self.typ, &mut |typ: &T| {
            match **typ {
                Type::Ident(ref id) => {
                    // Replace `Ident` with the alias it resolves to so that a `TypeEnv` is not
                    // needed to resolve the type later on
                    let replacement = self.group.iter().position(|alias| alias.name == *id).map(
                        |index| {
                            T::from(Type::Alias(AliasRef {
                                index: index,
                                group: self.group.clone(),
                            }))
                        },
                    );
                    if replacement.is_none() {
                        info!("Alias group were not able to resolve an identifier");
                    }
                    replacement
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
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "Seed<Id, T>"))]
#[cfg_attr(feature = "serde_derive",
           serde(bound(deserialize = "
           T: Clone + From<Type<Id, T>> + ::std::any::Any + DeserializeState<'de, Seed<Id, T>>,
           Id: DeserializeState<'de, Seed<Id, T>> + Clone + ::std::any::Any")))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "SeSeed"))]
#[cfg_attr(feature = "serde_derive",
           serde(bound(serialize = "T: SerializeState<SeSeed>, Id: SerializeState<SeSeed>")))]
pub struct AliasData<Id, T> {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub name: Id,
    /// The type that is being aliased
    #[cfg_attr(feature = "serde_derive", serde(state))]
    typ: T,
}

impl<Id, T> AliasData<Id, T>
where
    T: From<Type<Id, T>>,
{
    pub fn new(name: Id, args: Vec<Generic<Id>>, typ: T) -> AliasData<Id, T> {
        AliasData {
            name: name,
            typ: Type::forall(args, typ),
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

impl<Id, T> AliasData<Id, T>
where
    T: Deref<Target = Type<Id, T>>,
{
    pub fn params(&self) -> &[Generic<Id>] {
        self.typ.params()
    }

    pub fn aliased_type(&self) -> &T {
        match *self.typ {
            Type::Forall(_, ref typ, _) => typ,
            _ => &self.typ,
        }
    }
}

impl<Id, T> Deref for AliasRef<Id, T> {
    type Target = AliasData<Id, T>;

    fn deref(&self) -> &Self::Target {
        &self.group[self.index]
    }
}

#[derive(Clone, Hash, Eq, PartialEq, Debug)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "Seed<Id, U>"))]
#[cfg_attr(feature = "serde_derive", serde(de_parameters = "U"))]
#[cfg_attr(feature = "serde_derive",
           serde(bound(deserialize = "
           Id: DeserializeState<'de, Seed<Id, U>> + Clone + ::std::any::Any,
           T: DeserializeState<'de, Seed<Id, U>>
                             ")))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "SeSeed"))]
#[cfg_attr(feature = "serde_derive",
           serde(bound(serialize = "T: SerializeState<SeSeed>, Id: SerializeState<SeSeed>")))]
pub struct Field<Id, T = ArcType<Id>> {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub name: Id,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub typ: T,
}

/// `SmallVec` used in the `Type::App` constructor to avoid allocating a `Vec` for every applied
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

#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum ArgType {
    Explicit,
    Implicit,
}

/// The representation of gluon's types.
///
/// For efficiency this enum is not stored directly but instead a pointer wrapper which derefs to
/// `Type` is used to enable types to be shared. It is recommended to use the static functions on
/// `Type` such as `Type::app` and `Type::record` when constructing types as those will construct
/// the pointer wrapper directly.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "Seed<Id, T>"))]
#[cfg_attr(feature = "serde_derive",
           serde(bound(deserialize = "
           T: Clone
                + From<Type<Id, T>>
                + ::std::any::Any
                + DeserializeState<'de, Seed<Id, T>>,
           Id: DeserializeState<'de, Seed<Id, T>>
                + Clone
                + ::std::any::Any
                + DeserializeState<'de, Seed<Id, T>>")))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "SeSeed"))]
pub enum Type<Id, T = ArcType<Id>> {
    /// An unbound type `_`, awaiting ascription.
    Hole,
    /// An opaque type
    Opaque,
    /// A builtin type
    Builtin(BuiltinType),
    /// Universally quantified types
    Forall(
        #[cfg_attr(feature = "serde_derive", serde(state))] Vec<Generic<Id>>,
        #[cfg_attr(feature = "serde_derive", serde(state))] T,
        #[cfg_attr(feature = "serde_derive", serde(state))] Option<Vec<T>>,
    ),
    /// A type application with multiple arguments. For example,
    /// `Map String Int` would be represented as `App(Map, [String, Int])`.
    App(
        #[cfg_attr(feature = "serde_derive", serde(state))] T,
        #[cfg_attr(feature = "serde_derive", serde(state_with = "::serialization::seq"))] AppVec<T>,
    ),
    /// Function type which can have a explicit or implicit argument
    Function(
        ArgType,
        #[cfg_attr(feature = "serde_derive", serde(state))] T,
        #[cfg_attr(feature = "serde_derive", serde(state))] T,
    ),
    /// Record constructor, of kind `Row -> Type`
    Record(#[cfg_attr(feature = "serde_derive", serde(state))] T),
    /// Variant constructor, of kind `Row -> Type`
    Variant(#[cfg_attr(feature = "serde_derive", serde(state))] T),
    /// The empty row, of kind `Row`
    EmptyRow,
    /// Row extension, of kind `... -> Row -> Row`
    ExtendRow {
        /// The associated types of this record type
        #[cfg_attr(feature = "serde_derive", serde(state))]
        types: Vec<Field<Id, Alias<Id, T>>>,
        /// The fields of this record type
        #[cfg_attr(feature = "serde_derive", serde(state))]
        fields: Vec<Field<Id, T>>,
        /// The rest of the row
        #[cfg_attr(feature = "serde_derive", serde(state))]
        rest: T,
    },
    /// An identifier type. These are created during parsing, but should all be
    /// resolved into `Type::Alias`es during type checking.
    ///
    /// Identifiers are also sometimes used inside aliased types to avoid cycles
    /// in reference counted pointers. This is a bit of a wart at the moment and
    /// _may_ cause spurious unification failures.
    Ident(#[cfg_attr(feature = "serde_derive", serde(state))] Id),
    /// An unbound type variable that may be unified with other types. These
    /// will eventually be converted into `Type::Generic`s during generalization.
    Variable(#[cfg_attr(feature = "serde_derive", serde(state))] TypeVariable),
    /// A variable that needs to be instantiated with a fresh type variable
    /// when the binding is referred to.
    Generic(#[cfg_attr(feature = "serde_derive", serde(state))] Generic<Id>),
    Alias(#[cfg_attr(feature = "serde_derive", serde(state))] AliasRef<Id, T>),
    Skolem(#[cfg_attr(feature = "serde_derive", serde(state))] Skolem<Id>),
}

impl<Id, T> Type<Id, T> {
    pub fn as_variable(&self) -> Option<&TypeVariable> {
        match *self {
            Type::Variable(ref var) => Some(var),
            _ => None,
        }
    }
}

impl<Id, T> Type<Id, T>
where
    T: From<Type<Id, T>>,
{
    pub fn hole() -> T {
        T::from(Type::Hole)
    }

    pub fn opaque() -> T {
        T::from(Type::Opaque)
    }

    pub fn builtin(typ: BuiltinType) -> T {
        T::from(Type::Builtin(typ))
    }

    pub fn forall(params: Vec<Generic<Id>>, typ: T) -> T {
        Type::forall_with_vars(params, typ, None)
    }

    pub fn forall_with_vars(params: Vec<Generic<Id>>, typ: T, vars: Option<Vec<T>>) -> T {
        if let Some(ref vars) = vars {
            debug_assert!(vars.len() == params.len());
        }
        if params.is_empty() {
            typ
        } else {
            T::from(Type::Forall(params, typ, vars))
        }
    }

    pub fn array(typ: T) -> T {
        Type::app(Type::array_builtin(), collect![typ])
    }

    pub fn array_builtin() -> T {
        Type::builtin(BuiltinType::Array)
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

    pub fn tuple<S, I>(symbols: &mut S, elems: I) -> T
    where
        S: ?Sized + IdentEnv<Ident = Id>,
        I: IntoIterator<Item = T>,
    {
        T::from(Type::tuple_(symbols, elems))
    }

    pub fn tuple_<S, I>(symbols: &mut S, elems: I) -> Type<Id, T>
    where
        S: ?Sized + IdentEnv<Ident = Id>,
        I: IntoIterator<Item = T>,
    {
        Type::Record(Type::extend_row(
            vec![],
            elems
                .into_iter()
                .enumerate()
                .map(|(i, typ)| Field {
                    name: symbols.from_str(&format!("_{}", i)),
                    typ: typ,
                })
                .collect(),
            Type::empty_row(),
        ))
    }

    pub fn record(types: Vec<Field<Id, Alias<Id, T>>>, fields: Vec<Field<Id, T>>) -> T {
        Type::poly_record(types, fields, Type::empty_row())
    }

    pub fn poly_record(
        types: Vec<Field<Id, Alias<Id, T>>>,
        fields: Vec<Field<Id, T>>,
        rest: T,
    ) -> T {
        T::from(Type::Record(Type::extend_row(types, fields, rest)))
    }

    pub fn extend_row(
        types: Vec<Field<Id, Alias<Id, T>>>,
        fields: Vec<Field<Id, T>>,
        rest: T,
    ) -> T {
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
    where
        T: Clone,
    {
        args.into_iter().rev().fold(ret, |body, arg| {
            T::from(Type::Function(ArgType::Explicit, arg, body))
        })
    }

    pub fn function_implicit<I>(args: I, ret: T) -> T
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: DoubleEndedIterator<Item = T>,
    {
        args.into_iter().rev().fold(ret, |body, arg| {
            T::from(Type::Function(ArgType::Implicit, arg, body))
        })
    }

    pub fn generic(typ: Generic<Id>) -> T {
        T::from(Type::Generic(typ))
    }

    pub fn skolem(typ: Skolem<Id>) -> T {
        T::from(Type::Skolem(typ))
    }

    pub fn variable(typ: TypeVariable) -> T {
        T::from(Type::Variable(typ))
    }

    pub fn alias(name: Id, typ: T) -> T {
        T::from(Type::Alias(AliasRef {
            index: 0,
            group: Arc::new(vec![
                AliasData {
                    name: name,
                    typ: typ,
                },
            ]),
        }))
    }

    pub fn ident(id: Id) -> T {
        T::from(Type::Ident(id))
    }

    pub fn function_builtin() -> T {
        Type::builtin(BuiltinType::Function)
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
        Type::record(vec![], vec![])
    }
}

impl<Id, T> Type<Id, T>
where
    T: Deref<Target = Type<Id, T>>,
{
    pub fn as_function(&self) -> Option<(&T, &T)> {
        self.as_function_with_type().map(|t| (t.1, t.2))
    }

    pub fn as_function_with_type(&self) -> Option<(ArgType, &T, &T)> {
        match *self {
            Type::Function(arg_type, ref arg, ref ret) => return Some((arg_type, arg, ret)),
            Type::App(ref app, ref args) => if args.len() == 2 {
                if let Type::Builtin(BuiltinType::Function) = **app {
                    return Some((ArgType::Explicit, &args[0], &args[1]));
                }
            } else if args.len() == 1 {
                if let Type::App(ref app, ref args2) = **app {
                    if let Type::Builtin(BuiltinType::Function) = **app {
                        return Some((ArgType::Explicit, &args2[0], &args[0]));
                    }
                }
            },
            _ => (),
        }
        None
    }

    pub fn unapplied_args(&self) -> Cow<[T]>
    where
        T: Clone,
    {
        match *self {
            Type::App(ref f, ref args) => {
                let mut f = f;
                let mut extra_args = Vec::new();
                while let Type::App(ref f2, ref args2) = **f {
                    f = f2;
                    extra_args.extend(args2.iter().rev().cloned());
                }
                if extra_args.is_empty() {
                    Cow::Borrowed(args)
                } else {
                    extra_args.reverse();
                    extra_args.extend(args.iter().cloned());
                    Cow::Owned(extra_args)
                }
            }
            _ => Cow::Borrowed(&[]),
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

    pub fn is_non_polymorphic_record(&self) -> bool {
        match *self {
            Type::Record(ref row) | Type::ExtendRow { rest: ref row, .. } => {
                row.is_non_polymorphic_record()
            }
            Type::EmptyRow => true,
            _ => false,
        }
    }

    pub fn params(&self) -> &[Generic<Id>] {
        match *self {
            Type::Alias(ref alias) => alias.typ.params(),
            Type::Forall(ref params, _, _) => params,
            _ => &[],
        }
    }

    pub fn kind(&self) -> Cow<ArcKind> {
        self.kind_(0)
    }

    fn kind_(&self, applied_args: usize) -> Cow<ArcKind> {
        let mut immediate_kind = match *self {
            Type::Function(_, _, _) => Cow::Owned(Kind::typ()),
            Type::App(ref t, ref args) => t.kind_(args.len()),
            Type::Hole | Type::Opaque | Type::Builtin(_) | Type::Record(_) | Type::Variant(_) => {
                Cow::Owned(Kind::typ())
            }
            Type::EmptyRow | Type::ExtendRow { .. } => Cow::Owned(Kind::row().into()),
            Type::Forall(_, ref typ, _) => typ.kind_(applied_args),
            Type::Variable(ref var) => Cow::Borrowed(&var.kind),
            Type::Skolem(ref skolem) => Cow::Borrowed(&skolem.kind),
            Type::Generic(ref gen) => Cow::Borrowed(&gen.kind),
            // FIXME can be another kind
            Type::Ident(_) => Cow::Owned(Kind::typ()),
            Type::Alias(ref alias) => {
                return if alias.params().len() < applied_args {
                    alias.typ.kind_(applied_args - alias.params().len())
                } else {
                    let mut kind = alias.typ.kind_(0).into_owned();
                    for arg in &alias.params()[applied_args..] {
                        kind = Kind::function(arg.kind.clone(), kind)
                    }
                    Cow::Owned(kind)
                }
            }
        };
        for _ in 0..applied_args {
            immediate_kind = match immediate_kind {
                Cow::Borrowed(k) => match **k {
                    Kind::Function(_, ref ret) => Cow::Borrowed(ret),
                    _ => return Cow::Borrowed(k),
                },
                Cow::Owned(k) => match *k {
                    Kind::Function(_, ref ret) => Cow::Owned(ret.clone()),
                    _ => return Cow::Owned(k.clone()),
                },
            };
        }
        immediate_kind
    }
}

impl<T> Type<Symbol, T>
where
    T: Deref<Target = Type<Symbol, T>>,
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
            Type::Function(..) => Some(BuiltinType::Function.symbol()),
            Type::App(ref id, _) => match **id {
                Type::Builtin(b) => Some(b.symbol()),
                _ => None,
            },
            Type::Builtin(b) => Some(b.symbol()),
            _ => None,
        }
    }
}

/// A shared type which is atomically reference counted
#[derive(Eq, PartialEq, Hash)]
pub struct ArcType<Id = Symbol> {
    typ: Arc<Type<Id, ArcType<Id>>>,
}

#[cfg(feature = "serde")]
impl<'de, Id> DeserializeState<'de, Seed<Id, ArcType<Id>>> for ArcType<Id>
where
    Id: DeserializeState<'de, Seed<Id, ArcType<Id>>> + Clone + ::std::any::Any,
{
    fn deserialize_state<D>(
        seed: &mut Seed<Id, ArcType<Id>>,
        deserializer: D,
    ) -> Result<Self, D::Error>
    where
        D: ::serde::de::Deserializer<'de>,
    {
        use serialization::SharedSeed;
        let seed = SharedSeed::new(seed);
        ::serde::de::DeserializeSeed::deserialize(seed, deserializer)
            .map(|typ| ArcType { typ: typ })
    }
}

impl<Id> Clone for ArcType<Id> {
    fn clone(&self) -> ArcType<Id> {
        ArcType {
            typ: self.typ.clone(),
        }
    }
}

impl<Id: fmt::Debug> fmt::Debug for ArcType<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

impl<Id: AsRef<str>> fmt::Display for ArcType<Id> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", TypeFormatter::new(self))
    }
}

impl<Id> Deref for ArcType<Id> {
    type Target = Type<Id, ArcType<Id>>;

    fn deref(&self) -> &Type<Id, ArcType<Id>> {
        &self.typ
    }
}

impl<Id> HasSpan for ArcType<Id> {
    fn span(&self) -> Span<BytePos> {
        Span::new(0.into(), 0.into())
    }
}

impl<Id> Commented for ArcType<Id> {
    fn comment(&self) -> Option<&Comment> {
        None
    }
}

pub fn row_iter<T>(typ: &T) -> RowIterator<T> {
    RowIterator { typ, current: 0 }
}

pub fn row_iter_mut<Id, T>(typ: &mut T) -> RowIteratorMut<Id, T> {
    RowIteratorMut {
        fields: [].iter_mut(),
        rest: typ,
    }
}

pub fn type_field_iter<T>(typ: &T) -> TypeFieldIterator<T> {
    TypeFieldIterator { typ, current: 0 }
}

pub fn remove_forall<'a, Id, T>(typ: &'a T) -> &'a T
where
    T: Deref<Target = Type<Id, T>>,
    Id: 'a,
{
    match **typ {
        Type::Forall(_, ref typ, _) => remove_forall(typ),
        _ => typ,
    }
}

impl<Id> ArcType<Id> {
    pub fn new(typ: Type<Id, ArcType<Id>>) -> ArcType<Id> {
        ArcType { typ: Arc::new(typ) }
    }

    /// Returns an iterator over all type fields in a record.
    /// `{ Test, Test2, x, y } => [Test, Test2]`
    pub fn type_field_iter(&self) -> TypeFieldIterator<Self> {
        type_field_iter(self)
    }

    /// Returns an iterator over all fields in a record.
    /// `{ Test, Test2, x, y } => [x, y]`
    pub fn row_iter(&self) -> RowIterator<Self> {
        row_iter(self)
    }

    pub fn strong_count(typ: &ArcType<Id>) -> usize {
        Arc::strong_count(&typ.typ)
    }

    pub fn remove_implicit_args(&self) -> &ArcType<Id> {
        match **self {
            Type::Function(ArgType::Implicit, _, ref typ) => typ.remove_implicit_args(),
            _ => self,
        }
    }

    pub fn remove_forall(&self) -> &ArcType<Id> {
        remove_forall(self)
    }

    pub fn remove_forall_and_implicit_args(&self) -> &ArcType<Id> {
        match **self {
            Type::Function(ArgType::Implicit, _, ref typ) => typ.remove_forall_and_implicit_args(),
            Type::Forall(_, ref typ, _) => typ.remove_forall_and_implicit_args(),
            _ => self,
        }
    }

    pub fn skolemize(&self, named_variables: &mut FnvMap<Id, ArcType<Id>>) -> ArcType<Id>
    where
        Id: Clone + Eq + Hash,
    {
        let mut typ = self;
        while let Type::Forall(ref params, ref inner_type, Some(ref vars)) = **typ {
            let iter = params.iter().zip(vars).map(|(param, var)| {
                let var = var.as_variable().unwrap();
                (
                    param.id.clone(),
                    Type::skolem(Skolem {
                        name: param.id.clone(),
                        id: var.id,
                        kind: var.kind.clone(),
                    }),
                )
            });
            named_variables.extend(iter);
            typ = inner_type;
        }
        typ.skolemize_(named_variables)
            .unwrap_or_else(|| typ.clone())
    }

    fn skolemize_(&self, named_variables: &mut FnvMap<Id, ArcType<Id>>) -> Option<ArcType<Id>>
    where
        Id: Clone + Eq + Hash,
    {
        match **self {
            Type::Generic(ref generic) => named_variables.get(&generic.id).cloned(),
            _ => walk_move_type_opt(
                self,
                &mut ControlVisitation(|typ: &ArcType<Id>| typ.skolemize_(named_variables)),
            ),
        }
    }

    pub fn instantiate_generics(&self, named_variables: &mut FnvMap<Id, ArcType<Id>>) -> ArcType<Id>
    where
        Id: Clone + Eq + Hash,
    {
        let mut typ = self;
        while let Type::Forall(ref params, ref inner_type, Some(ref vars)) = **typ {
            named_variables.extend(
                params
                    .iter()
                    .zip(vars)
                    .map(|(param, var)| (param.id.clone(), var.clone())),
            );
            typ = inner_type;
        }
        typ.instantiate_generics_(named_variables)
            .unwrap_or_else(|| typ.clone())
    }

    pub fn instantiate_generics_(
        &self,
        named_variables: &FnvMap<Id, ArcType<Id>>,
    ) -> Option<ArcType<Id>>
    where
        Id: Clone + Eq + Hash,
    {
        match **self {
            Type::Generic(ref generic) => named_variables.get(&generic.id).cloned(),
            Type::Forall(ref params, ref typ, ref vars) => {
                // TODO This clone is inneficient
                let mut named_variables = named_variables.clone();
                // forall a . { x : forall a . a -> a } -> a
                // Should not instantiate the `a -> a` part so we must remove the parameters
                // before visiting that part
                for param in params {
                    named_variables.remove(&param.id);
                }

                typ.instantiate_generics_(&mut named_variables)
                    .map(|typ| Type::Forall(params.clone(), typ, vars.clone()).into())
            }
            _ => walk_move_type_opt(
                self,
                &mut ControlVisitation(|typ: &Self| typ.instantiate_generics_(named_variables)),
            ),
        }
    }

    pub fn forall_scope_iter(&self) -> ForallScopeIter<Id> {
        ForallScopeIter {
            typ: self,
            offset: 0,
        }
    }

    pub fn pretty<'a>(&'a self, arena: &'a Arena<'a>) -> DocBuilder<'a, Arena<'a>>
    where
        Id: AsRef<str>,
    {
        top(self).pretty(&Printer::new(arena, &Source::new("")))
    }
}

pub struct ForallScopeIter<'a, Id: 'a> {
    pub typ: &'a ArcType<Id>,
    offset: usize,
}

impl<'a, Id> Iterator for ForallScopeIter<'a, Id> {
    type Item = (&'a Generic<Id>, &'a ArcType<Id>);

    fn next(&mut self) -> Option<Self::Item> {
        match **self.typ {
            Type::Forall(ref params, ref typ, Some(ref vars)) => {
                let offset = self.offset;
                let item = params.get(offset).map(|param| {
                    self.offset += 1;
                    (param, &vars[offset])
                });
                match item {
                    Some(_) => item,
                    None => {
                        self.typ = typ;
                        self.next()
                    }
                }
            }
            _ => None,
        }
    }
}

impl ArcType {
    pub fn params_mut(&mut self) -> &mut [Generic<Symbol>] {
        use std::sync::Arc;

        match *Arc::make_mut(&mut self.typ) {
            /*
            // TODO
            Type::Alias(ref mut alias) => {
                Arc::make_mut(alias.unresolved_type_mut().typ).params_mut()
            }
            */
            Type::Forall(ref mut params, _, _) => params,
            Type::App(ref mut id, _) => id.params_mut(),
            _ => &mut [],
        }
    }

    /// Applies a list of arguments to a parameterised type, returning `Some`
    /// if the substitution was successful.
    ///
    /// Example:
    ///
    /// ```text
    /// self = forall e t . | Err e | Ok t
    /// args = [Error, Option a]
    /// result = | Err Error | Ok (Option a)
    /// ```
    pub fn apply_args(&self, args: &[ArcType]) -> Option<ArcType> {
        let params = self.params();
        let mut typ = self.remove_forall().clone();

        // It is ok to take the type only if it is fully applied or if it
        // the missing argument only appears in order at the end, i.e:
        //
        // type Test a b c = Type (a Int) b c
        //
        // Test a b == Type (a Int) b
        // Test a == Type (a Int)
        // Test == ??? (Impossible to do a sane substitution)
        match *typ.clone() {
            Type::App(ref d, ref arg_types) => {
                let allowed_missing_args = arg_types
                    .iter()
                    .rev()
                    .zip(params.iter().rev())
                    .take_while(|&(l, r)| match **l {
                        Type::Generic(ref g) => g == r,
                        _ => false,
                    })
                    .count();

                if params.len() - args.len() <= allowed_missing_args {
                    // Remove the args at the end of the aliased type
                    let arg_types: AppVec<_> = arg_types
                        .iter()
                        .take(arg_types.len() - (params.len() - args.len()))
                        .cloned()
                        .collect();
                    typ = Type::app(d.clone(), arg_types);
                } else {
                    return None;
                }
            }
            _ => if args.len() != params.len() {
                return None;
            },
        }

        Some(walk_move_type(typ.remove_forall().clone(), &mut |typ| {
            match **typ {
                Type::Generic(ref generic) => {
                    // Replace the generic variable with the type from the list
                    // or if it is not found the make a fresh variable
                    params
                        .iter()
                        .zip(args)
                        .find(|&(arg, _)| arg.id == generic.id)
                        .map(|(_, typ)| typ.clone())
                }
                _ => None,
            }
        }))
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
where
    T: Deref<Target = Type<Id, T>>,
{
    type Item = &'a Field<Id, Alias<Id, T>>;

    fn next(&mut self) -> Option<&'a Field<Id, Alias<Id, T>>> {
        match **self.typ {
            Type::Record(ref row) => {
                self.typ = row;
                self.next()
            }
            Type::ExtendRow {
                ref types,
                ref rest,
                ..
            } => {
                let current = self.current;
                self.current += 1;
                types.get(current).or_else(|| {
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
where
    T: Deref<Target = Type<Id, T>>,
{
    type Item = &'a Field<Id, T>;

    fn next(&mut self) -> Option<&'a Field<Id, T>> {
        match **self.typ {
            Type::Record(ref row) | Type::Variant(ref row) => {
                self.typ = row;
                self.next()
            }
            Type::ExtendRow {
                ref fields,
                ref rest,
                ..
            } => {
                let current = self.current;
                self.current += 1;
                fields.get(current).or_else(|| {
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
where
    T: Deref<Target = Type<Id, T>>,
{
    fn len(&self) -> usize {
        let mut typ = self.typ;
        let mut size = 0;
        loop {
            typ = match **typ {
                Type::Record(ref row) | Type::Variant(ref row) => row,
                Type::ExtendRow {
                    ref fields,
                    ref rest,
                    ..
                } => {
                    size += fields.len();
                    rest
                }
                _ => break,
            };
        }
        size
    }
}

pub struct RowIteratorMut<'a, Id: 'a, T: 'a> {
    fields: ::std::slice::IterMut<'a, Field<Id, T>>,
    rest: *mut T,
}

impl<'a, Id: 'a, T: 'a> Iterator for RowIteratorMut<'a, Id, T>
where
    T: DerefMut<Target = Type<Id, T>>,
{
    type Item = &'a mut Field<Id, T>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(x) = self.fields.next() {
                return Some(x);
            }
            // The lifetime checker can't see that self.rest will be unused after we assign the
            // contents to it so we must just a raw pointer get around it
            unsafe {
                match **self.rest {
                    Type::Record(ref mut row) | Type::Variant(ref mut row) => self.rest = row,
                    Type::ExtendRow {
                        ref mut fields,
                        ref mut rest,
                        ..
                    } => {
                        self.fields = fields.iter_mut();
                        self.rest = rest;
                    }
                    _ => return None,
                }
            }
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
where
    T: Deref<Target = Type<Id, T>>,
{
    ArgIterator { typ: typ }
}

impl<'a, Id, T> Iterator for ArgIterator<'a, T>
where
    Id: 'a,
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

pub struct ImplicitArgIterator<'a, T: 'a> {
    /// The current type being iterated over. After `None` has been returned this is the return
    /// type.
    pub typ: &'a T,
}

/// Constructs an iterator over a functions arguments
pub fn implicit_arg_iter<Id, T>(typ: &T) -> ImplicitArgIterator<T>
where
    T: Deref<Target = Type<Id, T>>,
{
    ImplicitArgIterator { typ: typ }
}

impl<'a, Id, T> Iterator for ImplicitArgIterator<'a, T>
where
    Id: 'a,
    T: Deref<Target = Type<Id, T>>,
{
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> {
        self.typ
            .as_function_with_type()
            .and_then(|(arg_type, arg, ret)| {
                if arg_type == ArgType::Implicit {
                    self.typ = ret;
                    Some(arg)
                } else {
                    None
                }
            })
    }
}

impl<Id> ArcType<Id> {
    /// Returns the lowest level which this type contains. The level informs from where type
    /// variables where created.
    pub fn level(&self) -> u32 {
        use std::cmp::min;
        fold_type(
            self,
            |typ, level| match **typ {
                Type::Variable(ref var) => min(var.id, level),
                _ => level,
            },
            u32::max_value(),
        )
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
pub enum Prec {
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

impl Prec {
    pub fn enclose<'a>(
        &self,
        limit: Prec,
        arena: &'a Arena<'a>,
        doc: DocBuilder<'a, Arena<'a>>,
    ) -> DocBuilder<'a, Arena<'a>> {
        if *self >= limit {
            chain![arena; "(", doc, ")"]
        } else {
            doc
        }
    }
}

fn dt<'a, T>(prec: Prec, typ: &'a T) -> DisplayType<'a, T> {
    DisplayType {
        prec: prec,
        typ: typ,
    }
}

fn top<'a, T>(typ: &'a T) -> DisplayType<'a, T> {
    dt(Prec::Top, typ)
}

pub struct DisplayType<'a, T: 'a> {
    prec: Prec,
    typ: &'a T,
}

pub trait ToDoc<'a, A, E> {
    fn to_doc(&'a self, allocator: &'a A, env: E) -> DocBuilder<'a, A>
    where
        A: DocAllocator<'a>;
}

impl<'a, I> ToDoc<'a, Arena<'a>, ()> for ArcType<I>
where
    I: AsRef<str>,
{
    fn to_doc(&'a self, arena: &'a Arena<'a>, _: ()) -> DocBuilder<'a, Arena<'a>> {
        self.to_doc(arena, &Source::new(""))
    }
}

impl<'a, 'e, I> ToDoc<'a, Arena<'a>, &'e Source<'a>> for ArcType<I>
where
    I: AsRef<str>,
{
    fn to_doc(&'a self, arena: &'a Arena<'a>, source: &'e Source<'a>) -> DocBuilder<'a, Arena<'a>> {
        let printer = Printer::new(arena, source);
        dt(Prec::Top, self).pretty(&printer)
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

impl<'a, I, T> DisplayType<'a, T>
where
    T: Deref<Target = Type<I, T>> + HasSpan + Commented + 'a,
{
    pub fn pretty<'e>(&self, printer: &Printer<'a, 'e, I>) -> DocBuilder<'a, Arena<'a>>
    where
        I: AsRef<str>,
    {
        const INDENT: usize = 4;

        let arena = printer.arena;

        let p = self.prec;
        let typ = self.typ;

        let doc = match **typ {
            Type::Hole => arena.text("_"),
            Type::Opaque => arena.text("<opaque>"),
            Type::Forall(ref args, ref typ, _) => {
                let doc = chain![arena;
                    chain![arena;
                        "forall ",
                        arena.concat(args.iter().map(|arg| {
                            arena.text(arg.id.as_ref()).append(arena.space())
                        })),
                        "."
                    ].group(),
                    arena.space(),
                    top(typ).pretty(printer)
                ];
                p.enclose(Prec::Function, arena, doc)
            }
            Type::Variable(ref var) => arena.text(format!("{}", var.id)),
            Type::Skolem(ref skolem) => chain![
                    arena;
                    skolem.name.as_ref(),
                    "@",
                    skolem.id.to_string()
                ],
            Type::Generic(ref gen) => arena.text(gen.id.as_ref()),
            Type::Function(..) => self.pretty_function(printer).nest(INDENT),
            Type::App(ref t, ref args) => match self.typ.as_function() {
                Some(_) => self.pretty_function(printer).nest(INDENT),
                None => {
                    let doc = dt(Prec::Top, t).pretty(printer);
                    let arg_doc = arena.concat(args.iter().map(|arg| {
                        arena
                            .space()
                            .append(dt(Prec::Constructor, arg).pretty(printer))
                    }));
                    let doc = doc.append(arg_doc.nest(INDENT));
                    p.enclose(Prec::Constructor, arena, doc).group()
                }
            },
            Type::Variant(ref row) => {
                let mut first = true;
                let mut doc = arena.nil();

                match **row {
                    Type::EmptyRow => (),
                    Type::ExtendRow { ref fields, .. } => for field in fields.iter() {
                        if !first {
                            doc = doc.append(arena.space());
                        }
                        first = false;
                        doc = doc.append("| ").append(field.name.as_ref());
                        for arg in arg_iter(&field.typ) {
                            doc = chain![arena;
                                doc,
                                " ",
                                dt(Prec::Constructor, arg).pretty(printer)
                            ];
                        }
                    },
                    _ => ice!("Unexpected type in variant"),
                };

                p.enclose(Prec::Constructor, arena, doc).group()
            }
            Type::Builtin(ref t) => match *t {
                BuiltinType::Function => chain![arena; "(", t.to_str(), ")"],
                _ => arena.text(t.to_str()),
            },
            Type::Record(ref row) => {
                let forced_newline = match **row {
                    Type::ExtendRow { ref fields, .. } => {
                        fields.iter().any(|field| field.typ.comment().is_some())
                    }
                    _ => false,
                };

                let newline = if forced_newline {
                    arena.newline()
                } else {
                    arena.space()
                };

                // Empty records are always formatted as unit (`()`)
                if let Type::EmptyRow = **row {
                    return arena.text("()");
                }
                let mut doc = arena.text("{");
                let empty_fields = match **row {
                    Type::ExtendRow { .. } => false,
                    _ => true,
                };

                doc = match **row {
                    Type::EmptyRow => doc,
                    Type::ExtendRow { .. } => doc.append(top(row).pretty(printer)).nest(INDENT),
                    _ => doc.append(arena.space())
                        .append("| ")
                        .append(top(row).pretty(printer))
                        .nest(INDENT),
                };
                if !empty_fields {
                    doc = doc.append(newline);
                }

                doc.append("}").group()
            }
            Type::ExtendRow { ref fields, .. } => {
                let mut doc = arena.nil();
                let mut typ = self.typ;
                let forced_newline = fields.iter().any(|field| field.typ.comment().is_some());

                let newline = if forced_newline {
                    arena.newline()
                } else {
                    arena.space()
                };

                let print_any_field = fields
                    .iter()
                    .any(|field| printer.filter(&field.name) != Filter::Drop);

                let mut filtered = false;

                while let Type::ExtendRow {
                    ref types,
                    ref rest,
                    ..
                } = **typ
                {
                    for (i, field) in types.iter().enumerate() {
                        let filter = printer.filter(&field.name);
                        if filter == Filter::Drop {
                            filtered = true;
                            continue;
                        }

                        let f = chain![arena;
                            field.name.as_ref(),
                            arena.space(),
                            arena.text("= "),
                            if filter == Filter::RetainKey {
                                arena.text("...")
                            } else {
                                 top(&field.typ.typ).pretty(printer)
                            },
                            if i + 1 != types.len() || print_any_field {
                                arena.text(",")
                            } else {
                                arena.nil()
                            }
                        ].group();
                        doc = doc.append(newline.clone()).append(f);
                    }
                    typ = rest;
                }

                if !fields.is_empty() {
                    typ = self.typ;
                }

                while let Type::ExtendRow {
                    ref fields,
                    ref rest,
                    ..
                } = **typ
                {
                    for (i, field) in fields.iter().enumerate() {
                        let filter = printer.filter(&field.name);
                        if filter == Filter::Drop {
                            filtered = true;
                            continue;
                        }

                        let mut rhs = if filter == Filter::RetainKey {
                            arena.text("...")
                        } else {
                            top(&field.typ).pretty(printer)
                        };
                        match *field.typ {
                            // Records handle nesting on their own
                            Type::Record(_) => (),
                            _ => rhs = rhs.nest(INDENT),
                        }
                        let f = chain![arena;
                            pretty_print::doc_comment(arena, field.typ.comment()),
                            pretty_print::ident(arena, field.name.as_ref()),
                            " : ",
                            rhs.group(),
                            if i + 1 != fields.len() {
                                arena.text(",")
                            } else {
                                arena.nil()
                            }].group();
                        doc = doc.append(newline.clone()).append(f);
                    }
                    typ = rest;
                }

                let doc = if filtered {
                    if doc.1 == arena.nil().1 {
                        chain![arena;
                            newline.clone(),
                            "..."
                        ]
                    } else {
                        chain![arena;
                            newline.clone(),
                            "...,",
                            doc,
                            if newline.1 == arena.space().1 {
                                arena.text(",")
                            } else {
                                arena.nil()
                            },
                            newline.clone(),
                            "..."
                        ]
                    }
                } else {
                    doc
                };
                match **typ {
                    Type::EmptyRow => doc,
                    _ => doc.append(arena.space())
                        .append("| ")
                        .append(top(typ).pretty(printer)),
                }
            }
            // This should not be displayed normally as it should only exist in `ExtendRow`
            // which handles `EmptyRow` explicitly
            Type::EmptyRow => arena.text("EmptyRow"),
            Type::Ident(ref id) => arena.text(id.as_ref()),
            Type::Alias(ref alias) => arena.text(alias.name.as_ref()),
        };
        match **typ {
            Type::App(..) | Type::ExtendRow { .. } | Type::Variant(..) | Type::Function(..) => doc,
            _ => {
                let comment = printer.comments_before(typ.span().start);
                comment.append(doc)
            }
        }
    }

    fn pretty_function<'e>(&self, printer: &Printer<'a, 'e, I>) -> DocBuilder<'a, Arena<'a>>
    where
        I: AsRef<str>,
    {
        let arena = printer.arena;
        let p = self.prec;
        match self.typ.as_function_with_type() {
            Some((arg_type, arg, ret)) => {
                let doc = chain![arena;
                    if arg_type == ArgType::Implicit { "[" } else { "" },
                    dt(Prec::Function, arg).pretty(printer).group(),
                    if arg_type == ArgType::Implicit { "]" } else { "" },
                    printer.space_after(arg.span().end),
                    "-> ",
                    top(ret).pretty_function(printer)
                ];

                p.enclose(Prec::Function, arena, doc)
            }
            None => self.pretty(printer),
        }
    }
}

pub fn pretty_print<'a, 'e, I, T>(
    printer: &Printer<'a, 'e, I>,
    typ: &'a T,
) -> DocBuilder<'a, Arena<'a>>
where
    I: AsRef<str> + 'a,
    T: Deref<Target = Type<I, T>> + HasSpan + Commented,
{
    dt(Prec::Top, typ).pretty(printer)
}

pub fn walk_type<'a, I, T, F>(typ: &'a T, mut f: F)
where
    F: Walker<'a, T>,
    T: Deref<Target = Type<I, T>> + 'a,
    I: 'a,
{
    f.walk(typ)
}

pub fn walk_type_<'a, I, T, F: ?Sized>(typ: &'a T, f: &mut F)
where
    F: Walker<'a, T>,
    T: Deref<Target = Type<I, T>> + 'a,
    I: 'a,
{
    match **typ {
        Type::Forall(_, ref typ, _) => f.walk(typ),
        Type::Function(_, ref arg, ref ret) => {
            f.walk(arg);
            f.walk(ret);
        }
        Type::App(ref t, ref args) => {
            f.walk(t);
            for a in args {
                f.walk(a);
            }
        }
        Type::Record(ref row) | Type::Variant(ref row) => f.walk(row),
        Type::ExtendRow {
            ref types,
            ref fields,
            ref rest,
        } => {
            for field in types {
                f.walk(&field.typ.typ);
            }
            for field in fields {
                f.walk(&field.typ);
            }
            f.walk(rest);
        }
        Type::Hole
        | Type::Opaque
        | Type::Builtin(_)
        | Type::Variable(_)
        | Type::Generic(_)
        | Type::Skolem(_)
        | Type::Ident(_)
        | Type::Alias(_)
        | Type::EmptyRow => (),
    }
}

pub fn walk_type_mut<I, T, F: ?Sized>(typ: &mut T, f: &mut F)
where
    F: WalkerMut<T>,
    T: DerefMut<Target = Type<I, T>>,
{
    match **typ {
        Type::Forall(_, ref mut typ, _) => f.walk_mut(typ),
        Type::Function(_, ref mut arg, ref mut ret) => {
            f.walk_mut(arg);
            f.walk_mut(ret);
        }
        Type::App(ref mut t, ref mut args) => {
            f.walk_mut(t);
            for a in args {
                f.walk_mut(a);
            }
        }
        Type::Record(ref mut row) | Type::Variant(ref mut row) => f.walk_mut(row),
        Type::ExtendRow {
            // Can't visit types mutably as they are always shared
            types: _,
            ref mut fields,
            ref mut rest,
        } => {
            for field in fields {
                f.walk_mut(&mut field.typ);
            }
            f.walk_mut(rest);
        }
        Type::Hole
        | Type::Opaque
        | Type::Builtin(_)
        | Type::Variable(_)
        | Type::Generic(_)
        | Type::Skolem(_)
        | Type::Ident(_)
        | Type::Alias(_)
        | Type::EmptyRow => (),
    }
}

pub fn fold_type<I, T, F, A>(typ: &T, mut f: F, a: A) -> A
where
    F: FnMut(&T, A) -> A,
    T: Deref<Target = Type<I, T>>,
{
    let mut a = Some(a);
    walk_type(typ, |t| {
        a = Some(f(t, a.take().expect("None in fold_type")));
    });
    a.expect("fold_type")
}

pub trait TypeVisitor<I, T> {
    fn visit(&mut self, typ: &T) -> Option<T>
    where
        T: Deref<Target = Type<I, T>> + From<Type<I, T>> + Clone,
        I: Clone,
    {
        walk_move_type_opt(typ, self)
    }
}

pub trait Walker<'a, T> {
    fn walk(&mut self, typ: &'a T);
}

impl<I, T, F: ?Sized> TypeVisitor<I, T> for F
where
    F: FnMut(&T) -> Option<T>,
{
    fn visit(&mut self, typ: &T) -> Option<T>
    where
        T: Deref<Target = Type<I, T>> + From<Type<I, T>> + Clone,
        I: Clone,
    {
        let new_type = walk_move_type_opt(typ, self);
        let new_type2 = self(new_type.as_ref().map_or(typ, |t| t));
        new_type2.or(new_type)
    }
}

/// Wrapper type which allows functions to control how to traverse the members of the type
pub struct ControlVisitation<F: ?Sized>(pub F);

impl<F, I, T> TypeVisitor<I, T> for ControlVisitation<F>
where
    F: FnMut(&T) -> Option<T>,
{
    fn visit(&mut self, typ: &T) -> Option<T>
    where
        T: Deref<Target = Type<I, T>> + From<Type<I, T>> + Clone,
        I: Clone,
    {
        (self.0)(typ)
    }
}

impl<'a, F, T> Walker<'a, T> for ControlVisitation<F>
where
    F: ?Sized + FnMut(&'a T),
    T: 'a,
{
    fn walk(&mut self, typ: &'a T) {
        (self.0)(typ)
    }
}

impl<'a, I, T, F: ?Sized> Walker<'a, T> for F
where
    F: FnMut(&'a T),
    T: Deref<Target = Type<I, T>> + 'a,
    I: 'a,
{
    fn walk(&mut self, typ: &'a T) {
        self(typ);
        walk_type_(typ, self)
    }
}

pub trait WalkerMut<T> {
    fn walk_mut(&mut self, typ: &mut T);
}

impl<I, T, F: ?Sized> WalkerMut<T> for F
where
    F: FnMut(&mut T),
    T: DerefMut<Target = Type<I, T>>,
{
    fn walk_mut(&mut self, typ: &mut T) {
        self(typ);
        walk_type_mut(typ, self)
    }
}

/// Walks through a type calling `f` on each inner type. If `f` return `Some` the type is replaced.
pub fn walk_move_type<F: ?Sized, I, T>(typ: T, f: &mut F) -> T
where
    F: FnMut(&T) -> Option<T>,
    T: Deref<Target = Type<I, T>> + From<Type<I, T>> + Clone,
    I: Clone,
{
    f.visit(&typ).unwrap_or(typ)
}

pub fn visit_type_opt<F: ?Sized, I, T>(typ: &T, f: &mut F) -> Option<T>
where
    F: TypeVisitor<I, T>,
    T: Deref<Target = Type<I, T>> + From<Type<I, T>> + Clone,
    I: Clone,
{
    f.visit(typ)
}

pub fn walk_move_type_opt<F: ?Sized, I, T>(typ: &Type<I, T>, f: &mut F) -> Option<T>
where
    F: TypeVisitor<I, T>,
    T: Deref<Target = Type<I, T>> + From<Type<I, T>> + Clone,
    I: Clone,
{
    match *typ {
        Type::Forall(ref args, ref typ, ref vars) => f.visit(typ)
            .map(|typ| T::from(Type::Forall(args.clone(), typ, vars.clone()))),

        Type::Function(arg_type, ref arg, ref ret) => {
            let new_arg = f.visit(arg);
            let new_ret = f.visit(ret);
            merge(arg, new_arg, ret, new_ret, |arg, ret| {
                T::from(Type::Function(arg_type, arg, ret))
            })
        }
        Type::App(ref id, ref args) => {
            let new_args = walk_move_types(args, |t| f.visit(t));
            merge(id, f.visit(id), args, new_args, Type::app)
        }
        Type::Record(ref row) => f.visit(row).map(|row| T::from(Type::Record(row))),
        Type::Variant(ref row) => f.visit(row).map(|row| T::from(Type::Variant(row))),
        Type::ExtendRow {
            ref types,
            ref fields,
            ref rest,
        } => {
            let new_fields = walk_move_types(fields, |field| {
                f.visit(&field.typ)
                    .map(|typ| Field::new(field.name.clone(), typ))
            });
            let new_rest = f.visit(rest);
            merge(fields, new_fields, rest, new_rest, |fields, rest| {
                Type::extend_row(types.clone(), fields, rest)
            })
        }
        Type::Hole
        | Type::Opaque
        | Type::Builtin(_)
        | Type::Variable(_)
        | Type::Skolem(_)
        | Type::Generic(_)
        | Type::Ident(_)
        | Type::Alias(_)
        | Type::EmptyRow => None,
    }
}

pub fn walk_move_types<'a, I, F, T, R>(types: I, mut f: F) -> Option<R>
where
    I: IntoIterator<Item = &'a T>,
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
where
    I: Iterator<Item = &'a T>,
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

pub fn translate_alias<Id, T, U, F>(alias: &AliasData<Id, T>, mut translate: F) -> AliasData<Id, U>
where
    T: Deref<Target = Type<Id, T>>,
    U: From<Type<Id, U>> + Clone,
    Id: Clone,
    F: FnMut(&T) -> U,
{
    AliasData {
        name: alias.name.clone(),
        typ: translate(&alias.typ),
    }
}

pub fn translate_type<Id, T, U>(cache: &TypeCache<Id, U>, typ: &Type<Id, T>) -> U
where
    T: Deref<Target = Type<Id, T>>,
    U: From<Type<Id, U>> + Clone,
    Id: Clone,
{
    translate_type_with(cache, typ, |t| translate_type(cache, t))
}

pub fn translate_type_with<Id, T, U, F>(
    cache: &TypeCache<Id, U>,
    typ: &Type<Id, T>,
    mut translate: F,
) -> U
where
    T: Deref<Target = Type<Id, T>>,
    U: From<Type<Id, U>> + Clone,
    Id: Clone,
    F: FnMut(&T) -> U,
{
    match *typ {
        Type::Function(arg_type, ref arg, ref ret) => {
            U::from(Type::Function(arg_type, translate(arg), translate(ret)))
        }
        Type::App(ref f, ref args) => Type::app(
            translate(f),
            args.iter().map(|typ| translate(typ)).collect(),
        ),
        Type::Record(ref row) => U::from(Type::Record(translate(row))),
        Type::Variant(ref row) => U::from(Type::Variant(translate(row))),
        Type::Forall(ref params, ref typ, ref skolem) => U::from(Type::Forall(
            params.clone(),
            translate(typ),
            skolem
                .as_ref()
                .map(|ts| ts.iter().map(|t| translate(t)).collect()),
        )),
        Type::Skolem(ref skolem) => U::from(Type::Skolem(Skolem {
            name: skolem.name.clone(),
            id: skolem.id.clone(),
            kind: skolem.kind.clone(),
        })),
        Type::ExtendRow {
            ref types,
            ref fields,
            ref rest,
        } => Type::extend_row(
            types
                .iter()
                .map(|field| Field {
                    name: field.name.clone(),
                    typ: Alias::from(translate_alias(&field.typ, &mut translate)),
                })
                .collect(),
            fields
                .iter()
                .map(|field| Field {
                    name: field.name.clone(),
                    typ: translate(&field.typ),
                })
                .collect(),
            translate_type(cache, rest),
        ),
        Type::Hole => cache.hole(),
        Type::Opaque => cache.opaque(),
        Type::Builtin(ref builtin) => cache.builtin_type(builtin.clone()),
        Type::Variable(ref var) => Type::variable(var.clone()),
        Type::Generic(ref gen) => Type::generic(gen.clone()),
        Type::Ident(ref id) => Type::ident(id.clone()),
        Type::Alias(_) => ice!("translate_type called on alias"),
        Type::EmptyRow => cache.empty_row(),
    }
}
