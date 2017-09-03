use std::borrow::Cow;
use std::fmt;
use std::ops::{Deref, DerefMut};
use std::sync::Arc;
use std::marker::PhantomData;

use pretty::{Arena, DocAllocator, DocBuilder};

use smallvec::{SmallVec, VecLike};

use ast::IdentEnv;
use kind::{ArcKind, Kind, KindEnv};
use merge::merge;
use symbol::{Symbol, SymbolRef};

#[cfg(feature = "serde")]
use serialization::{SeSeed, Seed};
#[cfg(feature = "serde")]
use serde::de::DeserializeState;
#[cfg(feature = "serde")]
use serde::ser::SerializeState;

/// Trait for values which contains typed values which can be refered by name
pub trait TypeEnv: KindEnv {
    /// Returns the type of the value bound at `id`
    fn find_type(&self, id: &SymbolRef) -> Option<&ArcType>;

    /// Returns information about the type `id`
    fn find_type_info(&self, id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>>;

    /// Returns a record which contains all `fields`. The first element is the record type and the
    /// second is the alias type.
    fn find_record(
        &self,
        fields: &[Symbol],
        selector: RecordSelector,
    ) -> Option<(ArcType, ArcType)>;
}

pub enum RecordSelector {
    // Selects a record which exactly has the fields
    Exact,
    // Selects a record which has all the passed fields (in any order)
    Subset,
}

impl RecordSelector {
    /// Returns `true` if the iterators matches according to the selector
    pub fn matches<F, I, J>(&self, mut record: F, needle: J) -> bool
    where
        F: FnMut() -> I,
        I: IntoIterator,
        J: IntoIterator<Item = I::Item>,
        I::Item: PartialEq,
    {
        match *self {
            RecordSelector::Exact => record().into_iter().eq(needle),
            RecordSelector::Subset => needle
                .into_iter()
                .all(|name| record().into_iter().any(|other| other == name)),
        }
    }
}

impl<'a, T: ?Sized + TypeEnv> TypeEnv for &'a T {
    fn find_type(&self, id: &SymbolRef) -> Option<&ArcType> {
        (**self).find_type(id)
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>> {
        (**self).find_type_info(id)
    }

    fn find_record(
        &self,
        fields: &[Symbol],
        selector: RecordSelector,
    ) -> Option<(ArcType, ArcType)> {
        (**self).find_record(fields, selector)
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
            Type::app(self.function_builtin(), collect![arg, body])
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
            .map(|(i, typ)| {
                Field {
                    name: symbols.from_str(&format!("_{}", i)),
                    typ: typ,
                }
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
    #[cfg_attr(feature = "serde_derive", serde(state))] pub kind: ArcKind,
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
pub struct Generic<Id> {
    #[cfg_attr(feature = "serde_derive", serde(state))] pub id: Id,
    #[cfg_attr(feature = "serde_derive", serde(state))] pub kind: ArcKind,
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
    #[cfg_attr(feature = "serde_derive", serde(state))] _typ: T,
    _marker: PhantomData<Id>,
}

impl<Id, T> Deref for Alias<Id, T>
where
    T: Deref<Target = Type<Id, T>>,
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
where
    T: From<Type<Id, T>>,
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
where
    T: From<Type<Id, T>>,
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
    #[cfg_attr(feature = "serde_derive", serde(state))] pub name: Id,
    /// Arguments to the alias
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub args: Vec<Generic<Id>>,
    /// The type that is being aliased
    #[cfg_attr(feature = "serde_derive", serde(state))]
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
    #[cfg_attr(feature = "serde_derive", serde(state))] pub name: Id,
    #[cfg_attr(feature = "serde_derive", serde(state))] pub typ: T,
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
    /// A type application with multiple arguments. For example,
    /// `Map String Int` would be represented as `App(Map, [String, Int])`.
    App(
        #[cfg_attr(feature = "serde_derive", serde(deserialize_state))]
        #[cfg_attr(feature = "serde_derive", serde(serialize_state))]
        T,
        #[cfg_attr(feature = "serde_derive",
                   serde(deserialize_state_with = "::serialization::deserialize_type_vec"))]
        #[cfg_attr(feature = "serde_derive",
                   serde(serialize_state_with = "::serialization::serialize_seq"))]
        AppVec<T>,
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
    Variable(
        #[cfg_attr(feature = "serde_derive", serde(state))] TypeVariable,
    ),
    /// A variable that needs to be instantiated with a fresh type variable
    /// when the binding is refered to.
    Generic(
        #[cfg_attr(feature = "serde_derive", serde(state))] Generic<Id>,
    ),
    Alias(
        #[cfg_attr(feature = "serde_derive", serde(state))] AliasRef<Id, T>,
    ),
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
                .map(|(i, typ)| {
                    Field {
                        name: symbols.from_str(&format!("_{}", i)),
                        typ: typ,
                    }
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
        let function: T = Type::builtin(BuiltinType::Function);
        args.into_iter().rev().fold(ret, |body, arg| {
            Type::app(function.clone(), collect![arg, body])
        })
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
            group: Arc::new(vec![
                AliasData {
                    name: name,
                    args: args,
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

    pub fn is_non_polymorphic_record(&self) -> bool {
        match *self {
            Type::Record(ref row) | Type::ExtendRow { rest: ref row, .. } => {
                row.is_non_polymorphic_record()
            }
            Type::EmptyRow => true,
            _ => false,
        }
    }

    pub fn pretty<'a>(&'a self, arena: &'a Arena<'a>) -> DocBuilder<'a, Arena<'a>>
    where
        Id: AsRef<str>,
    {
        top(self).pretty(arena)
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
            Type::App(ref id, _) => match **id {
                Type::Builtin(b) => Some(b.symbol()),
                _ => None,
            },
            Type::Builtin(b) => Some(b.symbol()),
            _ => None,
        }
    }

    pub fn kind(&self) -> Cow<ArcKind> {
        self.kind_(0)
    }

    fn kind_(&self, applied_args: usize) -> Cow<ArcKind> {
        let mut immediate_kind = match *self {
            Type::App(ref t, ref args) => t.kind_(args.len()),
            Type::Hole | Type::Opaque | Type::Builtin(_) | Type::Record(_) | Type::Variant(_) => {
                Cow::Owned(Kind::typ())
            }
            Type::EmptyRow | Type::ExtendRow { .. } => Cow::Owned(Kind::row().into()),
            Type::Variable(ref var) => Cow::Borrowed(&var.kind),
            Type::Generic(ref gen) => Cow::Borrowed(&gen.kind),
            // FIXME can be another kind
            Type::Ident(_) => Cow::Owned(Kind::typ()),
            Type::Alias(ref alias) => {
                return if alias.args.len() < applied_args {
                    alias.typ.kind_(applied_args - alias.args.len())
                } else {
                    let mut kind = alias.typ.kind_(0).into_owned();
                    for arg in &alias.args[applied_args..] {
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

    pub fn strong_count(typ: &ArcType<Id>) -> usize {
        Arc::strong_count(&typ.typ)
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


fn dt<'a, I, T>(prec: Prec, typ: &'a Type<I, T>) -> DisplayType<'a, I, T> {
    DisplayType {
        prec: prec,
        typ: typ,
    }
}

fn top<'a, I, T>(typ: &'a Type<I, T>) -> DisplayType<'a, I, T> {
    dt(Prec::Top, typ)
}

pub fn display_type<'a, I, T>(typ: &'a Type<I, T>) -> TypeFormatter<'a, I, T> {
    TypeFormatter {
        width: 80,
        typ: typ,
    }
}

pub struct DisplayType<'a, I: 'a, T: 'a> {
    prec: Prec,
    typ: &'a Type<I, T>,
}

pub struct TypeFormatter<'a, I, T>
where
    I: 'a,
    T: 'a,
{
    width: usize,
    typ: &'a Type<I, T>,
}

impl<'a, I, T> TypeFormatter<'a, I, T> {
    pub fn new(typ: &'a Type<I, T>) -> Self {
        TypeFormatter {
            width: 80,
            typ: typ,
        }
    }
}

impl<'a, I, T> TypeFormatter<'a, I, T> {
    pub fn width(mut self, width: usize) -> Self {
        self.width = width;
        self
    }
}

impl<'a, I, T> fmt::Display for TypeFormatter<'a, I, T>
where
    T: Deref<Target = Type<I, T>> + 'a,
    I: AsRef<str>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let arena = Arena::new();
        let mut s = Vec::new();
        dt(Prec::Top, self.typ)
            .pretty(&arena)
            .group()
            .1
            .render(self.width, &mut s)
            .map_err(|_| fmt::Error)?;
        write!(f, "{}", ::std::str::from_utf8(&s).expect("utf-8"))
    }
}

pub trait ToDoc<'a, A> {
    fn to_doc(&'a self, allocator: &'a A) -> DocBuilder<'a, A>
    where
        A: DocAllocator<'a>;
}

impl<'a, I> ToDoc<'a, Arena<'a>> for ArcType<I>
where
    I: AsRef<str>,
{
    fn to_doc(&'a self, allocator: &'a Arena<'a>) -> DocBuilder<'a, Arena<'a>> {
        dt(Prec::Top, self).pretty(allocator)
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

impl<'a, I, T> DisplayType<'a, I, T>
where
    T: Deref<Target = Type<I, T>> + 'a,
{
    pub fn pretty(&self, arena: &'a Arena<'a>) -> DocBuilder<'a, Arena<'a>>
    where
        I: AsRef<str>,
    {
        use pretty_print::ident;

        const INDENT: usize = 4;

        let p = self.prec;
        match *self.typ {
            Type::Hole => arena.text("_"),
            Type::Opaque => arena.text("<opaque>"),
            Type::Variable(ref var) => arena.text(format!("{}", var.id)),
            Type::Generic(ref gen) => arena.text(gen.id.as_ref()),
            Type::App(ref t, ref args) => match self.typ.as_function() {
                Some((arg, ret)) => {
                    let doc = chain![arena;
                            dt(Prec::Function, arg).pretty(arena).group(),
                            arena.space(),
                            "-> ",
                            top(ret).pretty(arena)
                        ];

                    p.enclose(Prec::Function, arena, doc)
                }
                None => {
                    let doc = dt(Prec::Top, t).pretty(arena);
                    let arg_doc = arena.concat(args.iter().map(|arg| {
                        arena
                            .space()
                            .append(dt(Prec::Constructor, arg).pretty(arena))
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
                                            dt(Prec::Constructor, &arg).pretty(arena)];
                        }
                    },
                    ref typ => panic!("Unexpected type `{}` in variant", typ),
                };

                p.enclose(Prec::Constructor, arena, doc).group()
            }
            Type::Builtin(ref t) => match *t {
                BuiltinType::Function => chain![arena; "(", t.to_str(), ")"],
                _ => arena.text(t.to_str()),
            },
            Type::Record(ref row) => {
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
                    Type::ExtendRow { .. } => doc.append(top(row).pretty(arena)).nest(INDENT),
                    _ => doc.append(arena.space())
                        .append("| ")
                        .append(top(row).pretty(arena))
                        .nest(INDENT),
                };
                if !empty_fields {
                    doc = doc.append(arena.space());
                }

                doc.append("}").group()
            }
            Type::ExtendRow { ref fields, .. } => {
                let mut doc = arena.nil();
                let mut typ = self.typ;

                while let Type::ExtendRow {
                    ref types,
                    ref rest,
                    ..
                } = *typ
                {
                    for (i, field) in types.iter().enumerate() {
                        let f = chain![arena;
                            field.name.as_ref(),
                            arena.space(),
                            arena.concat(field.typ.args.iter().map(|arg| {
                                arena.text(arg.id.as_ref()).append(" ")
                            })),
                            arena.text("= ")
                                 .append(top(&field.typ.typ).pretty(arena)),
                            if i + 1 != types.len() || !fields.is_empty() {
                                arena.text(",")
                            } else {
                                arena.nil()
                            }].group();
                        doc = doc.append(arena.space()).append(f);
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
                } = *typ
                {
                    for (i, field) in fields.iter().enumerate() {
                        let mut rhs = top(&*field.typ).pretty(arena);
                        match *field.typ {
                            // Records handle nesting on their own
                            Type::Record(_) => (),
                            _ => rhs = rhs.nest(INDENT),
                        }
                        let f = chain![arena;
                            ident(arena, field.name.as_ref()),
                            " : ",
                            rhs.group(),
                            if i + 1 != fields.len() {
                                arena.text(",")
                            } else {
                                arena.nil()
                            }].group();
                        doc = doc.append(arena.space()).append(f);
                        typ = rest;
                    }
                }
                match *typ {
                    Type::EmptyRow => doc,
                    _ => doc.append(arena.space())
                        .append("| ")
                        .append(top(typ).pretty(arena)),
                }
            }
            // This should not be displayed normally as it should only exist in `ExtendRow`
            // which handles `EmptyRow` explicitly
            Type::EmptyRow => arena.text("EmptyRow"),
            Type::Ident(ref id) => arena.text(id.as_ref()),
            Type::Alias(ref alias) => arena.text(alias.name.as_ref()),
        }
    }
}

impl<I, T> fmt::Display for Type<I, T>
where
    I: AsRef<str>,
    T: Deref<Target = Type<I, T>>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", TypeFormatter::new(self))
    }
}

pub fn pretty_print<'a, I, T>(
    arena: &'a Arena<'a>,
    typ: &'a Type<I, T>,
) -> DocBuilder<'a, Arena<'a>>
where
    I: AsRef<str>,
    T: Deref<Target = Type<I, T>>,
{
    dt(Prec::Top, typ).pretty(arena)
}

pub fn walk_type<I, T, F>(typ: &T, mut f: F)
where
    F: FnMut(&T),
    T: Deref<Target = Type<I, T>>,
{
    f.walk(typ)
}

pub fn walk_type_<I, T, F: ?Sized>(typ: &T, f: &mut F)
where
    F: Walker<T>,
    T: Deref<Target = Type<I, T>>,
{
    match **typ {
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

pub trait Walker<T> {
    fn walk(&mut self, typ: &T);
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
pub struct ControlVisitation<F>(pub F);

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

impl<I, T, F: ?Sized> Walker<T> for F
where
    F: FnMut(&T),
    T: Deref<Target = Type<I, T>>,
{
    fn walk(&mut self, typ: &T) {
        self(typ);
        walk_type_(typ, self)
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

pub fn walk_move_type_opt<F: ?Sized, I, T>(typ: &Type<I, T>, f: &mut F) -> Option<T>
where
    F: TypeVisitor<I, T>,
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

pub fn translate_type<Id, T, U>(cache: &TypeCache<Id, U>, typ: &Type<Id, T>) -> U
where
    T: Deref<Target = Type<Id, T>>,
    U: From<Type<Id, U>> + Clone,
    Id: Clone,
{
    fn translate_alias<Id, T, U>(
        cache: &TypeCache<Id, U>,
        alias: &AliasData<Id, T>,
    ) -> AliasData<Id, U>
    where
        T: Deref<Target = Type<Id, T>>,
        U: From<Type<Id, U>> + Clone,
        Id: Clone,
    {
        AliasData::new(
            alias.name.clone(),
            alias.args.clone(),
            translate_type(cache, &alias.typ),
        )
    }
    match *typ {
        Type::App(ref f, ref args) => Type::app(
            translate_type(cache, f),
            args.iter().map(|typ| translate_type(cache, typ)).collect(),
        ),
        Type::Record(ref row) => U::from(Type::Record(translate_type(cache, row))),
        Type::Variant(ref row) => U::from(Type::Variant(translate_type(cache, row))),
        Type::ExtendRow {
            ref types,
            ref fields,
            ref rest,
        } => Type::extend_row(
            types
                .iter()
                .map(|field| {
                    Field {
                        name: field.name.clone(),
                        typ: Alias::from(translate_alias(cache, &field.typ)),
                    }
                })
                .collect(),
            fields
                .iter()
                .map(|field| {
                    Field {
                        name: field.name.clone(),
                        typ: translate_type(cache, typ),
                    }
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
        // This is not quite correct but currently only `AstType` -> `ArcType` translations are needed
        // so this will not be used
        Type::Alias(ref alias) => U::from(Type::Alias(AliasRef {
            index: 0,
            group: Arc::new(vec![translate_alias(cache, alias)]),
        })),
        Type::EmptyRow => cache.empty_row(),
    }
}
