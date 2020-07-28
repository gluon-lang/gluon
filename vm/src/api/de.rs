//! _This module requires Gluon to be built with the `serde` feature._

use std::{cell::RefCell, fmt, marker::PhantomData, result::Result as StdResult};

use crate::base::{
    resolve,
    symbol::Symbol,
    types::{ctor_args, ArcType, BuiltinType, NullInterner, Type, TypeEnv, TypeExt},
};

use crate::api::{Getable, ValueRef, VmType};
use crate::thread::{RootedThread, RootedValue, Thread, ThreadInternal};
use crate::{Error as VmError, Result, Variants};

use crate::serde::de::{
    self, DeserializeOwned, DeserializeSeed, EnumAccess, Error, IntoDeserializer, MapAccess,
    SeqAccess, VariantAccess, Visitor,
};

impl de::Error for VmError {
    fn custom<T>(msg: T) -> Self
    where
        T: fmt::Display,
    {
        VmError::Message(format!("{}", msg))
    }
}

/**
`Getable` wrapper which extracts `T` by deserializing it into a rust value.

## Struct

```
#[macro_use]
extern crate serde_derive;

#[macro_use]
extern crate gluon_vm;

use gluon::{Thread, ThreadExt, new_vm};
use gluon::base::types::ArcType;
use gluon::vm::api::VmType;
use gluon::vm::api::de::De;
# fn main() {

#[derive(Debug, PartialEq, Deserialize)]
struct Vec2 {
    x: f64,
    y: f64
}

impl VmType for Vec2 {
    type Type = Self;

    fn make_type(thread: &Thread) -> ArcType {
        field_decl!{ x, y }
        type T = record_type! {
            x => f64,
            y => f64
        };
        T::make_type(thread)
    }
}

# if ::std::env::var("GLUON_PATH").is_err() {
#     ::std::env::set_var("GLUON_PATH", "..");
# }

let thread = new_vm();
# thread.get_database_mut().implicit_prelude(false);

let (De(vec), _) = thread
    .run_expr::<De<Vec2>>("test", "{ x = 1.0, y = 2.0 }")
    .unwrap_or_else(|err| panic!("{}", err));
assert_eq!(vec, Vec2 {
        x: 1.0,
        y: 2.0
    });

# }
```

## Enum

```
#[macro_use]
extern crate serde_derive;

use gluon::{Thread, ThreadExt, new_vm};
use gluon::base::types::ArcType;
use gluon::vm::api::VmType;
use gluon::vm::api::de::De;
# fn main() {

#[derive(Debug, PartialEq, Deserialize)]
enum Enum {
    A(i32),
    B { string: String, test: f64 },
}

impl VmType for Enum {
    type Type = Self;

    fn make_type(thread: &Thread) -> ArcType {
        // Use the enum type declared in gluon
        thread.find_type_info("test.Enum").unwrap().into_type()
    }
}

# if ::std::env::var("GLUON_PATH").is_err() {
#     ::std::env::set_var("GLUON_PATH", "..");
# }

let thread = new_vm();
# thread.get_database_mut().implicit_prelude(false);

thread
    .load_script(
        "test",
        r#" type Enum = | A Int | B { string : String, test : Float } in { Enum } "#,
    )
    .unwrap_or_else(|err| panic!("{}", err));

let (De(enum_), _) = thread
    .run_expr::<De<Enum>>(
        "test",
        r#" let { Enum } = import! "test" in A 123 "#,
    )
    .unwrap_or_else(|err| panic!("{}", err));
assert_eq!(enum_, Enum::A(123));

// The field names of record variants are ignored so make sure the fields are declared correctly
let (De(enum_), _) = thread
    .run_expr::<De<Enum>>(
        "test",
        r#" let { Enum } = import! "test" in B { string = "abc", test = 3.14 } "#,
    )
    .unwrap_or_else(|err| panic!("{}", err));
assert_eq!(
    enum_,
    Enum::B {
        string: "abc".to_string(),
        test: 3.14,
    }
);

# }
```
*/

pub struct De<T>(pub T);

impl<T> VmType for De<T>
where
    T: VmType,
{
    type Type = T::Type;

    fn make_type(thread: &Thread) -> ArcType {
        T::make_type(thread)
    }
}

impl<'vm, 'value, T> Getable<'vm, 'value> for De<T>
where
    T: VmType,
    T: DeserializeOwned,
{
    impl_getable_simple!();

    fn from_value(thread: &'vm Thread, value: Variants<'value>) -> Self {
        let typ = T::make_type(thread);
        match from_value(thread, value, &typ).map(De) {
            Ok(v) => v,
            Err(err) => ice!("Getable::from_value for De: {}", err),
        }
    }
}

/// Deserializes `T` from a gluon value assuming that `value` is of type `typ`.
pub fn from_value<T>(thread: &Thread, value: Variants, typ: &ArcType) -> Result<T>
where
    T: DeserializeOwned,
{
    let env = thread.get_env();
    let mut deserializer = Deserializer::from_value(thread, &env, value, typ);
    T::deserialize(&mut deserializer)
}

#[derive(Clone)]
struct State<'de> {
    thread: &'de Thread,
    env: &'de dyn TypeEnv<Type = ArcType>,
}

#[derive(Clone)]
struct Deserializer<'de, 't> {
    state: State<'de>,
    input: Variants<'de>,
    typ: &'t ArcType,
}

impl<'de, 't> Deserializer<'de, 't> {
    fn from_value(
        thread: &'de Thread,
        env: &'de dyn TypeEnv<Type = ArcType>,
        input: Variants<'de>,
        typ: &'t ArcType,
    ) -> Self {
        Deserializer {
            state: State {
                thread: thread,
                env: env,
            },
            input: input,
            typ: typ,
        }
    }

    fn deserialize_builtin<T, F, R>(&self, expected: BuiltinType, visit: F) -> Result<R>
    where
        F: FnOnce(T) -> Result<R>,
        T: Getable<'de, 'de>,
    {
        self.deserialize_leaf(|t| *t == Type::Builtin(expected), visit)
    }

    fn deserialize_leaf<T, E, F, R>(&self, expected: E, visit: F) -> Result<R>
    where
        E: FnOnce(&Type<Symbol, ArcType>) -> bool,
        F: FnOnce(T) -> Result<R>,
        T: Getable<'de, 'de>,
    {
        let typ = resolve::remove_aliases_cow(self.state.env, &mut NullInterner, self.typ);
        if expected(&typ) {
            visit(T::from_value(self.state.thread, self.input.clone()))
        } else {
            Err(VmError::Message(format!(
                "Unable to deserialize `{}`",
                self.typ
            )))
        }
    }
}

thread_local! {
    static VALUE_TRANSFER: RefCell<Option<RootedValue<RootedThread>>> = RefCell::new(None);
}

/// Allows deserializing a `Value` as-is. Only works with the `Deserializer` defined in this module
pub fn deserialize_raw_value<'de, D>(
    deserializer: D,
) -> StdResult<RootedValue<RootedThread>, D::Error>
where
    D: de::Deserializer<'de>,
{
    use crate::serde::Deserialize;

    VALUE_TRANSFER.with(|t| {
        assert!(t.borrow().is_none());
    });

    RawValueDeserialize::deserialize(deserializer)?;

    let opt_value = VALUE_TRANSFER.with(|t| t.borrow_mut().take());
    opt_value.ok_or_else(|| D::Error::custom("Unable to deserialize raw value"))
}

impl<'de> de::Deserialize<'de> for RootedValue<RootedThread> {
    fn deserialize<D>(deserializer: D) -> StdResult<Self, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        deserialize_raw_value(deserializer)
    }
}

#[derive(Deserialize)]
struct RawValueDeserialize;

impl<'de, 't, 'a> de::Deserializer<'de> for &'a mut Deserializer<'de, 't> {
    type Error = VmError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Array(ref array) => match array.as_slice::<u8>() {
                Some(_) => self.deserialize_bytes(visitor),
                _ => self.deserialize_seq(visitor),
            },
            ValueRef::Byte(_) => self.deserialize_u8(visitor),
            ValueRef::Data(_) => {
                let typ = resolve::remove_aliases_cow(self.state.env, &mut NullInterner, self.typ);
                let mut deserializer = Deserializer {
                    typ: &typ,
                    ..self.clone()
                };
                if let Type::Record(_) = **typ {
                    deserializer.deserialize_enum("", &[], visitor)
                } else {
                    deserializer.deserialize_map(visitor)
                }
            }
            ValueRef::Float(_) => self.deserialize_f64(visitor),
            ValueRef::Int(_) => self.deserialize_i64(visitor),
            ValueRef::String(ref s) => visitor.visit_borrowed_str(s),
            ValueRef::Closure(_)
            | ValueRef::Userdata(_)
            | ValueRef::Thread(_)
            | ValueRef::Internal => Err(VmError::Message(format!(
                "Unable to deserialize `{}`",
                self.typ
            ))),
        }
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Data(data) => visitor.visit_bool(data.tag() != 0),
            _ => Err(VmError::Message(format!("Unable to deserialize bool"))),
        }
    }

    // The `parse_signed` function is generic over the integer type `T` so here
    // it is invoked with `T=i8`. The next 8 methods are similar.
    fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Byte(b) => visitor.visit_i8(b as i8),
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Byte(b) => visitor.visit_i16(b as i16),
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Int(b) => visitor.visit_i32(b as i32),
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Int(b) => visitor.visit_i64(b as i64),
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Byte(b) => visitor.visit_u8(b),
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Byte(b) => visitor.visit_u16(b as u16),
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Int(b) => visitor.visit_u32(b as u32),
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Int(b) => visitor.visit_u64(b as u64),
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Float(f) => visitor.visit_f32(f as f32),
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Float(f) => visitor.visit_f64(f),
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        use std::char::from_u32;
        let typ = resolve::remove_aliases_cow(self.state.env, &mut NullInterner, self.typ);
        match (self.input.as_ref(), &**typ) {
            (ValueRef::Int(c), &Type::Builtin(BuiltinType::Char)) => match from_u32(c as u32) {
                Some(c) => visitor.visit_char(c),
                None => self.deserialize_any(visitor),
            },
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_builtin(BuiltinType::String, |s| visitor.visit_borrowed_str(s))
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_str(visitor)
    }

    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_leaf(
            |typ| match *typ {
                Type::App(ref func, ref args) if args.len() == 1 => {
                    **func == Type::Builtin(BuiltinType::Array)
                        && *args[0] == Type::Builtin(BuiltinType::Byte)
                }
                _ => false,
            },
            |s| visitor.visit_bytes(s),
        )
    }

    fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_bytes(visitor)
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let typ = resolve::canonical_alias(self.state.env, &mut NullInterner, self.typ, |alias| {
            alias.name.name().as_str() == "std.types.Option"
        });
        let option_inner_typ = match **typ {
            Type::App(ref func, ref args) if args.len() == 1 => match **func {
                Type::Alias(ref alias) if alias.name.name().as_str() == "std.types.Option" => {
                    Some(&args[0])
                }
                _ => None,
            },
            _ => None,
        };
        // If the type is not `Option` we just visit the value itself
        match option_inner_typ {
            Some(typ) => match &self.input.as_ref() {
                ValueRef::Data(data) if data.tag() == 0 => visitor.visit_none(),
                ValueRef::Data(data) if data.tag() == 1 => visitor.visit_some(&mut Deserializer {
                    state: self.state.clone(),
                    typ: typ,
                    input: data.get_variant(0).unwrap(),
                }),
                _ => self.deserialize_any(visitor),
            },
            None => visitor.visit_some(self),
        }
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match &self.input.as_ref() {
            ValueRef::Data(data) if data.tag() == 0 => visitor.visit_unit(),
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_unit_struct<V>(self, name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        if name == "RawValueDeserialize" {
            VALUE_TRANSFER.with(|t| {
                let mut store = t.borrow_mut();
                assert!(store.is_none());
                *store = Some(self.state.thread.root_value(self.input.clone()));
            });
            visitor.visit_unit()
        } else {
            self.deserialize_unit(visitor)
        }
    }

    fn deserialize_newtype_struct<V>(self, _name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_newtype_struct(self)
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let typ = resolve::remove_aliases_cow(self.state.env, &mut NullInterner, self.typ);
        match (&self.input.as_ref(), &**typ) {
            (ValueRef::Array(values), &Type::App(_, ref args)) if args.len() == 1 => visitor
                .visit_seq(SeqDeserializer::new(
                    self.state.clone(),
                    values.as_ref().iter().map(|variant| (variant, &args[0])),
                )),
            (ValueRef::Data(data), &Type::Variant(ref row)) => {
                match row.row_iter().nth(data.tag() as usize) {
                    Some(field) => {
                        let iter = (0..data.len())
                            .map(|i| data.get_variant(i).unwrap())
                            .zip(ctor_args(&field.typ));
                        visitor.visit_seq(SeqDeserializer::new(self.state.clone(), iter))
                    }
                    None => self.deserialize_any(visitor),
                }
            }
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_tuple<V>(self, _len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_seq(visitor)
    }

    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_seq(visitor)
    }

    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let typ = resolve::remove_aliases_cow(self.state.env, &mut NullInterner, self.typ);
        match (self.input.as_ref(), &**typ) {
            (ValueRef::Data(ref data), &Type::Record { .. }) => {
                let iter = typ.row_iter().flat_map(|field| {
                    data.lookup_field(self.state.thread, field.name.as_ref())
                        .map(|variant| (variant, &field.name, &field.typ))
                });
                visitor.visit_map(MapDeserializer::new(self.state.clone(), iter))
            }
            _ => self.deserialize_any(visitor),
        }
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_map(visitor)
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_enum(Enum::new(self))
    }

    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_str(visitor)
    }

    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_any(visitor)
    }
}

struct SeqDeserializer<'de, 't, I> {
    state: State<'de>,
    iter: I,
    _marker: PhantomData<&'t ()>,
}

impl<'de, 't, I> SeqDeserializer<'de, 't, I> {
    fn new(state: State<'de>, iter: I) -> Self {
        SeqDeserializer {
            state: state,
            iter: iter,
            _marker: PhantomData,
        }
    }
}

impl<'de, 't, I> SeqAccess<'de> for SeqDeserializer<'de, 't, I>
where
    I: Iterator<Item = (Variants<'de>, &'t ArcType)>,
{
    type Error = VmError;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>>
    where
        T: DeserializeSeed<'de>,
    {
        match self.iter.next() {
            Some((value, typ)) => seed
                .deserialize(&mut Deserializer {
                    state: self.state.clone(),
                    input: value,
                    typ: typ,
                })
                .map(Some),
            None => Ok(None),
        }
    }
}

struct MapDeserializer<'de, 't, I> {
    state: State<'de>,
    iter: I,
    value: Option<(Variants<'de>, &'t ArcType)>,
}

impl<'de, 't, I> MapDeserializer<'de, 't, I> {
    fn new(state: State<'de>, iter: I) -> Self {
        MapDeserializer {
            state: state,
            iter: iter,
            value: None,
        }
    }
}

impl<'de, 'a, 't, I> MapAccess<'de> for MapDeserializer<'de, 't, I>
where
    I: Iterator<Item = (Variants<'de>, &'t Symbol, &'t ArcType)>,
{
    type Error = VmError;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>>
    where
        K: DeserializeSeed<'de>,
    {
        match self.iter.next() {
            Some((value, field, typ)) => {
                self.value = Some((value, typ));
                seed.deserialize(field.as_str().into_deserializer())
                    .map(Some)
            }
            None => Ok(None),
        }
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value>
    where
        V: DeserializeSeed<'de>,
    {
        match self.value.take() {
            Some((value, typ)) => seed.deserialize(&mut Deserializer {
                state: self.state.clone(),
                input: value,
                typ: typ,
            }),
            None => Err(Self::Error::custom("Unable to deserialize value")),
        }
    }
}

struct Enum<'a, 'de: 'a, 't: 'a> {
    de: &'a mut Deserializer<'de, 't>,
}

impl<'a, 'de, 't> Enum<'a, 'de, 't> {
    fn new(de: &'a mut Deserializer<'de, 't>) -> Self {
        Enum { de }
    }
}

impl<'a, 'b, 'de, 't> de::Deserializer<'de> for &'b mut Enum<'a, 'de, 't> {
    type Error = VmError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.de.input.as_ref() {
            ValueRef::Data(data) => visitor.visit_u32(data.tag()),
            _ => Err(Self::Error::custom("Unable to deserialize tag")),
        }
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let tag = match self.de.input.as_ref() {
            ValueRef::Data(data) => data.tag(),
            _ => return Err(Self::Error::custom("Unable to deserialize tag")),
        };
        let typ = resolve::remove_aliases_cow(self.de.state.env, &mut NullInterner, self.de.typ);
        match **typ {
            Type::Variant(ref variants) => {
                let variant = variants
                    .row_iter()
                    .nth(tag as usize)
                    .ok_or_else(|| Self::Error::custom("Unable to deserialize tag"))?;
                visitor.visit_str(variant.name.as_ref())
            }
            _ => return Err(Self::Error::custom("Unable to deserialize tag")),
        }
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_str(visitor)
    }

    forward_to_deserialize_any! {
        bool i8 i16 i32 i64 u8 u16 u32 u64 f32 f64 char bytes
        byte_buf option unit unit_struct newtype_struct seq tuple
        tuple_struct map struct enum identifier ignored_any
    }
}

impl<'a, 'de, 't> EnumAccess<'de> for Enum<'a, 'de, 't> {
    type Error = VmError;
    type Variant = Self;

    fn variant_seed<V>(mut self, seed: V) -> Result<(V::Value, Self::Variant)>
    where
        V: DeserializeSeed<'de>,
    {
        seed.deserialize(&mut self).map(|value| (value, self))
    }
}

impl<'de, 'a, 't> VariantAccess<'de> for Enum<'a, 'de, 't> {
    type Error = VmError;

    fn unit_variant(self) -> Result<()> {
        Ok(())
    }

    fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value>
    where
        T: DeserializeSeed<'de>,
    {
        let typ = resolve::remove_aliases_cow(self.de.state.env, &mut NullInterner, self.de.typ);
        match (&self.de.input.as_ref(), &**typ) {
            (ValueRef::Data(data), &Type::Variant(ref row)) => {
                match row.row_iter().nth(data.tag() as usize) {
                    Some(field) => seed.deserialize(&mut Deserializer {
                        input: data.get_variant(0).ok_or_else(|| {
                            VmError::Message("Expected variant to have a value argument".into())
                        })?,
                        typ: ctor_args(&field.typ).next().ok_or_else(|| {
                            VmError::Message("Expected variant to have a type argument".into())
                        })?,
                        ..self.de.clone()
                    }),
                    None => seed.deserialize(self.de),
                }
            }
            _ => seed.deserialize(self.de),
        }
    }

    fn tuple_variant<V>(self, _len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        de::Deserializer::deserialize_seq(self.de, visitor)
    }

    fn struct_variant<V>(self, _fields: &'static [&'static str], visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let typ = resolve::remove_aliases_cow(self.de.state.env, &mut NullInterner, self.de.typ);
        let input = self.de.input.as_ref();
        let (data, row) = match (&input, &**typ) {
            (ValueRef::Data(data), Type::Variant(row)) => (data, row),
            _ => {
                return Err(VmError::Message(format!(
                    "Unable to deserialize `{}`",
                    self.de.typ
                )))
            }
        };

        let field = row
            .row_iter()
            .nth(data.tag() as usize)
            .ok_or_else(|| VmError::Message(format!("Unable to deserialize `{}`", self.de.typ)))?;

        let typ = resolve::remove_aliases_cow(self.de.state.env, &mut NullInterner, &field.typ);
        let variant = data.get_variant(0).map(|d| d.as_ref());
        let (data, typ) = match (&variant, &**typ) {
            (Some(ValueRef::Data(data)), Type::Function(_, typ, _)) => (data, typ),
            _ => {
                return Err(VmError::Message(format!(
                    "Unable to deserialize `{}`",
                    self.de.typ
                )))
            }
        };

        let iter = typ.row_iter().flat_map(|field| {
            data.lookup_field(self.de.state.thread, field.name.as_ref())
                .map(|variant| (variant, &field.name, &field.typ))
        });
        visitor.visit_map(MapDeserializer::new(self.de.state.clone(), iter))
    }
}
