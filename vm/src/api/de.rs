use std::fmt;

use base::resolve;
use base::types::{ArcType, BuiltinType, Type, TypeEnv};
use base::symbol::Symbol;

use {Error as VmError, Result, Variants};
use api::{Getable, ValueRef, VmType};
use thread::{Thread, ThreadInternal};

use serde::de::{self, DeserializeSeed, DeserializeOwned, Visitor, SeqAccess, MapAccess,
                EnumAccess, VariantAccess, IntoDeserializer, Error};

impl de::Error for VmError {
    fn custom<T>(msg: T) -> Self
    where
        T: fmt::Display,
    {
        VmError::Message(format!("{}", msg))
    }
}

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

impl<'vm, T> Getable<'vm> for De<T>
where
    T: VmType,
    T: DeserializeOwned,
{
    fn from_value(thread: &'vm Thread, value: Variants) -> Option<Self> {
        let env = thread.global_env().get_env();
        let typ = T::make_type(thread);
        let mut deserializer = Deserializer {
            state: State {
                thread: thread,
                env: &*env,
            },
            input: value,
            typ: &typ,
        };
        T::deserialize(&mut deserializer).map(De).ok()
    }
}


#[derive(Clone)]
struct State<'de> {
    thread: &'de Thread,
    env: &'de TypeEnv,
}
pub struct Deserializer<'de, 't> {
    state: State<'de>,
    input: Variants<'de>,
    typ: &'t ArcType,
}

impl<'de, 't> Deserializer<'de, 't> {
    pub fn from_value(
        thread: &'de Thread,
        env: &'de TypeEnv,
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

    pub fn deserialize_builtin<T, F, R>(&self, expected: BuiltinType, visit: F) -> Result<R>
    where
        F: FnOnce(T) -> Result<R>,
        T: Getable<'de>,
    {
        self.deserialize_leaf(|t| *t == Type::Builtin(expected), visit)
    }

    pub fn deserialize_leaf<T, E, F, R>(&self, expected: E, visit: F) -> Result<R>
    where
        E: FnOnce(&Type<Symbol, ArcType>) -> bool,
        F: FnOnce(T) -> Result<R>,
        T: Getable<'de>,
    {
        let typ = resolve::remove_aliases_cow(self.state.env, self.typ);
        match T::from_value(self.state.thread, self.input) {
            Some(c) => {
                if expected(&typ) {
                    visit(c)
                } else {
                    Err(Error::custom("Cant deserialize type"))
                }
            }
            _ => Err(Error::custom("Cant deserialize type")),
        }
    }
}


impl<'de, 't, 'a> de::Deserializer<'de> for &'a mut Deserializer<'de, 't> {
    type Error = VmError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Array(ref array) => {
                match array.as_slice::<u8>() {
                    Some(_) => self.deserialize_bytes(visitor),
                    _ => self.deserialize_seq(visitor),
                }
            }
            ValueRef::Byte(_) => self.deserialize_u8(visitor),
            ValueRef::Data(_) => {
                if let Type::Record(_) = **resolve::remove_aliases_cow(self.state.env, self.typ) {
                    self.deserialize_enum("", &[], visitor)
                } else {
                    self.deserialize_map(visitor)
                }
            }
            ValueRef::Float(_) => self.deserialize_f64(visitor),
            ValueRef::Int(_) => self.deserialize_i64(visitor),
            ValueRef::String(ref s) => visitor.visit_borrowed_str(s),
            ValueRef::Tag(_) => self.deserialize_enum("", &[], visitor),
            ValueRef::Userdata(_) |
            ValueRef::Internal => Err(Self::Error::custom("Cant deserialize type")),
        }
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Tag(t) => visitor.visit_bool(t != 0),
            _ => Err(Self::Error::custom("Cant deserialize type")),
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
            _ => Err(Self::Error::custom("Cant deserialize type")),
        }
    }

    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Byte(b) => visitor.visit_i16(b as i16),
            _ => Err(Self::Error::custom("Cant deserialize type")),
        }
    }

    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Int(b) => visitor.visit_i32(b as i32),
            _ => Err(Self::Error::custom("Cant deserialize type")),
        }
    }

    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Int(b) => visitor.visit_i64(b as i64),
            _ => Err(Self::Error::custom("Cant deserialize type")),
        }
    }

    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Byte(b) => visitor.visit_u8(b),
            _ => Err(Self::Error::custom("Cant deserialize type")),
        }
    }

    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Byte(b) => visitor.visit_u16(b as u16),
            _ => Err(Self::Error::custom("Cant deserialize type")),
        }
    }

    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Int(b) => visitor.visit_u32(b as u32),
            _ => Err(Self::Error::custom("Cant deserialize type")),
        }
    }

    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Int(b) => visitor.visit_u64(b as u64),
            _ => Err(Self::Error::custom("Cant deserialize type")),
        }
    }

    fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Float(f) => visitor.visit_f32(f as f32),
            _ => Err(Self::Error::custom("Cant deserialize type")),
        }
    }

    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Float(f) => visitor.visit_f64(f),
            _ => Err(Self::Error::custom("Cant deserialize type")),
        }
    }

    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        use std::char::from_u32;
        let typ = resolve::remove_aliases_cow(self.state.env, self.typ);
        match (self.input.as_ref(), &**typ) {
            (ValueRef::Int(c), &Type::Builtin(BuiltinType::Char)) => {
                match from_u32(c as u32) {
                    Some(c) => visitor.visit_char(c),
                    None => Err(Self::Error::custom("Cant deserialize type")),
                }
            }
            _ => Err(Self::Error::custom("Cant deserialize type")),
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
                    **func == Type::Builtin(BuiltinType::Array) &&
                        *args[0] == Type::Builtin(BuiltinType::Byte)
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
        let typ = resolve::canonical_alias(self.state.env, self.typ, |alias| {
            alias.name.declared_name() == "std.types.Option"
        });
        let typ = match **typ {
            Type::App(ref func, ref args) if args.len() == 1 => {
                match **func {
                    Type::Alias(ref alias) if alias.name.declared_name() == "std.types.Option" => {
                        args[0].clone()
                    }
                    _ => return Err(Self::Error::custom("Expected `Option` type")),
                }
            }
            _ => return Err(Self::Error::custom("Expected `Option` type")),
        };
        match self.input.as_ref() {
            ValueRef::Tag(0) => visitor.visit_none(),
            ValueRef::Data(data) if data.tag() == 1 => {
                visitor.visit_some(&mut Deserializer {
                    state: self.state.clone(),
                    typ: &typ,
                    input: data.get_variants(0).unwrap(),
                })
            }
            _ => Err(Self::Error::custom("Cant deserialize type")),
        }
    }

    // In Serde, unit means an anonymous value containing no data.
    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input.as_ref() {
            ValueRef::Tag(0) => visitor.visit_unit(),
            _ => Err(Self::Error::custom("Cant deserialize type")),
        }
    }

    // Unit struct means a named value containing no data.
    fn deserialize_unit_struct<V>(self, _name: &'static str, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_unit(visitor)
    }

    // As is done here, serializers are encouraged to treat newtype structs as
    // insignificant wrappers around the data they contain. That means not
    // parsing anything other than the contained value.
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
        let typ = resolve::remove_aliases_cow(self.state.env, self.typ);
        match (self.input.as_ref(), &**typ) {
            (ValueRef::Array(values), &Type::App(_, ref args)) if args.len() == 1 => {
                visitor.visit_seq(SeqDeserializer::new(
                    self.state.clone(),
                    &args[0],
                    values.iter(),
                ))
            }
            _ => Err(Self::Error::custom("Cant deserialize type")),
        }
    }

    fn deserialize_tuple<V>(self, _len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_seq(visitor)
    }

    // Tuple structs look just like sequences in JSON.
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

    // Much like `deserialize_seq` but calls the visitors `visit_map` method
    // with a `MapAccess` implementation, rather than the visitor's `visit_seq`
    // method with a `SeqAccess` implementation.
    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let typ = resolve::remove_aliases_cow(self.state.env, self.typ);
        match (self.input.as_ref(), &**typ) {
            (ValueRef::Data(ref data), &Type::Record { .. }) => {
                let iter = (0..data.len())
                    .map(|i| data.get_variants(i).unwrap())
                    .zip(typ.row_iter())
                    .map(|(value, field)| (value, &field.name, &field.typ));
                visitor.visit_map(MapDeserializer::new(self.state.clone(), iter))
            }
            _ => Err(Self::Error::custom("Cant deserialize type")),
        }
    }

    // Structs look just like maps in JSON.
    //
    // Notice the `fields` parameter - a "struct" in the Serde data model means
    // that the `Deserialize` implementation is required to know what the fields
    // are before even looking at the input data. Any key-value pairing in which
    // the fields cannot be known ahead of time is probably a map.
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

    // An identifier in Serde is the type that identifies a field of a struct or
    // the variant of an enum. In JSON, struct fields and enum variants are
    // represented as strings. In other formats they may be represented as
    // numeric indices.
    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_str(visitor)
    }

    // Like `deserialize_any` but indicates to the `Deserializer` that it makes
    // no difference which `Visitor` method is called because the data is
    // ignored.
    //
    // Some deserializers are able to implement this more efficiently than
    // `deserialize_any`, for example by rapidly skipping over matched
    // delimiters without paying close attention to the data in between.
    //
    // Some formats are not able to implement this at all. Formats that can
    // implement `deserialize_any` and `deserialize_ignored_any` are known as
    // self-describing.
    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_any(visitor)
    }
}

struct SeqDeserializer<'de, 't, I> {
    state: State<'de>,
    typ: &'t ArcType,
    iter: I,
}

impl<'de, 't, I> SeqDeserializer<'de, 't, I> {
    fn new(state: State<'de>, typ: &'t ArcType, iter: I) -> Self {
        SeqDeserializer {
            state: state,
            typ: typ,
            iter: iter,
        }
    }
}

// `SeqAccess` is provided to the `Visitor` to give it the ability to iterate
// through elements of the sequence.
impl<'de, 't, I> SeqAccess<'de> for SeqDeserializer<'de, 't, I>
where
    I: Iterator<Item = Variants<'de>>,
{
    type Error = VmError;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>>
    where
        T: DeserializeSeed<'de>,
    {
        match self.iter.next() {
            Some(value) => {
                seed.deserialize(&mut Deserializer {
                    state: self.state.clone(),
                    input: value,
                    typ: self.typ,
                }).map(Some)
            }
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

// `MapAccess` is provided to the `Visitor` to give it the ability to iterate
// through entries of the map.
impl<'de, 'a, 't, I> MapAccess<'de> for MapDeserializer<'de, 't, I>
where
    I: Iterator<
        Item = (
            Variants<'de>,
            &'t Symbol,
            &'t ArcType,
        ),
    >,
{
    type Error = VmError;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>>
    where
        K: DeserializeSeed<'de>,
    {
        match self.iter.next() {
            Some((value, field, typ)) => {
                self.value = Some((value, typ));
                seed.deserialize(field.as_ref().into_deserializer()).map(
                    Some,
                )
            }
            None => Ok(None),
        }
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value>
    where
        V: DeserializeSeed<'de>,
    {
        match self.value.take() {
            Some((value, typ)) => {
                seed.deserialize(&mut Deserializer {
                    state: self.state.clone(),
                    input: value,
                    typ: typ,
                })
            }
            None => Err(Self::Error::custom("Cant deserialize type")),
        }
    }
}

struct Enum<'a, 'de: 'a, 't: 'a> {
    de: &'a mut Deserializer<'de, 't>,
}

impl<'a, 'de, 't> Enum<'a, 'de, 't> {
    fn new(de: &'a mut Deserializer<'de, 't>) -> Self {
        Enum { de: de }
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
            ValueRef::Tag(tag) => visitor.visit_u32(tag),
            _ => Err(Self::Error::custom("Cant deserialize tag")),
        }
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let tag = match self.de.input.as_ref() {
            ValueRef::Data(data) => data.tag(),
            ValueRef::Tag(tag) => tag,
            _ => return Err(Self::Error::custom("Cant deserialize tag")),
        };
        let typ = resolve::remove_aliases_cow(self.de.state.env, self.de.typ);
        match **typ {
            Type::Variant(ref variants) => {
                let variant = variants.row_iter().nth(tag as usize).ok_or_else(|| {
                    Self::Error::custom("Cant deserialize tag")
                })?;
                visitor.visit_str(variant.name.as_ref())
            }
            _ => return Err(Self::Error::custom("Cant deserialize tag")),
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

// `EnumAccess` is provided to the `Visitor` to give it the ability to determine
// which variant of the enum is supposed to be deserialized.
//
// Note that all enum deserialization methods in Serde refer exclusively to the
// "externally tagged" enum representation.
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

// `VariantAccess` is provided to the `Visitor` to give it the ability to see
// the content of the single variant that it decided to deserialize.
impl<'de, 'a, 't> VariantAccess<'de> for Enum<'a, 'de, 't> {
    type Error = VmError;

    fn unit_variant(self) -> Result<()> {
        Ok(())
    }

    fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value>
    where
        T: DeserializeSeed<'de>,
    {
        seed.deserialize(self.de)
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
        de::Deserializer::deserialize_map(self.de, visitor)
    }
}
