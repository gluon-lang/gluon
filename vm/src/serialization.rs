use std::borrow::Cow;
use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;

use itertools::Itertools;

use serde::Deserializer;
use serde::de::{Deserialize, DeserializeSeed, SeqSeed, Error};
use serde::ser::{Serializer, SerializeSeed, SerializeSeq, Seeded};

use base::fnv::FnvMap;
use base::serialization::{NodeMap, NodeToId};
use base::symbol::{Symbol, Symbols};
use gc::{DataDef, GcPtr, Traverseable, WriteOnly};
use thread::{RootedThread, Status, Thread, ThreadInternal};
use types::VmIndex;
use value::{BytecodeFunction, Callable, ClosureData, ClosureDataDef, ExternFunction,
            PartialApplicationData, PartialApplicationDataDef, Value};

#[derive(Clone)]
pub struct DeSeed {
    thread: RootedThread,
    symbols: Rc<RefCell<Symbols>>,
    gc_map: NodeMap,
}

impl DeSeed {
    pub fn new(thread: RootedThread) -> DeSeed {
        DeSeed {
            thread: thread,
            symbols: Default::default(),
            gc_map: NodeMap::default(),
        }
    }

    pub fn deserialize<'de, D, T>(self, deserializer: D) -> Result<T, D::Error>
        where D: Deserializer<'de>,
              T: GcSerialize<'de>
    {
        <T::Seed>::from(self).deserialize(deserializer)
    }
}

#[derive(Default)]
pub struct SeSeed {
    interner: Symbols,
    node_to_id: NodeToId,
}

impl AsRef<NodeToId> for SeSeed {
    fn as_ref(&self) -> &NodeToId {
        &self.node_to_id
    }
}

impl SeSeed {
    pub fn new() -> SeSeed {
        SeSeed::default()
    }
}

pub struct Seed<T> {
    pub state: DeSeed,
    _marker: PhantomData<T>,
}

impl<T> Clone for Seed<T> {
    fn clone(&self) -> Seed<T> {
        Seed {
            state: self.state.clone(),
            _marker: PhantomData,
        }
    }
}

impl<T> AsMut<NodeMap> for Seed<T> {
    fn as_mut(&mut self) -> &mut NodeMap {
        &mut self.state.gc_map
    }
}

impl<T> From<DeSeed> for Seed<T> {
    fn from(value: DeSeed) -> Self {
        Seed {
            state: value,
            _marker: PhantomData,
        }
    }
}

pub trait GcSerialize<'de>: Sized {
    type Seed: DeserializeSeed<'de, Value = Self> + From<DeSeed>;
}

#[macro_export]
macro_rules! gc_serialize {
    ($value: ty) => {

        impl<'de> $crate::serialization::GcSerialize<'de> for $value {
            type Seed = $crate::serialization::Seed<$value>;
        }
    }
}

pub mod gc {
    use super::*;
    use serde::{Deserialize, Deserializer};
    use serde::de::{DeserializeSeed, Error, SeqSeed};
    use serde::ser::{SerializeSeed, Serialize, Serializer};
    use value::{ArrayDef, DataStruct, GcStr, Value, ValueArray};
    use thread::ThreadInternal;
    use types::VmTag;

    impl<'de, T> GcSerialize<'de> for GcPtr<T>
        where T: GcSerialize<'de> + ::gc::Traverseable + 'static
    {
        type Seed = Seed<GcPtr<T>>;
    }

    impl<'de, T> GcSerialize<'de> for ::gc::Move<T>
        where T: GcSerialize<'de> + ::gc::Traverseable
    {
        type Seed = Seed<::gc::Move<T>>;
    }

    impl<'de, T> DeserializeSeed<'de> for Seed<::gc::Move<T>>
        where T: GcSerialize<'de> + ::gc::Traverseable,
              T::Seed: DeserializeSeed<'de>
    {
        type Value = ::gc::Move<T>;

        fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where D: Deserializer<'de>
        {
            T::Seed::from(self.state)
                .deserialize(deserializer)
                .map(::gc::Move)
        }
    }

    impl<'de, T> DeserializeSeed<'de> for Seed<GcPtr<T>>
        where T: GcSerialize<'de> + ::gc::Traverseable + 'static,
              T::Seed: DeserializeSeed<'de>
    {
        type Value = GcPtr<T>;

        fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where D: Deserializer<'de>
        {
            use gc::Move;
            DeserializeSeed::deserialize(Seed::<DataDefSeed<Move<T>>>::from(self.state.clone()),
                                         deserializer)
        }
    }

    impl SerializeSeed for ValueArray {
        type Seed = SeSeed;

        fn serialize_seed<S>(&self, serializer: S, seed: &Self::Seed) -> Result<S::Ok, S::Error>
            where S: Serializer
        {
            use serde::ser::Seeded;

            serializer.collect_seq(self.iter().map(|value| Seeded::new(seed, value)))
        }
    }

    pub fn deserialize_array<'de, D, T>(seed: &mut Seed<T>,
                                        deserializer: D)
                                        -> Result<GcPtr<ValueArray>, D::Error>
        where D: Deserializer<'de>
    {
        DeserializeSeed::deserialize(Seed::<DataDefSeed<Vec<Value>>>::from(seed.state.clone()),
                                     deserializer)
    }

    gc_serialize!{ Data }

    #[derive(DeserializeSeed)]
    #[serde(deserialize_seed = "::serialization::Seed<Data>")]
    pub struct Data {
        tag: VmTag,
        #[serde(deserialize_seed_with = "::serialization::deserialize")]
        fields: Vec<Value>,
    }

    unsafe impl DataDef for Data {
        type Value = DataStruct;

        fn size(&self) -> usize {
            use value::Def;
            Def {
                    tag: self.tag,
                    elems: &self.fields,
                }
                .size()
        }

        fn initialize<'w>(self, result: WriteOnly<'w, Self::Value>) -> &'w mut Self::Value {
            use value::Def;
            Def {
                    tag: self.tag,
                    elems: &self.fields,
                }
                .initialize(result)
        }
    }

    pub fn deserialize_data<'de, D, T>(seed: &mut Seed<T>,
                                       deserializer: D)
                                       -> Result<GcPtr<DataStruct>, D::Error>
        where D: Deserializer<'de>
    {
        DeserializeSeed::deserialize(Seed::<DataDefSeed<Data>>::from(seed.state.clone()),
                                     deserializer)
    }

    impl<'de> GcSerialize<'de> for GcStr {
        type Seed = Seed<GcStr>;
    }

    impl<'de> DeserializeSeed<'de> for Seed<GcStr> {
        type Value = GcStr;

        fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where D: Deserializer<'de>
        {
            Cow::<str>::deserialize(deserializer)
                .map(|s| unsafe {
                         GcStr::from_utf8_unchecked(self.state
                                                        .thread
                                                        .context()
                                                        .alloc(s.as_bytes())
                                                        .unwrap())
                     })
        }
    }

    impl<T> ::base::serialization::Shared for GcPtr<T> {
        fn unique(&self) -> bool {
            false
        }
        fn as_ptr(&self) -> *const () {
            let t: *const T = &**self;
            t as *const ()
        }
    }

    impl<T> SerializeSeed for GcPtr<T>
        where T: SerializeSeed,
              T::Seed: AsRef<NodeToId>
    {
        type Seed = T::Seed;

        #[inline]
        fn serialize_seed<S>(&self, serializer: S, seed: &Self::Seed) -> Result<S::Ok, S::Error>
            where S: Serializer
        {
            ::base::serialization::serialize_shared(self, serializer, seed)
        }
    }
}

pub mod symbol {
    use super::*;
    use base::symbol::Symbol;
    use serde::{Deserialize, Deserializer};
    use serde::ser::{Serialize, Serializer};

    impl<'de> GcSerialize<'de> for Symbol {
        type Seed = Seed<Symbol>;
    }

    impl<'de> DeserializeSeed<'de> for Seed<Symbol> {
        type Value = Symbol;

        fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where D: Deserializer<'de>
        {
            String::deserialize(deserializer).map(|s| self.state.symbols.borrow_mut().symbol(s))
        }
    }

    pub fn serialize<S>(symbol: &Symbol, serializer: S, _seed: &SeSeed) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        let s: &str = symbol.as_ref();
        s.serialize(serializer)
    }
}

pub mod intern {
    use super::*;
    use interner::InternedStr;
    use thread::ThreadInternal;

    use serde::{Deserialize, Deserializer};
    use serde::de::{DeserializeSeed, SeqSeed};
    use serde::ser::{SerializeSeed, Serialize, Serializer};

    impl<'de> GcSerialize<'de> for InternedStr {
        type Seed = Seed<InternedStr>;
    }

    impl<'de> DeserializeSeed<'de> for Seed<InternedStr> {
        type Value = InternedStr;

        fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where D: Deserializer<'de>
        {
            String::deserialize(deserializer).map(|s| {
                                                      self.state
                                                          .thread
                                                          .global_env()
                                                          .intern(&s)
                                                          .unwrap()
                                                  })
        }
    }

    impl SerializeSeed for InternedStr {
        type Seed = SeSeed;

        #[inline]
        fn serialize_seed<S>(&self, serializer: S, _seed: &Self::Seed) -> Result<S::Ok, S::Error>
            where S: Serializer
        {
            let s: &str = self;
            s.serialize(serializer)
        }
    }
}

pub mod typ {
    use serde::de::{Deserialize, Deserializer, DeserializeSeed, Error};
    use serde::ser::{Seeded, Serialize, Serializer, SerializeSeed};

    use super::*;
    use base::types::{ArcType, Type};

    pub fn deserialize<'de, D, T>(seed: &mut Seed<T>, deserializer: D) -> Result<ArcType, D::Error>
        where D: Deserializer<'de>
    {
        use base::types::{TypeSeed, Seed, SharedType};
        TypeSeed::<Symbol, ArcType, ()>::new(Seed::new(seed.state.gc_map.clone()))
            .deserialize(deserializer)
    }

    pub fn serialize<S>(typ: &ArcType, serializer: S, seed: &SeSeed) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        typ.serialize_seed(serializer,
                           &::base::serialization::SeSeed::new(seed.node_to_id.clone()))
    }
}

struct ClosureDataModel {
    function: GcPtr<BytecodeFunction>,
    upvars: usize,
}

unsafe impl DataDef for ClosureDataModel {
    type Value = ClosureData;

    fn size(&self) -> usize {
        use std::mem::size_of;
        use array::Array;
        size_of::<GcPtr<BytecodeFunction>>() + Array::<Value>::size_of(self.upvars)
    }

    fn initialize<'w>(self, mut result: WriteOnly<'w, Self::Value>) -> &'w mut Self::Value {
        unsafe {
            let result = &mut *result.as_mut_ptr();
            result.function = self.function;
            result
                .upvars
                .initialize(::std::iter::repeat(Value::Int(0)).take(self.upvars));
            result
        }
    }
}

#[derive(Deserialize, Serialize)]
enum GraphVariant {
    Marked(::base::serialization::Id),
    Reference(::base::serialization::Id),
}

impl SerializeSeed for ClosureData {
    type Seed = SeSeed;

    #[inline]
    fn serialize_seed<S>(&self, serializer: S, seed: &Self::Seed) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        let mut serializer = serializer.serialize_seq(Some(3 + self.upvars.len()))?;
        let self_id = self as *const _ as *const ();
        if let Some(&id) = seed.node_to_id.borrow().get(&self_id) {
            serializer
                .serialize_element(&GraphVariant::Reference(id))?;
            return serializer.end();
        }
        {
            let mut node_to_id = seed.node_to_id.borrow_mut();
            let len = node_to_id.len() as ::base::serialization::Id;
            serializer.serialize_element(&GraphVariant::Marked(len))?;
            node_to_id.insert(self_id, len);
        }
        serializer
            .serialize_element(&Seeded::new(seed, self.function))?;
        serializer.serialize_element(&self.upvars.len())?;
        for item in self.upvars.iter() {
            serializer.serialize_element(&Seeded::new(seed, item))?;
        }
        serializer.end()
    }
}

pub fn deserialize_closure<'de, T, D>(seed: &mut Seed<T>,
                                      deserializer: D)
                                      -> Result<GcPtr<ClosureData>, D::Error>
    where D: Deserializer<'de>
{
    use std::fmt;

    use serde::de::{SeqAccess, Visitor};

    impl<'de> DeserializeSeed<'de> for Seed<ClosureData> {
        type Value = GcPtr<ClosureData>;

        fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where D: Deserializer<'de>
        {
            impl<'de> Visitor<'de> for Seed<ClosureData> {
                type Value = GcPtr<ClosureData>;

                fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                    formatter.write_str("struct ClosureData")
                }

                fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
                    where V: SeqAccess<'de>
                {
                    use base::serialization::{VariantSeed, Variant};

                    let variant = seq.next_element()?
                        .ok_or_else(|| V::Error::invalid_length(0, &self))?;
                    unsafe {
                        match variant {
                            GraphVariant::Marked(id) => {
                                let function =
                                    seq.next_element_seed(Seed::<GcPtr<BytecodeFunction>>::from(self.state.clone()))?
                                        .ok_or_else(|| V::Error::invalid_length(1, &self))?;
                                let upvars =
                                    seq.next_element()?
                                        .ok_or_else(|| V::Error::invalid_length(2, &self))?;

                                let mut closure: GcPtr<ClosureData> =
                                    self.state
                                        .thread
                                        .context()
                                        .gc
                                        .alloc(ClosureDataModel {
                                                   function: function,
                                                   upvars: upvars,
                                               })
                                        .map_err(V::Error::custom)?;
                                self.state.gc_map.insert(id, closure);

                                for i in 0..upvars {
                                    let value = seq.next_element_seed(Seed::<Value>::from(self.state.clone()))?
                                        .ok_or_else(|| V::Error::invalid_length(i + 2, &self))?;
                                    closure.as_mut().upvars[i] = value;
                                }
                                Ok(closure)
                            }
                            GraphVariant::Reference(id) => {
                                match self.state.gc_map.get::<GcPtr<ClosureData>>(&id) {
                                    Some(rc) => Ok(rc),
                                    None => {
                                        Err(V::Error::custom(format_args!("missing id {}", id)))
                                    }
                                }
                            }
                        }
                    }
                }
            }

            deserializer.deserialize_seq(self)
        }
    }
    use base::serialization::SharedSeed;

    DeserializeSeed::deserialize(Seed::<ClosureData>::from(seed.state.clone()), deserializer)
}

#[derive(DeserializeSeed)]
#[serde(deserialize_seed = "Seed<PartialApplicationModel>")]
struct PartialApplicationModel {
    #[serde(deserialize_seed_with = "deserialize")]
    function: Callable,
    #[serde(deserialize_seed_with = "deserialize")]
    upvars: Vec<Value>,
}

gc_serialize!{ PartialApplicationModel }

unsafe impl DataDef for PartialApplicationModel {
    type Value = PartialApplicationData;

    fn size(&self) -> usize {
        PartialApplicationDataDef(self.function, &self.upvars).size()
    }

    fn initialize<'w>(self, result: WriteOnly<'w, Self::Value>) -> &'w mut Self::Value {
        PartialApplicationDataDef(self.function, &self.upvars).initialize(result)
    }
}

pub fn deserialize_application<'de, T, D>(seed: &mut Seed<T>,
                                          deserializer: D)
                                          -> Result<GcPtr<PartialApplicationData>, D::Error>
    where D: Deserializer<'de>
{
    DeserializeSeed::deserialize(Seed::<DataDefSeed<PartialApplicationModel>>::from(seed.state.clone()),
                                 deserializer)
}


struct DataDefSeed<T>(PhantomData<T>);

impl<'de, T> DeserializeSeed<'de> for ::serialization::Seed<DataDefSeed<T>>
    where T: DataDef + GcSerialize<'de> + 'static,
          <T as DataDef>::Value: Sized,
          T::Seed: DeserializeSeed<'de>
{
    type Value = GcPtr<<T as DataDef>::Value>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
        where D: Deserializer<'de>
    {
        use base::serialization::SharedSeed;

        struct GcSeed<T> {
            _marker: PhantomData<T>,
            state: DeSeed,
        }
        impl<T> Clone for GcSeed<T> {
            fn clone(&self) -> Self {
                GcSeed {
                    _marker: PhantomData,
                    state: self.state.clone(),
                }
            }
        }
        impl<T> AsMut<NodeMap> for GcSeed<T> {
            fn as_mut(&mut self) -> &mut NodeMap {
                &mut self.state.gc_map
            }
        }

        impl<'de, T> DeserializeSeed<'de> for GcSeed<T>
            where T: DataDef + GcSerialize<'de> + 'static,
                  <T as DataDef>::Value: Sized,
                  T::Seed: DeserializeSeed<'de>
        {
            type Value = GcPtr<<T as DataDef>::Value>;

            fn deserialize<D>(mut self, deserializer: D) -> Result<Self::Value, D::Error>
                where D: Deserializer<'de>
            {
                let def = DeserializeSeed::deserialize(T::Seed::from(self.state.clone()),
                                                       deserializer)?;
                self.state
                    .thread
                    .context()
                    .gc
                    .alloc(def)
                    .map_err(D::Error::custom)
            }
        }

        let seed = GcSeed {
            _marker: PhantomData::<T>,
            state: self.state,
        };

        SharedSeed(seed).deserialize(deserializer)
    }
}

gc_serialize!{ ExternFunction }

impl<'de> DeserializeSeed<'de> for Seed<ExternFunction> {
    type Value = ExternFunction;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
        where D: Deserializer<'de>
    {
        use api::{Hole, OpaqueValue};
        #[derive(Deserialize)]
        struct ExternFunction_<'s> {
            id: Cow<'s, str>,
            args: VmIndex,
        }

        let partial = ExternFunction_::deserialize(deserializer)?;
        // Wrap any operators with parens so that they are acceptable for `get_global`
        let escaped_id: String = partial
            .id
            .split(|c: char| c == '.')
            .map(|s| if s.chars()
                        .next()
                        .map_or(false, ::base::ast::is_operator_char) {
                     Cow::Owned(format!("({})", s))
                 } else {
                     Cow::Borrowed(s)
                 })
            .intersperse(Cow::Borrowed("."))
            .collect();
        let function = self.state
            .thread
            .get_global::<OpaqueValue<&Thread, Hole>>(&partial.id)
            .map_err(|err| panic!("{}\n{}", partial.id, escaped_id))?;
        unsafe {
            match function.get_value() {
                Value::Function(function) if partial.args == function.args => {
                    Ok(ExternFunction {
                           id: function.id.clone(),
                           args: function.args,
                           function: function.function,
                       })
                }
                _ => Err(D::Error::custom("Invalid type for extern function")),
            }
        }
    }
}

impl<'de, T> GcSerialize<'de> for Vec<T>
    where T: GcSerialize<'de>,
          T::Seed: Clone
{
    type Seed = Seed<Vec<T>>;
}

impl<'de, T> DeserializeSeed<'de> for Seed<Vec<T>>
    where T: GcSerialize<'de>,
          T::Seed: Clone
{
    type Value = Vec<T>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
        where D: Deserializer<'de>
    {
        SeqSeed::new(T::Seed::from(self.state.clone()), Vec::with_capacity)
            .deserialize(deserializer)
    }
}

pub fn deserialize<'de, D, T, U>(seed: &mut Seed<T>, deserializer: D) -> Result<U, D::Error>
    where D: Deserializer<'de>,
          U: GcSerialize<'de>
{
    U::Seed::from(seed.state.clone()).deserialize(deserializer)
}

#[cfg(test)]
mod tests {
    extern crate serde_json;

    use super::*;
    use value::Value;
    use thread::RootedThread;

    #[test]
    fn str_value() {
        let thread = RootedThread::new();
        let mut de = serde_json::Deserializer::from_str(r#" { "String": "test" } "#);
        let value: Value = DeSeed::new(thread).deserialize(&mut de).unwrap();
        match value {
            Value::String(s) => assert_eq!(&*s, "test"),
            _ => panic!(),
        }
    }

    #[test]
    fn int_array() {
        let thread = RootedThread::new();
        let mut de = serde_json::Deserializer::from_str(r#" {
            "Array": [
                { "Int": 1 },
                { "Int": 2 },
                { "Int": 3 }
            ]
        } "#);
        let value: Value = DeSeed::new(thread).deserialize(&mut de).unwrap();
        match value {
            Value::Array(s) => {
                assert_eq!(s.iter().collect::<Vec<_>>(),
                           [Value::Int(1), Value::Int(2), Value::Int(3)])
            }
            _ => panic!(),
        }
    }
}
