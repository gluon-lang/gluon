use std::borrow::Cow;
use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;
use std::sync::Arc;

use itertools::Itertools;

use serde::Deserializer;
use serde::de::{Deserialize, DeserializeSeed, DeserializeState, Error};
use serde::ser::{Seeded, SerializeSeq, SerializeState, Serializer};

use base::serialization::{NodeMap, NodeToId};
use base::symbol::{Symbol, Symbols};
use base::types::ArcType;

use Variants;
use array::Array;
use gc::{DataDef, GcPtr, WriteOnly};
use thread::{RootedThread, Thread, ThreadInternal};
use types::VmIndex;
use value::{BytecodeFunction, Callable, ClosureData, ExternFunction, PartialApplicationData,
            PartialApplicationDataDef, Value, ValueRepr};

#[derive(Clone)]
pub struct DeSeed {
    pub thread: RootedThread,
    symbols: Rc<RefCell<Symbols>>,
    gc_map: NodeMap,
    base_seed: ::base::serialization::Seed<Symbol, ArcType<Symbol>>,
}

impl DeSeed {
    pub fn new(thread: &Thread) -> DeSeed {
        DeSeed {
            thread: thread.root_thread(),
            symbols: Default::default(),
            gc_map: NodeMap::default(),
            base_seed: Default::default(),
        }
    }

    pub fn deserialize<'de, D, T>(mut self, deserializer: D) -> Result<T, D::Error>
    where
        D: Deserializer<'de>,
        T: DeserializeState<'de, Self>,
    {
        T::deserialize_state(&mut self, deserializer)
    }
}

impl AsMut<NodeMap> for DeSeed {
    fn as_mut(&mut self) -> &mut NodeMap {
        &mut self.gc_map
    }
}

pub struct SeSeed {
    node_to_id: ::base::serialization::SeSeed,
}

impl AsRef<NodeToId> for SeSeed {
    fn as_ref(&self) -> &NodeToId {
        &self.node_to_id.node_to_id
    }
}

impl SeSeed {
    pub fn new() -> SeSeed {
        SeSeed {
            node_to_id: Default::default(),
        }
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

pub mod gc {
    use super::*;
    use serde::de::{Deserialize, DeserializeState, Deserializer};
    use serde::ser::{Serialize, SerializeState, Serializer};

    use interner::InternedStr;
    use value::{DataStruct, GcStr, ValueArray};
    use thread::ThreadInternal;
    use types::VmTag;

    impl Serialize for GcStr {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            (**self).serialize(serializer)
        }
    }

    impl<'de, T> DeserializeState<'de, DeSeed> for ::gc::Move<T>
    where
        T: ::gc::Traverseable,
        T: DeserializeState<'de, DeSeed>,
    {
        fn deserialize_state<D>(seed: &mut DeSeed, deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            T::deserialize_state(seed, deserializer).map(::gc::Move)
        }
    }

    impl<'de, T> DeserializeState<'de, DeSeed> for GcPtr<T>
    where
        T: ::gc::Traverseable + 'static,
        T: DeserializeState<'de, DeSeed>,
    {
        fn deserialize_state<D>(seed: &mut DeSeed, deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            use gc::Move;
            DeserializeSeed::deserialize(
                Seed::<DataDefSeed<Move<T>>>::from(seed.clone()),
                deserializer,
            )
        }
    }

    impl SerializeState<SeSeed> for ValueArray {
        fn serialize_state<S>(&self, serializer: S, seed: &SeSeed) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            use serde::ser::Seeded;

            serializer.collect_seq(self.iter().map(|value| Seeded::new(seed, value)))
        }
    }

    pub fn deserialize_array<'de, D>(
        seed: &mut DeSeed,
        deserializer: D,
    ) -> Result<GcPtr<ValueArray>, D::Error>
    where
        D: Deserializer<'de>,
    {
        DeserializeSeed::deserialize(
            Seed::<DataDefSeed<Vec<Value>>>::from(seed.clone()),
            deserializer,
        )
    }

    #[derive(DeserializeState, SerializeState)]
    #[serde(deserialize_state = "::serialization::DeSeed")]
    #[serde(serialize_state = "::serialization::SeSeed")]
    #[serde(bound(deserialize = "F: DeserializeState<'de, ::serialization::DeSeed>,
                                 S: ::std::ops::Deref + ::std::any::Any + Clone
                                    + ::base::serialization::Shared
                                    + DeserializeState<'de, ::serialization::DeSeed>",
                  serialize = "F: SerializeState<::serialization::SeSeed>,
                               S: ::std::ops::Deref + ::std::any::Any + Clone
                                    + ::base::serialization::Shared,
                               S::Target: SerializeState<::serialization::SeSeed>"))]
    struct Data<F, S> {
        #[serde(state)]
        tag: DataTag<S>,
        #[serde(state)]
        fields: F,
    }

    #[derive(DeserializeState, SerializeState)]
    #[serde(deserialize_state = "::serialization::DeSeed")]
    #[serde(serialize_state = "::serialization::SeSeed")]
    #[serde(bound(deserialize = "S: ::std::ops::Deref + ::std::any::Any + Clone
                                    + ::base::serialization::Shared
                                    + DeserializeState<'de, ::serialization::DeSeed>",
                  serialize = "S: ::std::ops::Deref + ::std::any::Any + Clone
                                    + ::base::serialization::Shared,
                               S::Target: SerializeState<::serialization::SeSeed>"))]
    enum DataTag<S> {
        Record(#[serde(state_with = "::base::serialization::shared")] S),
        Data(VmTag),
    }

    impl SerializeState<SeSeed> for DataStruct {
        fn serialize_state<S>(&self, serializer: S, seed: &SeSeed) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let tag = if self.is_record() {
                let fields = unsafe { GcPtr::from_raw(self).field_names().clone() };
                DataTag::Record(fields)
            } else {
                DataTag::Data(self.tag())
            };
            Data {
                tag: tag,
                fields: &self.fields[..],
            }.serialize_state(serializer, seed)
        }
    }

    pub fn deserialize_data<'de, D>(
        seed: &mut DeSeed,
        deserializer: D,
    ) -> Result<GcPtr<DataStruct>, D::Error>
    where
        D: Deserializer<'de>,
    {
        use base::serialization::SharedSeed;

        struct GcSeed<'a> {
            state: &'a mut DeSeed,
        }
        impl<'a> AsMut<NodeMap> for GcSeed<'a> {
            fn as_mut(&mut self) -> &mut NodeMap {
                &mut self.state.gc_map
            }
        }

        impl<'de, 'a> DeserializeState<'de, GcSeed<'a>> for GcPtr<DataStruct> {
            fn deserialize_state<D>(
                seed: &mut GcSeed<'a>,
                deserializer: D,
            ) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                let seed = &mut seed.state;
                let def = Data::<Vec<Value>, Arc<Vec<InternedStr>>>::deserialize_state(
                    seed,
                    deserializer,
                )?;
                use value::{Def, RecordDef};
                match def.tag {
                    DataTag::Record(fields) => seed.thread
                        .context()
                        .gc
                        .alloc(RecordDef {
                            elems: &def.fields,
                            fields: &fields[..],
                        })
                        .map_err(D::Error::custom),
                    DataTag::Data(tag) => seed.thread
                        .context()
                        .gc
                        .alloc(Def {
                            tag: tag,
                            elems: &def.fields,
                        })
                        .map_err(D::Error::custom),
                }
            }
        }

        let mut seed = GcSeed { state: seed };

        DeserializeSeed::deserialize(SharedSeed::new(&mut seed), deserializer)
    }

    impl<'de> DeserializeState<'de, DeSeed> for GcStr {
        fn deserialize_state<D>(seed: &mut DeSeed, deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            Cow::<str>::deserialize(deserializer).map(|s| unsafe {
                GcStr::from_utf8_unchecked(seed.thread.context().alloc(s.as_bytes()).unwrap())
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

    impl<T, Seed> SerializeState<Seed> for GcPtr<T>
    where
        T: SerializeState<Seed>,
        Seed: AsRef<NodeToId>,
    {
        #[inline]
        fn serialize_state<S>(&self, serializer: S, seed: &Seed) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            ::base::serialization::shared::serialize(self, serializer, seed)
        }
    }
}

pub mod symbol {
    use super::*;
    use base::symbol::Symbol;
    use serde::{Deserialize, Deserializer};
    use serde::ser::{Serialize, Serializer};

    pub fn deserialize<'de, D>(seed: &mut DeSeed, deserializer: D) -> Result<Symbol, D::Error>
    where
        D: Deserializer<'de>,
    {
        String::deserialize(deserializer).map(|s| seed.symbols.borrow_mut().symbol(s))
    }

    pub fn serialize<S>(symbol: &Symbol, serializer: S, _state: &SeSeed) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
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
    use serde::ser::{Serialize, SerializeState, Serializer};

    impl<'de> DeserializeState<'de, DeSeed> for InternedStr {
        fn deserialize_state<D>(seed: &mut DeSeed, deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            String::deserialize(deserializer).map(|s| seed.thread.global_env().intern(&s).unwrap())
        }
    }

    impl SerializeState<SeSeed> for InternedStr {
        #[inline]
        fn serialize_state<S>(&self, serializer: S, _state: &SeSeed) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let s: &str = self;
            s.serialize(serializer)
        }
    }
}

pub mod borrow {
    use super::*;
    use std::borrow::{Borrow, BorrowMut};

    pub fn deserialize<'de, D, T, Seed, Seed2>(
        seed: &mut Seed,
        deserializer: D,
    ) -> Result<T, D::Error>
    where
        D: Deserializer<'de>,
        T: DeserializeState<'de, Seed2>,
        Seed: BorrowMut<Seed2>,
    {
        T::deserialize_state(seed.borrow_mut(), deserializer)
    }

    pub fn serialize<S, T, Seed, Seed2>(
        symbol: &T,
        serializer: S,
        seed: &Seed,
    ) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: SerializeState<Seed2>,
        Seed: Borrow<Seed2>,
    {
        symbol.serialize_state(serializer, seed.borrow())
    }
}

pub mod typ {
    use super::*;
    use base::types::ArcType;
    use base::symbol::Symbol;

    impl ::std::borrow::Borrow<::base::serialization::Seed<Symbol, ArcType<Symbol>>> for DeSeed {
        fn borrow(&self) -> &::base::serialization::Seed<Symbol, ArcType<Symbol>> {
            &self.base_seed
        }
    }
    impl ::std::borrow::BorrowMut<::base::serialization::Seed<Symbol, ArcType<Symbol>>> for DeSeed {
        fn borrow_mut(&mut self) -> &mut ::base::serialization::Seed<Symbol, ArcType<Symbol>> {
            &mut self.base_seed
        }
    }

    impl ::std::borrow::Borrow<::base::serialization::SeSeed> for SeSeed {
        fn borrow(&self) -> &::base::serialization::SeSeed {
            &self.node_to_id
        }
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
        size_of::<ClosureData>() + size_of::<Value>() * self.upvars
    }

    fn initialize<'w>(self, mut result: WriteOnly<'w, Self::Value>) -> &'w mut Self::Value {
        unsafe {
            let result = &mut *result.as_mut_ptr();
            result.function = self.function;
            result.upvars.initialize(
                ::std::iter::repeat(())
                    .map(|_| ValueRepr::Int(0).into())
                    .take(self.upvars),
            );
            result
        }
    }
}

#[derive(Deserialize, Serialize)]
enum GraphVariant {
    Marked(::base::serialization::Id),
    Reference(::base::serialization::Id),
}

impl SerializeState<SeSeed> for ClosureData {
    #[inline]
    fn serialize_state<S>(&self, serializer: S, seed: &SeSeed) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut serializer = serializer.serialize_seq(Some(3 + self.upvars.len()))?;
        let self_id = self as *const _ as *const ();
        if let Some(&id) = seed.node_to_id.node_to_id.borrow().get(&self_id) {
            serializer.serialize_element(&GraphVariant::Reference(id))?;
            return serializer.end();
        }
        {
            let mut node_to_id = seed.node_to_id.node_to_id.borrow_mut();
            let len = node_to_id.len() as ::base::serialization::Id;
            serializer.serialize_element(&GraphVariant::Marked(len))?;
            node_to_id.insert(self_id, len);
        }
        serializer.serialize_element(&Seeded::new(seed, self.function))?;
        serializer.serialize_element(&self.upvars.len())?;
        for item in self.upvars.iter() {
            serializer.serialize_element(&Seeded::new(seed, item))?;
        }
        serializer.end()
    }
}

pub mod closure {
    use super::*;

    pub fn deserialize<'de, D>(
        seed: &mut DeSeed,
        deserializer: D,
    ) -> Result<GcPtr<ClosureData>, D::Error>
    where
        D: Deserializer<'de>,
    {
        use std::fmt;

        use serde::de::{SeqAccess, Visitor};

        impl<'de> DeserializeSeed<'de> for Seed<ClosureData> {
            type Value = GcPtr<ClosureData>;

            fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where
                D: Deserializer<'de>,
            {
                impl<'de> Visitor<'de> for Seed<ClosureData> {
                    type Value = GcPtr<ClosureData>;

                    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        formatter.write_str("struct ClosureData")
                    }

                    fn visit_seq<V>(mut self, mut seq: V) -> Result<Self::Value, V::Error>
                    where
                        V: SeqAccess<'de>,
                    {
                        let variant = seq.next_element()?
                            .ok_or_else(|| V::Error::invalid_length(0, &self))?;
                        unsafe {
                            match variant {
                                GraphVariant::Marked(id) => {
                                    let function = seq.next_element_seed(::serde::de::Seed::new(
                                        &mut self.state,
                                    ))?
                                        .ok_or_else(|| V::Error::invalid_length(1, &self))?;
                                    let upvars = seq.next_element()?
                                        .ok_or_else(|| V::Error::invalid_length(2, &self))?;

                                    let mut closure: GcPtr<
                                        ClosureData,
                                    > = self.state
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
                                        let value = seq.next_element_seed(::serde::de::Seed::new(
                                            &mut self.state,
                                        ))?
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

        DeserializeSeed::deserialize(Seed::<ClosureData>::from(seed.clone()), deserializer)
    }

    pub fn serialize<S>(
        self_: &ClosureData,
        serializer: S,
        seed: &SeSeed,
    ) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self_.serialize_state(serializer, seed)
    }
}

#[derive(DeserializeState)]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "DeSeed"))]
struct PartialApplicationModel {
    #[cfg_attr(feature = "serde_derive", serde(deserialize_state))]
    function: Callable,
    #[cfg_attr(feature = "serde_derive", serde(deserialize_state))]
    args: Vec<Value>,
}

unsafe impl DataDef for PartialApplicationModel {
    type Value = PartialApplicationData;

    fn size(&self) -> usize {
        PartialApplicationDataDef(self.function, &self.args).size()
    }

    fn initialize<'w>(self, result: WriteOnly<'w, Self::Value>) -> &'w mut Self::Value {
        PartialApplicationDataDef(self.function, &self.args).initialize(result)
    }
}

pub fn deserialize_application<'de, D>(
    seed: &mut DeSeed,
    deserializer: D,
) -> Result<GcPtr<PartialApplicationData>, D::Error>
where
    D: Deserializer<'de>,
{
    DeserializeSeed::deserialize(
        Seed::<DataDefSeed<PartialApplicationModel>>::from(seed.clone()),
        deserializer,
    )
}

struct DataDefSeed<T>(PhantomData<T>);

impl<'de, T> DeserializeSeed<'de> for ::serialization::Seed<DataDefSeed<T>>
where
    T: DataDef + 'static,
    <T as DataDef>::Value: Sized,
    T: DeserializeState<'de, DeSeed>,
{
    type Value = GcPtr<<T as DataDef>::Value>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        use base::serialization::SharedSeed;

        struct GcSeed<T> {
            _marker: PhantomData<T>,
            state: DeSeed,
        }
        impl<T> AsMut<NodeMap> for GcSeed<T> {
            fn as_mut(&mut self) -> &mut NodeMap {
                &mut self.state.gc_map
            }
        }

        impl<'de, T> DeserializeState<'de, GcSeed<T>> for GcPtr<T::Value>
        where
            T: DataDef + 'static,
            <T as DataDef>::Value: Sized,
            T: DeserializeState<'de, DeSeed>,
        {
            fn deserialize_state<D>(seed: &mut GcSeed<T>, deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                let def = T::deserialize_state(&mut seed.state, deserializer)?;
                seed.state
                    .thread
                    .context()
                    .gc
                    .alloc(def)
                    .map_err(D::Error::custom)
            }
        }

        let mut seed = GcSeed {
            _marker: PhantomData::<T>,
            state: self.state,
        };

        DeserializeSeed::deserialize(SharedSeed::new(&mut seed), deserializer)
    }
}

impl<'de> DeserializeState<'de, DeSeed> for ExternFunction {
    fn deserialize_state<D>(seed: &mut DeSeed, deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        use api::{Hole, OpaqueValue};
        #[derive(Deserialize)]
        struct ExternFunction_<'s> {
            id: Cow<'s, str>,
            args: VmIndex,
        }

        let partial = ExternFunction_::deserialize(deserializer)?;
        // Wrap any operators with parens so that they are acceptable for `get_global`
        let mut escaped_id = Cow::Borrowed("");
        let iter = partial
            .id
            .split(|c: char| c == '.')
            .map(|s| {
                if s.chars()
                    .next()
                    .map_or(false, ::base::ast::is_operator_char)
                {
                    Cow::Owned(format!("({})", s))
                } else {
                    Cow::Borrowed(s)
                }
            })
            .intersperse(Cow::Borrowed("."));
        for s in iter {
            escaped_id += s;
        }
        let function = seed.thread
            .get_global::<OpaqueValue<&Thread, Hole>>(&escaped_id)
            .map_err(|err| D::Error::custom(err))?;
        unsafe {
            match function.get_value().get_repr() {
                ValueRepr::Function(function) if partial.args == function.args => {
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

impl<T> SerializeState<SeSeed> for Array<T>
where
    T: SerializeState<SeSeed>,
{
    fn serialize_state<S>(&self, serializer: S, seed: &SeSeed) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        (**self).serialize_state(serializer, seed)
    }
}

pub fn serialize_userdata<S, T>(_: &T, _: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    use serde::ser::Error;
    Err(S::Error::custom("Userdata cannot be serialized"))
}

impl<'a> ::serde::ser::SerializeState<::serialization::SeSeed> for Variants<'a> {
    #[inline]
    fn serialize_state<S>(
        &self,
        serializer: S,
        seed: &::serialization::SeSeed,
    ) -> ::std::result::Result<S::Ok, S::Error>
    where
        S: ::serde::ser::Serializer,
    {
        self.0.serialize_state(serializer, seed)
    }
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
        let value: Value = DeSeed::new(&thread).deserialize(&mut de).unwrap();
        match value.get_repr() {
            ValueRepr::String(s) => assert_eq!(&*s, "test"),
            _ => ice!(),
        }
    }

    #[test]
    fn int_array() {
        let thread = RootedThread::new();
        let mut de = serde_json::Deserializer::from_str(
            r#" {
            "Array": {
                "Marked": [
                    0,
                    [
                        { "Int": 1 },
                        { "Int": 2 },
                        { "Int": 3 }
                    ]
                ]
            }
        } "#,
        );
        let value: Value = DeSeed::new(&thread).deserialize(&mut de).unwrap();
        match value.get_repr() {
            ValueRepr::Array(s) => assert_eq!(
                s.iter().map(|v| v.get_value()).collect::<Vec<_>>(),
                [Value::int(1), Value::int(2), Value::int(3)]
            ),
            _ => ice!(),
        }
    }
}
