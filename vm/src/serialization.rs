use std::borrow::Cow;
use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;
use std::sync::Arc;

use itertools::Itertools;

use crate::serde::de::{Deserialize, DeserializeSeed, DeserializeState, Error};
use crate::serde::ser::{Seeded, Serialize, SerializeSeq, SerializeState, Serializer};
use crate::serde::Deserializer;

use crate::base::serialization::{NodeMap, NodeToId};
use crate::base::symbol::{Symbol, Symbols};
use crate::base::types::ArcType;

use crate::array::Array;
use crate::gc::{DataDef, GcPtr, GcRef, OwnedGcRef, WriteOnly};
use crate::thread::{RootedThread, RootedValue, Thread, ThreadInternal};
use crate::types::VmIndex;
use crate::value::{
    BytecodeFunction, Callable, ClosureData, ExternFunction, PartialApplicationData,
    PartialApplicationDataDef, Value, ValueArray, ValueRepr,
};
use crate::Variants;

#[derive(Clone)]
pub struct DeSeed {
    pub thread: RootedThread,
    symbols: Rc<RefCell<Symbols>>,
    gc_map: NodeMap,
    base_seed: crate::base::serialization::Seed<Symbol, ArcType<Symbol>>,
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
    node_to_id: crate::base::serialization::SeSeed,
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
    use crate::serde::{
        de::{Deserialize, DeserializeState, Deserializer},
        ser::{Serialize, SerializeState, Serializer},
    };

    use crate::{
        interner::InternedStr,
        thread::ThreadInternal,
        types::VmTag,
        value::{DataStruct, GcStr, ValueArray},
    };

    impl Serialize for GcStr {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            (**self).serialize(serializer)
        }
    }

    impl<'de, T> DeserializeState<'de, DeSeed> for crate::gc::Move<T>
    where
        T: crate::gc::Trace + PostDeserialize,
        T: DeserializeState<'de, DeSeed>,
    {
        fn deserialize_state<D>(seed: &mut DeSeed, deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            T::deserialize_state(seed, deserializer).map(crate::gc::Move)
        }
    }

    impl<'de, T> DeserializeState<'de, DeSeed> for GcPtr<T>
    where
        T: crate::gc::Trace + PostDeserialize + 'static,
        T: DeserializeState<'de, DeSeed>,
    {
        fn deserialize_state<D>(seed: &mut DeSeed, deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            use crate::gc::Move;
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
    #[serde(deserialize_state = "crate::serialization::DeSeed")]
    #[serde(serialize_state = "crate::serialization::SeSeed")]
    #[serde(bound(
        deserialize = "F: DeserializeState<'de, crate::serialization::DeSeed>,
                                 S: std::ops::Deref + std::any::Any + Clone
                                    + crate::base::serialization::Shared
                                    + DeserializeState<'de, crate::serialization::DeSeed>",
        serialize = "F: SerializeState<crate::serialization::SeSeed>,
                               S: std::ops::Deref + std::any::Any + Clone
                                    + crate::base::serialization::Shared,
                               S::Target: SerializeState<crate::serialization::SeSeed>"
    ))]
    struct Data<F, S> {
        #[serde(state)]
        tag: DataTag<S>,
        #[serde(state)]
        fields: F,
    }

    #[derive(DeserializeState, SerializeState)]
    #[serde(deserialize_state = "crate::serialization::DeSeed")]
    #[serde(serialize_state = "crate::serialization::SeSeed")]
    #[serde(bound(
        deserialize = "S: std::ops::Deref + std::any::Any + Clone
                                    + crate::base::serialization::Shared
                                    + DeserializeState<'de, crate::serialization::DeSeed>",
        serialize = "S: std::ops::Deref + std::any::Any + Clone
                                    + crate::base::serialization::Shared,
                               S::Target: SerializeState<crate::serialization::SeSeed>"
    ))]
    enum DataTag<S> {
        Record(#[serde(state_with = "crate::base::serialization::shared")] S),
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
            }
            .serialize_state(serializer, seed)
        }
    }

    pub fn deserialize_data<'de, D>(
        seed: &mut DeSeed,
        deserializer: D,
    ) -> Result<GcPtr<DataStruct>, D::Error>
    where
        D: Deserializer<'de>,
    {
        use crate::base::serialization::SharedSeed;

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
                use crate::value::{Def, RecordDef};
                unsafe {
                    Ok(match def.tag {
                        DataTag::Record(fields) => seed
                            .thread
                            .context()
                            .gc
                            .alloc(RecordDef {
                                elems: &def.fields,
                                fields: &fields[..],
                            })
                            .map_err(D::Error::custom)?
                            .unrooted(),
                        DataTag::Data(tag) => seed
                            .thread
                            .context()
                            .gc
                            .alloc(Def {
                                tag: tag,
                                elems: &def.fields,
                            })
                            .map_err(D::Error::custom)?
                            .unrooted(),
                    })
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
            // FIXME
            unsafe {
                Ok(Cow::<str>::deserialize(deserializer).and_then(|s| {
                    seed.thread
                        .context()
                        .gc
                        .alloc(&s[..])
                        .map(|v| v.unrooted())
                        .map_err(D::Error::custom)
                })?)
            }
        }
    }

    impl<T> crate::base::serialization::Shared for GcPtr<T> {
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
            crate::base::serialization::shared::serialize(self, serializer, seed)
        }
    }
}

pub mod symbol {
    use super::*;
    use crate::base::symbol::Symbol;
    use crate::serde::ser::{Serialize, Serializer};
    use crate::serde::{Deserialize, Deserializer};

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
    use crate::interner::InternedStr;

    use crate::serde::ser::{Serialize, SerializeState, Serializer};
    use crate::serde::{Deserialize, Deserializer};

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
    use crate::base::symbol::Symbol;
    use crate::base::types::ArcType;

    impl std::borrow::Borrow<crate::base::serialization::Seed<Symbol, ArcType<Symbol>>> for DeSeed {
        fn borrow(&self) -> &crate::base::serialization::Seed<Symbol, ArcType<Symbol>> {
            &self.base_seed
        }
    }
    impl std::borrow::BorrowMut<crate::base::serialization::Seed<Symbol, ArcType<Symbol>>> for DeSeed {
        fn borrow_mut(&mut self) -> &mut crate::base::serialization::Seed<Symbol, ArcType<Symbol>> {
            &mut self.base_seed
        }
    }

    impl std::borrow::Borrow<crate::base::serialization::SeSeed> for SeSeed {
        fn borrow(&self) -> &crate::base::serialization::SeSeed {
            &self.node_to_id
        }
    }
}

pub mod atomic_cell {
    use super::*;

    use crossbeam_utils::atomic::AtomicCell;

    pub fn deserialize<'de, D, T>(deserializer: D) -> Result<AtomicCell<T>, D::Error>
    where
        D: Deserializer<'de>,
        T: Deserialize<'de>,
    {
        T::deserialize(deserializer).map(AtomicCell::new)
    }

    pub fn serialize<S, T>(t: &AtomicCell<T>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: Serialize + Copy,
    {
        t.load().serialize(serializer)
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
                std::iter::repeat(())
                    .map(|_| ValueRepr::Int(0).into())
                    .take(self.upvars),
            );
            result
        }
    }
}

#[derive(Deserialize, Serialize)]
enum GraphVariant {
    Marked(crate::base::serialization::Id),
    Reference(crate::base::serialization::Id),
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
            let len = node_to_id.len() as crate::base::serialization::Id;
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

        use crate::serde::de::{SeqAccess, Visitor};

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
                        let variant = seq
                            .next_element()?
                            .ok_or_else(|| V::Error::invalid_length(0, &self))?;
                        unsafe {
                            match variant {
                                GraphVariant::Marked(id) => {
                                    let function = seq
                                        .next_element_seed(crate::serde::de::Seed::new(
                                            &mut self.state,
                                        ))?
                                        .ok_or_else(|| V::Error::invalid_length(1, &self))?;
                                    let upvars = seq
                                        .next_element()?
                                        .ok_or_else(|| V::Error::invalid_length(2, &self))?;

                                    let mut closure: GcPtr<ClosureData> = self
                                        .state
                                        .thread
                                        .context()
                                        .gc
                                        .alloc(ClosureDataModel {
                                            function: function,
                                            upvars: upvars,
                                        })
                                        .map_err(V::Error::custom)?
                                        .unrooted();
                                    self.state.gc_map.insert(id, closure);

                                    for i in 0..upvars {
                                        let value = seq
                                            .next_element_seed(crate::serde::de::Seed::new(
                                                &mut self.state,
                                            ))?
                                            .ok_or_else(|| {
                                                V::Error::invalid_length(i + 2, &self)
                                            })?;
                                        closure.as_mut().upvars[i] = value;
                                    }
                                    Ok(closure)
                                }
                                GraphVariant::Reference(id) => {
                                    match self.state.gc_map.get::<GcPtr<ClosureData>>(id) {
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
        PartialApplicationDataDef::size_of(self.args.len())
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

pub trait PostDeserialize {
    fn init<'gc>(parent: &Thread, ptr: OwnedGcRef<'gc, Self>) -> GcRef<'gc, Self>;
}

impl PostDeserialize for PartialApplicationData {
    fn init<'gc>(_parent: &Thread, ptr: OwnedGcRef<'gc, Self>) -> GcRef<'gc, Self> {
        ptr.into()
    }
}

impl PostDeserialize for ValueArray {
    fn init<'gc>(_parent: &Thread, ptr: OwnedGcRef<'gc, Self>) -> GcRef<'gc, Self> {
        ptr.into()
    }
}

impl PostDeserialize for ExternFunction {
    fn init<'gc>(_parent: &Thread, ptr: OwnedGcRef<'gc, Self>) -> GcRef<'gc, Self> {
        ptr.into()
    }
}

impl PostDeserialize for BytecodeFunction {
    fn init<'gc>(_parent: &Thread, ptr: OwnedGcRef<'gc, Self>) -> GcRef<'gc, Self> {
        ptr.into()
    }
}

impl PostDeserialize for Thread {
    fn init<'gc>(parent: &Thread, mut ptr: OwnedGcRef<'gc, Self>) -> GcRef<'gc, Self> {
        let mut parent_threads = parent.child_threads.write().unwrap();
        let entry = parent_threads.vacant_entry();
        ptr.thread_index = entry.key();
        let ptr = GcRef::from(ptr);
        unsafe {
            entry.insert((ptr.clone().unrooted(), 0));
        }
        ptr
    }
}

struct DataDefSeed<T>(PhantomData<T>);

impl<'de, T> DeserializeSeed<'de> for crate::serialization::Seed<DataDefSeed<T>>
where
    T: DataDef + 'static,
    <T as DataDef>::Value: Sized + PostDeserialize,
    T: DeserializeState<'de, DeSeed>,
{
    type Value = GcPtr<<T as DataDef>::Value>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        use crate::base::serialization::SharedSeed;

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
            <T as DataDef>::Value: PostDeserialize + Sized,
            T: DeserializeState<'de, DeSeed>,
        {
            fn deserialize_state<D>(seed: &mut GcSeed<T>, deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                let def = T::deserialize_state(&mut seed.state, deserializer)?;
                let mut context = seed.state.thread.context();
                let ptr = context.gc.alloc_owned(def).map_err(D::Error::custom)?;
                unsafe { Ok(T::Value::init(&seed.state.thread, ptr).unrooted()) }
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
        use crate::api::{Hole, OpaqueValue};
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
                    .map_or(false, crate::base::ast::is_operator_char)
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
        let function = seed
            .thread
            .get_global::<OpaqueValue<RootedThread, Hole>>(&escaped_id)
            .map_err(|err| D::Error::custom(err))?;
        match function.get_value().get_repr() {
            ValueRepr::Function(function) if partial.args == function.args => Ok(ExternFunction {
                id: function.id.clone(),
                args: function.args,
                function: function.function,
            }),
            _ => Err(D::Error::custom("Invalid type for extern function")),
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
    use crate::serde::ser::Error;
    Err(S::Error::custom("Userdata cannot be serialized"))
}

impl<'a> crate::serde::ser::SerializeState<crate::serialization::SeSeed> for Variants<'a> {
    #[inline]
    fn serialize_state<S>(
        &self,
        serializer: S,
        seed: &crate::serialization::SeSeed,
    ) -> std::result::Result<S::Ok, S::Error>
    where
        S: crate::serde::ser::Serializer,
    {
        self.0.serialize_state(serializer, seed)
    }
}

impl<'de> DeserializeState<'de, DeSeed> for RootedValue<RootedThread> {
    fn deserialize_state<D>(seed: &mut DeSeed, deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let value = Value::deserialize_state(seed, deserializer)?;
        Ok(seed.thread.root_value(Variants::new(&value)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{thread::RootedThread, value::Value};

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
                s.iter().collect::<Vec<_>>(),
                [Variants::int(1), Variants::int(2), Variants::int(3)]
            ),
            _ => ice!(),
        }
    }
}
