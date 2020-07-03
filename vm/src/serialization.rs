use std::{borrow::Cow, cell::RefCell, marker::PhantomData, rc::Rc, sync::Arc};

use itertools::Itertools;

use crate::serde::{
    de::{Deserialize, DeserializeSeed, DeserializeState, Error},
    ser::{Seeded, Serialize, SerializeSeq, SerializeState, Serializer},
    Deserializer,
};

use crate::base::{
    serialization::{NodeMap, NodeToId, SharedSeed},
    symbol::{Symbol, Symbols},
    types::ArcType,
};

use crate::{
    array::Array,
    gc::{CloneUnrooted, DataDef, GcPtr, GcRef, OwnedGcRef, WriteOnly},
    stack::State,
    thread::{ActiveThread, ExecuteContext, RootedThread, RootedValue, Thread, ThreadInternal},
    types::VmIndex,
    value::{
        BytecodeFunction, Callable, ClosureData, ExternFunction, PartialApplicationData,
        PartialApplicationDataDef, Value, ValueArray, ValueRepr,
    },
    Variants,
};

pub struct DeSeed<'gc> {
    pub thread: RootedThread,
    context: ExecuteContext<'gc, 'gc, State>,
    symbols: Rc<RefCell<Symbols>>,
    gc_map: NodeMap,
    base_seed: crate::base::serialization::Seed<Symbol, ArcType<Symbol>>,
}

impl<'de, 'gc> DeSeed<'gc> {
    pub fn new(thread: &Thread, context: &'gc mut ActiveThread) -> DeSeed<'gc> {
        DeSeed {
            thread: thread.root_thread(),
            symbols: Default::default(),
            gc_map: NodeMap::default(),
            base_seed: Default::default(),
            context: context.context(),
        }
    }

    pub fn deserialize<D, T>(mut self, deserializer: D) -> Result<T, D::Error>
    where
        D: Deserializer<'de>,
        T: DeserializeState<'de, Self>,
    {
        T::deserialize_state(&mut self, deserializer)
    }
}

impl AsMut<NodeMap> for DeSeed<'_> {
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

fn gc_seed<S, T>(seed: &mut S) -> SharedSeed<GcPtr<T>, S> {
    SharedSeed::with_cloner(seed, |p| unsafe { p.clone_unrooted() })
}

pub struct Seed<'a, 'gc, T> {
    pub state: &'a mut DeSeed<'gc>,
    _marker: PhantomData<T>,
}

impl<T> AsMut<NodeMap> for Seed<'_, '_, T> {
    fn as_mut(&mut self) -> &mut NodeMap {
        &mut self.state.gc_map
    }
}

impl<'a, 'gc, T> From<&'a mut DeSeed<'gc>> for Seed<'a, 'gc, T> {
    fn from(value: &'a mut DeSeed<'gc>) -> Self {
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

    impl<'de, 'gc, T> DeserializeState<'de, DeSeed<'gc>> for crate::gc::Move<T>
    where
        T: crate::gc::Trace + PostDeserialize,
        T: DeserializeState<'de, DeSeed<'gc>>,
    {
        fn deserialize_state<D>(seed: &mut DeSeed<'gc>, deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            T::deserialize_state(seed, deserializer).map(crate::gc::Move)
        }
    }

    impl<'de, 'gc, T> DeserializeState<'de, DeSeed<'gc>> for GcPtr<T>
    where
        T: crate::gc::Trace + PostDeserialize + 'static,
        T: DeserializeState<'de, DeSeed<'gc>>,
    {
        fn deserialize_state<D>(seed: &mut DeSeed<'gc>, deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            use crate::gc::Move;
            DeserializeSeed::deserialize(Seed::<DataDefSeed<Move<T>>>::from(seed), deserializer)
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

    pub fn deserialize_array<'de, 'gc, D>(
        seed: &mut DeSeed<'gc>,
        deserializer: D,
    ) -> Result<GcPtr<ValueArray>, D::Error>
    where
        D: Deserializer<'de>,
    {
        DeserializeSeed::deserialize(Seed::<DataDefSeed<Vec<Value>>>::from(seed), deserializer)
    }

    #[derive(DeserializeState, SerializeState)]
    #[serde(
        deserialize_state = "crate::serialization::DeSeed<'gc>",
        de_parameters = "'gc"
    )]
    #[serde(serialize_state = "crate::serialization::SeSeed")]
    #[serde(bound(
        deserialize = "F: DeserializeState<'de, crate::serialization::DeSeed<'gc>>,
                                 S: std::ops::Deref + std::any::Any + Clone
                                    + crate::base::serialization::Shared
                                    + DeserializeState<'de, crate::serialization::DeSeed<'gc>>",
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
    #[serde(
        deserialize_state = "crate::serialization::DeSeed<'gc>",
        de_parameters = "'gc"
    )]
    #[serde(serialize_state = "crate::serialization::SeSeed")]
    #[serde(bound(
        deserialize = "S: std::ops::Deref + std::any::Any + Clone
                                    + crate::base::serialization::Shared
                                    + DeserializeState<'de, crate::serialization::DeSeed<'gc>>",
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

    pub fn deserialize_data<'de, 'gc, D>(
        seed: &mut DeSeed<'gc>,
        deserializer: D,
    ) -> Result<GcPtr<DataStruct>, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct GcSeed<'a, 'gc> {
            state: &'a mut DeSeed<'gc>,
        }
        impl<'a> AsMut<NodeMap> for GcSeed<'a, '_> {
            fn as_mut(&mut self) -> &mut NodeMap {
                &mut self.state.gc_map
            }
        }

        impl<'de, 'gc, 'a> DeserializeState<'de, GcSeed<'a, 'gc>> for GcPtr<DataStruct> {
            fn deserialize_state<D>(
                seed: &mut GcSeed<'a, 'gc>,
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
                            .context
                            .gc
                            .alloc(RecordDef {
                                elems: &def.fields,
                                fields: &fields[..],
                            })
                            .map_err(D::Error::custom)?
                            .unrooted(),
                        DataTag::Data(tag) => seed
                            .context
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

        DeserializeSeed::deserialize(gc_seed(&mut seed), deserializer)
    }

    impl<'de, 'gc> DeserializeState<'de, DeSeed<'gc>> for GcStr {
        fn deserialize_state<D>(seed: &mut DeSeed<'gc>, deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            // FIXME
            unsafe {
                Ok(Cow::<str>::deserialize(deserializer).and_then(|s| {
                    seed.context
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

    pub fn deserialize<'de, 'gc, D>(
        seed: &mut DeSeed<'gc>,
        deserializer: D,
    ) -> Result<Symbol, D::Error>
    where
        D: Deserializer<'de>,
    {
        String::deserialize(deserializer).map(|s| seed.symbols.borrow_mut().simple_symbol(s))
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

    impl<'de, 'gc> DeserializeState<'de, DeSeed<'gc>> for InternedStr {
        fn deserialize_state<D>(seed: &mut DeSeed<'gc>, deserializer: D) -> Result<Self, D::Error>
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

pub mod rw_lock {
    use super::*;

    pub fn deserialize<'de, D, T, Seed>(
        seed: &mut Seed,
        deserializer: D,
    ) -> Result<parking_lot::RwLock<T>, D::Error>
    where
        D: Deserializer<'de>,
        T: DeserializeState<'de, Seed>,
    {
        T::deserialize_state(seed, deserializer).map(parking_lot::RwLock::new)
    }

    pub fn serialize<S, T, Seed>(
        t: &parking_lot::RwLock<T>,
        serializer: S,
        seed: &Seed,
    ) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: SerializeState<Seed>,
    {
        t.read().serialize_state(serializer, seed)
    }
}

pub mod typ {
    use super::*;
    use crate::base::symbol::Symbol;
    use crate::base::types::ArcType;

    impl std::borrow::Borrow<crate::base::serialization::Seed<Symbol, ArcType<Symbol>>> for DeSeed<'_> {
        fn borrow(&self) -> &crate::base::serialization::Seed<Symbol, ArcType<Symbol>> {
            &self.base_seed
        }
    }
    impl std::borrow::BorrowMut<crate::base::serialization::Seed<Symbol, ArcType<Symbol>>>
        for DeSeed<'_>
    {
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
        serializer.serialize_element(&Seeded::new(seed, &self.function))?;
        serializer.serialize_element(&self.upvars.len())?;
        for item in self.upvars.iter() {
            serializer.serialize_element(&Seeded::new(seed, item))?;
        }
        serializer.end()
    }
}

pub mod closure {
    use super::*;

    pub fn deserialize<'de, 'gc, D>(
        seed: &mut DeSeed<'gc>,
        deserializer: D,
    ) -> Result<GcPtr<ClosureData>, D::Error>
    where
        D: Deserializer<'de>,
    {
        use std::fmt;

        use crate::serde::de::{SeqAccess, Visitor};

        impl<'de, 'gc> DeserializeSeed<'de> for Seed<'_, 'gc, ClosureData> {
            type Value = GcPtr<ClosureData>;

            fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where
                D: Deserializer<'de>,
            {
                impl<'de, 'gc> Visitor<'de> for Seed<'_, 'gc, ClosureData> {
                    type Value = GcPtr<ClosureData>;

                    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        formatter.write_str("struct ClosureData")
                    }

                    fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
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
                                            &mut *self.state,
                                        ))?
                                        .ok_or_else(|| V::Error::invalid_length(1, &self))?;
                                    let upvars = seq
                                        .next_element()?
                                        .ok_or_else(|| V::Error::invalid_length(2, &self))?;

                                    let mut closure: GcPtr<ClosureData> = self
                                        .state
                                        .context
                                        .gc
                                        .alloc(ClosureDataModel {
                                            function: function,
                                            upvars: upvars,
                                        })
                                        .map_err(V::Error::custom)?
                                        .unrooted();
                                    self.state.gc_map.insert(id, closure.clone_unrooted());

                                    for i in 0..upvars {
                                        let value = seq
                                            .next_element_seed(crate::serde::de::Seed::new(
                                                &mut *self.state,
                                            ))?
                                            .ok_or_else(|| {
                                                V::Error::invalid_length(i + 2, &self)
                                            })?;
                                        closure.as_mut().upvars[i] = value;
                                    }
                                    Ok(closure)
                                }
                                GraphVariant::Reference(id) => {
                                    match self
                                        .state
                                        .gc_map
                                        .get_with::<GcPtr<ClosureData>, _>(id, |p| {
                                            p.clone_unrooted()
                                        }) {
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

        DeserializeSeed::deserialize(Seed::<ClosureData>::from(seed), deserializer)
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
#[cfg_attr(
    feature = "serde_derive",
    serde(deserialize_state = "DeSeed<'gc>", de_parameters = "'gc")
)]
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

pub fn deserialize_application<'de, 'gc, D>(
    seed: &mut DeSeed<'gc>,
    deserializer: D,
) -> Result<GcPtr<PartialApplicationData>, D::Error>
where
    D: Deserializer<'de>,
{
    DeserializeSeed::deserialize(
        Seed::<DataDefSeed<PartialApplicationModel>>::from(seed),
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
            entry.insert(ptr.clone().unrooted());
        }
        ptr
    }
}

struct DataDefSeed<T>(PhantomData<T>);

impl<'de, 'gc, T> DeserializeSeed<'de> for Seed<'_, 'gc, DataDefSeed<T>>
where
    T: DataDef + 'static,
    <T as DataDef>::Value: Sized + PostDeserialize,
    T: DeserializeState<'de, DeSeed<'gc>>,
{
    type Value = GcPtr<<T as DataDef>::Value>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct GcSeed<'a, 'gc, T> {
            _marker: PhantomData<T>,
            state: &'a mut DeSeed<'gc>,
        }
        impl<T> AsMut<NodeMap> for GcSeed<'_, '_, T> {
            fn as_mut(&mut self) -> &mut NodeMap {
                &mut self.state.gc_map
            }
        }

        impl<'de, 'gc, T> DeserializeState<'de, GcSeed<'_, 'gc, T>> for GcPtr<T::Value>
        where
            T: DataDef + 'static,
            <T as DataDef>::Value: PostDeserialize + Sized,
            T: DeserializeState<'de, DeSeed<'gc>>,
        {
            fn deserialize_state<D>(
                seed: &mut GcSeed<'_, 'gc, T>,
                deserializer: D,
            ) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                let def = T::deserialize_state(&mut seed.state, deserializer)?;
                let ptr = seed
                    .state
                    .context
                    .gc
                    .alloc_owned(def)
                    .map_err(D::Error::custom)?;
                unsafe { Ok(T::Value::init(&seed.state.thread, ptr).unrooted()) }
            }
        }

        let mut seed = GcSeed {
            _marker: PhantomData::<T>,
            state: self.state,
        };

        DeserializeSeed::deserialize(gc_seed(&mut seed), deserializer)
    }
}

impl<'de, 'gc> DeserializeState<'de, DeSeed<'gc>> for ExternFunction {
    fn deserialize_state<D>(seed: &mut DeSeed<'gc>, deserializer: D) -> Result<Self, D::Error>
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

impl<'de, 'gc> DeserializeState<'de, DeSeed<'gc>> for RootedValue<RootedThread> {
    fn deserialize_state<D>(seed: &mut DeSeed<'gc>, deserializer: D) -> Result<Self, D::Error>
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
        let value: Value = DeSeed::new(&thread, &mut thread.current_context())
            .deserialize(&mut de)
            .unwrap();
        match value.get_repr() {
            ValueRepr::String(s) => assert_eq!(&s[..], "test"),
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
        let value: Value = DeSeed::new(&thread, &mut thread.current_context())
            .deserialize(&mut de)
            .unwrap();
        match value.get_repr() {
            ValueRepr::Array(s) => assert_eq!(
                s.iter().collect::<Vec<_>>(),
                [Variants::int(1), Variants::int(2), Variants::int(3)]
            ),
            _ => ice!(),
        }
    }
}
