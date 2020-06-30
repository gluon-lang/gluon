use std::any::Any;
use std::cell::RefCell;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::ops::Deref;
use std::rc::Rc;
use std::sync::Arc;

use crate::serde::de::{DeserializeSeed, DeserializeState, Deserializer, Error};
use crate::serde::ser::{SerializeState, Serializer};

use crate::kind::ArcKind;
use crate::symbol::Symbol;
use crate::types::{AliasData, ArcType, Generic, Type, TypeExt, TypePtr};

#[derive(Default)]
pub struct SeSeed {
    pub node_to_id: NodeToId,
}

impl SeSeed {
    pub fn new(node_to_id: NodeToId) -> Self {
        SeSeed { node_to_id }
    }
}

impl AsRef<NodeToId> for SeSeed {
    fn as_ref(&self) -> &NodeToId {
        &self.node_to_id
    }
}

pub struct Seed<Id, T> {
    nodes: crate::serialization::NodeMap,
    _marker: PhantomData<(Id, T)>,
}

impl<Id, T> Default for Seed<Id, T> {
    fn default() -> Self {
        Seed::new(crate::serialization::NodeMap::default())
    }
}

impl<Id, T> AsMut<Seed<Id, T>> for Seed<Id, T> {
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

impl<Id, T> AsMut<crate::serialization::NodeMap> for Seed<Id, T> {
    fn as_mut(&mut self) -> &mut crate::serialization::NodeMap {
        &mut self.nodes
    }
}

impl<Id, T> Seed<Id, T> {
    pub fn new(nodes: crate::serialization::NodeMap) -> Self {
        Seed {
            nodes,
            _marker: PhantomData,
        }
    }
}

impl<Id, T> Clone for Seed<Id, T> {
    fn clone(&self) -> Self {
        Seed {
            nodes: self.nodes.clone(),
            _marker: PhantomData,
        }
    }
}

pub fn deserialize_group<'de, Id, T, D>(
    seed: &mut Seed<Id, T>,
    deserializer: D,
) -> Result<Arc<[AliasData<Id, T>]>, D::Error>
where
    D: crate::serde::Deserializer<'de>,
    T: TypePtr<Id = Id>
        + Clone
        + From<Type<Id, T>>
        + ::std::any::Any
        + DeserializeState<'de, Seed<Id, T>>,
    Id: DeserializeState<'de, Seed<Id, T>>
        + Clone
        + ::std::any::Any
        + DeserializeState<'de, Seed<Id, T>>,
    T::Generics: Default + Extend<Generic<Id>> + Clone,
{
    let seed = SharedSeed::new(seed);
    DeserializeSeed::deserialize(seed, deserializer).map(|vec: Vec<_>| Arc::from(vec))
}

impl<'a, T> Shared for &'a T {
    fn unique(&self) -> bool {
        false
    }

    fn as_ptr(&self) -> *const () {
        &**self as *const _ as *const ()
    }
}

impl Shared for crate::kind::ArcKind {
    fn unique(&self) -> bool {
        crate::kind::ArcKind::strong_count(self) == 1
    }

    fn as_ptr(&self) -> *const () {
        &**self as *const _ as *const ()
    }
}

impl<T> Shared for Arc<T>
where
    T: ?Sized,
{
    fn unique(&self) -> bool {
        Arc::strong_count(self) == 1
    }

    fn as_ptr(&self) -> *const () {
        &**self as *const T as *const ()
    }
}

impl<Id> Shared for ArcType<Id>
where
    Id: PartialEq,
{
    fn unique(&self) -> bool {
        ArcType::strong_count(self) == 1
    }

    fn as_ptr(&self) -> *const () {
        &**self as *const Type<_, _> as *const ()
    }
}

impl Shared for Symbol {
    fn unique(&self) -> bool {
        Symbol::strong_count(self) == 1
    }

    fn as_ptr(&self) -> *const () {
        &**self as *const _ as *const ()
    }
}

pub type Id = u32;
type IdToShared<T> = HashMap<Id, T>;

#[derive(Clone)]
pub struct NodeMap(Rc<RefCell<anymap::Map>>);

impl Default for NodeMap {
    fn default() -> Self {
        NodeMap(Rc::new(RefCell::new(anymap::Map::new())))
    }
}

impl AsMut<NodeMap> for NodeMap {
    fn as_mut(&mut self) -> &mut NodeMap {
        self
    }
}

impl NodeMap {
    pub fn insert<T>(&self, id: Id, value: T)
    where
        T: Any,
    {
        self.0
            .borrow_mut()
            .entry::<IdToShared<T>>()
            .or_insert(IdToShared::new())
            .insert(id, value);
    }

    pub fn get<T>(&self, id: Id) -> Option<T>
    where
        T: Any + Clone,
    {
        self.get_with(id, T::clone)
    }

    pub fn get_with<T, F>(&self, id: Id, clone: F) -> Option<T>
    where
        T: Any,
        F: FnOnce(&T) -> T,
    {
        self.0
            .borrow()
            .get::<IdToShared<T>>()
            .and_then(|map| map.get(&id).map(clone))
    }
}

pub struct SharedSeed<'seed, T, S: 'seed> {
    pub seed: &'seed mut S,
    cloner: fn(&T) -> T,
    _marker: PhantomData<T>,
}

impl<'seed, T, S> SharedSeed<'seed, T, S> {
    pub fn with_cloner(seed: &'seed mut S, cloner: fn(&T) -> T) -> Self {
        SharedSeed {
            seed,
            cloner,
            _marker: PhantomData,
        }
    }
}

impl<'seed, T, S> SharedSeed<'seed, T, S>
where
    T: Clone,
{
    pub fn new(seed: &'seed mut S) -> SharedSeed<'seed, T, S> {
        SharedSeed {
            seed,
            cloner: T::clone,
            _marker: PhantomData,
        }
    }
}

impl<'seed, T, S> AsMut<S> for SharedSeed<'seed, T, S> {
    fn as_mut(&mut self) -> &mut S {
        self.seed
    }
}

#[derive(DeserializeState, SerializeState)]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "S"))]
#[cfg_attr(feature = "serde_derive", serde(de_parameters = "S"))]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(deserialize = "T: DeserializeState<'de, S>"))
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(serialize = "T: SerializeState<S>"))
)]
#[cfg_attr(feature = "serde_derive", serde(ser_parameters = "S"))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "S"))]
pub enum Variant<T> {
    Marked(Id, #[cfg_attr(feature = "serde_derive", serde(state))] T),
    Plain(#[cfg_attr(feature = "serde_derive", serde(state))] T),
    Reference(Id),
}

impl<'de, 'seed, T, S> DeserializeSeed<'de> for SharedSeed<'seed, T, S>
where
    T: DeserializeState<'de, S>,
    S: AsMut<NodeMap>,
    T: Any,
{
    type Value = T;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        match Variant::<T>::deserialize_state(self.seed, deserializer)? {
            Variant::Marked(id, node) => {
                self.seed.as_mut().insert(id, (self.cloner)(&node));
                Ok(node)
            }
            Variant::Plain(value) => Ok(value),
            Variant::Reference(id) => match self.seed.as_mut().get_with(id, self.cloner) {
                Some(rc) => Ok(rc),
                None => Err(D::Error::custom(format_args!("missing id {}", id))),
            },
        }
    }
}

pub trait Shared {
    fn unique(&self) -> bool;
    fn as_ptr(&self) -> *const ();
}

pub type NodeToId = Rc<RefCell<HashMap<*const (), Id>>>;

enum Lookup {
    Unique,
    Found(Id),
    Inserted(Id),
}

fn node_to_id<T>(map: &NodeToId, node: &T) -> Lookup
where
    T: ?Sized + Shared,
{
    if Shared::unique(node) {
        return Lookup::Unique;
    }
    let mut map = map.borrow_mut();
    if let Some(id) = map.get(&node.as_ptr()) {
        return Lookup::Found(*id);
    }
    let id = map.len() as Id;
    map.insert(node.as_ptr(), id);
    Lookup::Inserted(id)
}

pub mod seq {
    use super::*;

    pub fn deserialize<'de, S, T, U, D>(seed: &mut S, deserializer: D) -> Result<T, D::Error>
    where
        D: crate::serde::Deserializer<'de>,
        T: Extend<U> + Default + ::std::any::Any,
        U: DeserializeState<'de, S> + Clone + ::std::any::Any + DeserializeState<'de, S>,
    {
        DeserializeSeed::deserialize(
            crate::serde::de::SeqSeedEx::new(seed, |_| T::default()),
            deserializer,
        )
    }

    pub fn serialize<'a, S, T, V, Seed>(
        self_: &'a T,
        serializer: S,
        seed: &Seed,
    ) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: Deref<Target = [V]>,
        V: SerializeState<Seed>,
    {
        (**self_).serialize_state(serializer, seed)
    }
}

impl<Id> SerializeState<SeSeed> for ArcType<Id>
where
    Id: SerializeState<SeSeed> + PartialEq,
{
    fn serialize_state<S>(&self, serializer: S, seed: &SeSeed) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        crate::serialization::shared::serialize(self, serializer, seed)
    }
}

impl SerializeState<SeSeed> for ArcKind {
    fn serialize_state<S>(&self, serializer: S, seed: &SeSeed) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        crate::serialization::shared::serialize(self, serializer, seed)
    }
}

pub mod shared {
    use super::*;
    use crate::serde::de::DeserializeSeed;

    pub fn serialize<S, T, Seed>(self_: &T, serializer: S, seed: &Seed) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
        T: ?Sized + Shared + Deref,
        T::Target: SerializeState<Seed>,
        Seed: AsRef<NodeToId>,
    {
        let node = match node_to_id(seed.as_ref(), self_) {
            Lookup::Unique => Variant::Plain(&**self_),
            Lookup::Found(id) => Variant::Reference(id),
            Lookup::Inserted(id) => Variant::Marked(id, &**self_),
        };
        node.serialize_state(serializer, seed)
    }

    pub fn deserialize<'de, D, S, T>(seed: &mut S, deserializer: D) -> Result<T, D::Error>
    where
        D: Deserializer<'de>,
        T: DeserializeState<'de, S>,
        S: AsMut<NodeMap>,
        T: Any + Clone,
    {
        SharedSeed::new(seed).deserialize(deserializer)
    }
}
