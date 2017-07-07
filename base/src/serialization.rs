extern crate anymap;

use std::any::Any;
use std::cell::RefCell;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::ops::Deref;
use std::rc::Rc;
use std::sync::Arc;

use serde::de::{Deserialize, DeserializeSeed, DeserializeSeedEx, Deserializer, Error};
use serde::ser::{SerializeSeed, Serializer};

use symbol::Symbol;
use types::{ArcType, Type};

pub struct SeSeed {
    node_to_id: NodeToId,
}

impl SeSeed {
    pub fn new(node_to_id: NodeToId) -> Self {
        SeSeed { node_to_id: node_to_id }
    }
}

impl AsRef<NodeToId> for SeSeed {
    fn as_ref(&self) -> &NodeToId {
        &self.node_to_id
    }
}

impl Shared for ::kind::ArcKind {
    fn unique(&self) -> bool {
        ::kind::ArcKind::strong_count(self) == 1
    }

    fn as_ptr(&self) -> *const () {
        &**self as *const _ as *const ()
    }
}

impl<T> Shared for Arc<T> {
    fn unique(&self) -> bool {
        Arc::strong_count(self) == 1
    }

    fn as_ptr(&self) -> *const () {
        &**self as *const T as *const ()
    }
}

impl<T> Shared for ArcType<T> {
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


#[derive(Clone)]
pub struct IdSeed<Id>(NodeMap, PhantomData<Id>);

impl<Id> IdSeed<Id> {
    pub fn new(map: NodeMap) -> Self {
        IdSeed(map, PhantomData)
    }
}

impl<'de, Id> DeserializeSeed<'de> for IdSeed<Id>
where
    Id: Deserialize<'de>,
{
    type Value = Id;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        Id::deserialize(deserializer)
    }
}

impl<Id> AsMut<NodeMap> for IdSeed<Id> {
    fn as_mut(&mut self) -> &mut NodeMap {
        &mut self.0
    }
}

#[derive(Clone)]
pub struct MapSeed<S, F> {
    seed: S,
    map: F,
}

impl<S, F> MapSeed<S, F> {
    pub fn new(seed: S, map: F) -> MapSeed<S, F> {
        MapSeed {
            seed: seed,
            map: map,
        }
    }
}

impl<S, T, F> AsMut<T> for MapSeed<S, F>
where
    S: AsMut<T>,
{
    fn as_mut(&mut self) -> &mut T {
        self.seed.as_mut()
    }
}


impl<'de, S, F, R> DeserializeSeed<'de> for MapSeed<S, F>
where
    S: DeserializeSeed<'de>,
    F: FnOnce(S::Value) -> R,
{
    type Value = R;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        self.seed.deserialize(deserializer).map(self.map)
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

    pub fn get<T>(&self, id: &Id) -> Option<T>
    where
        T: Any + Clone,
    {
        self.0
            .borrow()
            .get::<IdToShared<T>>()
            .and_then(|map| map.get(id).cloned())
    }
}

pub struct SharedSeed<'seed, T: 'seed>(pub &'seed mut T);

impl<'seed, T> AsMut<T> for SharedSeed<'seed, T> {
    fn as_mut(&mut self) -> &mut T {
        self.0
    }
}

pub struct VariantSeed<T>(pub T);

fn deserialize_t<'de, D, T>(
    seed: &mut VariantSeed<T>,
    deserializer: D,
) -> Result<T::Value, D::Error>
where
    D: Deserializer<'de>,
    T: DeserializeSeed<'de>,
{
    seed.0.deserialize(deserializer)
}

#[derive(DeserializeSeed, SerializeSeed)]
#[serde(deserialize_seed = "VariantSeed<S>")]
#[serde(de_parameters = "S")]
#[serde(bound(deserialize = "S: DeserializeSeed<'de, Value = T>"))]
#[serde(bound(serialize = "T: SerializeSeed"))]
#[serde(serialize_seed = "T::Seed")]
pub enum Variant<T> {
    Marked(
        Id,
        #[serde(deserialize_seed_with = "deserialize_t")]
        #[serde(serialize_seed)]
        T
    ),
    Plain(
        #[serde(deserialize_seed_with = "deserialize_t")]
        #[serde(serialize_seed)]
        T
    ),
    Reference(Id),
}

impl<'de, 'seed, T> DeserializeSeed<'de> for SharedSeed<'seed, T>
where
    T: DeserializeSeed<'de>,
    T: AsMut<NodeMap>,
    T::Value: Any + Clone,
{
    type Value = T::Value;

    fn deserialize<D>(mut self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        match Variant::deserialize_seed(&mut VariantSeed(&mut self), deserializer)? {
            Variant::Marked(id, node) => {
                self.0.as_mut().insert(id, node.clone());
                Ok(node)
            }
            Variant::Plain(value) => Ok(value),
            Variant::Reference(id) => {
                match self.0.as_mut().get(&id) {
                    Some(rc) => Ok(rc),
                    None => Err(D::Error::custom(format_args!("missing id {}", id))),
                }
            }
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
    T: Shared,
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


pub fn serialize_shared<S, T>(
    self_: &T,
    serializer: S,
    seed: &<T::Target as SerializeSeed>::Seed,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
    T: Shared + Deref,
    T::Target: SerializeSeed,
    <T::Target as SerializeSeed>::Seed: AsRef<NodeToId>,
{
    let node = match node_to_id(seed.as_ref(), self_) {
        Lookup::Unique => Variant::Plain(&**self_),
        Lookup::Found(id) => Variant::Reference(id),
        Lookup::Inserted(id) => Variant::Marked(id, &**self_),
    };
    node.serialize_seed(serializer, seed)
}

pub fn serialize_seq<'a, S, T, V>(
    self_: &'a T,
    serializer: S,
    seed: &V::Seed,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
    T: Deref<Target = [V]>,
    V: SerializeSeed,
{
    (**self_).serialize_seed(serializer, seed)
}
