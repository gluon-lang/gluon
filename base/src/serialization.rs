extern crate anymap;

use std::any::Any;
use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::Deref;
use std::rc::Rc;

use serde::de::{Deserialize, DeserializeSeed, Deserializer, Error};
use serde::ser::{Serialize, SerializeSeed, Serializer};

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
    where S: AsMut<T>
{
    fn as_mut(&mut self) -> &mut T {
        self.seed.as_mut()
    }
}


impl<'de, S, F, R> DeserializeSeed<'de> for MapSeed<S, F>
    where S: DeserializeSeed<'de>,
          F: FnOnce(S::Value) -> R
{
    type Value = R;

    fn deserialize<D>(mut self, deserializer: D) -> Result<Self::Value, D::Error>
        where D: Deserializer<'de>
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
        where T: Any
    {
        self.0
            .borrow_mut()
            .entry::<IdToShared<T>>()
            .or_insert(IdToShared::new())
            .insert(id, value);
    }

    pub fn get<T>(&self, id: &Id) -> Option<T>
        where T: Any + Clone
    {
        self.0
            .borrow()
            .get::<IdToShared<T>>()
            .and_then(|map| map.get(id).cloned())
    }
}

pub struct SharedSeed<T>(pub T);

pub struct VariantSeed<T>(pub T);

fn deserialize_t<'de, D, T>(seed: &mut VariantSeed<T>,
                            deserializer: D)
                            -> Result<T::Value, D::Error>
    where D: Deserializer<'de>,
          T: DeserializeSeed<'de> + Clone
{
    seed.0.clone().deserialize(deserializer)
}

#[derive(DeserializeSeed, SerializeSeed)]
#[serde(deserialize_seed = "VariantSeed<T>")]
#[serde(bound(deserialize  = "T: DeserializeSeed<'de> + Clone"))]
#[serde(bound(serialize = "T: SerializeSeed"))]
#[serde(serialize_seed = "T::Seed")]
pub enum Variant<T> {
    Marked(Id,
           #[serde(deserialize_seed_with = "deserialize_t")]
           #[serde(serialize_seed)]
           T),
    Plain(#[serde(deserialize_seed_with = "deserialize_t")]
          #[serde(serialize_seed)]
          T),
    Reference(Id),
}

impl<'de, T> DeserializeSeed<'de> for SharedSeed<T>
    where T: DeserializeSeed<'de> + Clone,
          T: AsMut<NodeMap>,
          T::Value: Any + Clone
{
    type Value = T::Value;

    fn deserialize<D>(mut self, deserializer: D) -> Result<Self::Value, D::Error>
        where D: Deserializer<'de>
    {
        match VariantSeed(self.0.clone()).deserialize(deserializer)? {
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

pub type NodeToId = RefCell<HashMap<*const (), Id>>;

enum Lookup {
    Unique,
    Found(Id),
    Inserted(Id),
}

fn node_to_id<T>(map: &NodeToId, node: &T) -> Lookup
    where T: Shared
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


pub fn serialize_shared<S, T>(self_: &T,
                              serializer: S,
                              seed: &<T::Target as SerializeSeed>::Seed)
                              -> Result<S::Ok, S::Error>
    where S: Serializer,
          T: Shared + Deref,
          T::Target: SerializeSeed,
          <T::Target as SerializeSeed>::Seed: AsRef<NodeToId>
{
    let node = match node_to_id(seed.as_ref(), self_) {
        Lookup::Unique => Variant::Plain(&**self_),
        Lookup::Found(id) => Variant::Reference(id),
        Lookup::Inserted(id) => Variant::Marked(id, &**self_),
    };
    node.serialize_seed(serializer, seed)
}
