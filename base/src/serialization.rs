use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use serde::de::{Deserialize, DeserializeSeed, Deserializer, Error};

type Id = u32;
type IdToShared<T> = HashMap<Id, T>;

#[derive(Default)]
pub struct NodeMap<T>(Rc<RefCell<IdToShared<T>>>);

pub struct SharedSeed<T>(T);

struct VariantSeed<T>(T);

fn deserialize_t<'de, D, T>(seed: &mut VariantSeed<T>,
                            deserializer: D)
                            -> Result<T::Value, D::Error>
    where D: Deserializer<'de>,
          T: DeserializeSeed<'de> + Clone
{
    seed.0.clone().deserialize(deserializer)
}

#[derive(DeserializeSeed)]
#[serde(deserialize_seed = "VariantSeed<T>")]
#[serde(bound = "T: DeserializeSeed<'de> + Clone")]
enum Variant<T> {
    Marked(Id,
           #[serde(deserialize_seed_with = "deserialize_t")]
           T),
    Plain(#[serde(deserialize_seed_with = "deserialize_t")]
          T),
    Reference(Id),
}

impl<'de, T> DeserializeSeed<'de> for SharedSeed<T>
    where T: DeserializeSeed<'de> + Deserialize<'de> + Clone,
          T: AsMut<NodeMap<<T as DeserializeSeed<'de>>::Value>>,
          T::Value: Clone
{
    type Value = T::Value;

    fn deserialize<D>(mut self, deserializer: D) -> Result<Self::Value, D::Error>
        where D: Deserializer<'de>
    {

        match VariantSeed(self.0.clone()).deserialize(deserializer)? {
            Variant::Marked(id, node) => {
                self.0
                    .as_mut()
                    .0
                    .borrow_mut()
                    .insert(id, node.clone());
                Ok(node)
            }
            Variant::Plain(value) => Ok(value),
            Variant::Reference(id) => {
                match self.0.as_mut().0.borrow_mut().get(&id) {
                    Some(rc) => Ok(rc.clone()),
                    None => Err(D::Error::custom(format_args!("missing id {}", id))),
                }
            }
        }
    }
}
