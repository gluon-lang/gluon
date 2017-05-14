use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;

#[cfg(test)]
use serde::Deserializer;
use serde::de::DeserializeSeed;

use base::symbol::Symbols;
use gc::GcPtr;
use thread::{RootedThread, ThreadInternal};

#[derive(Clone)]
pub struct DeSeed {
    thread: RootedThread,
    symbols: Rc<RefCell<Symbols>>,
}

impl DeSeed {
    pub fn new(thread: RootedThread) -> DeSeed {
        DeSeed {
            thread: thread,
            symbols: Default::default(),
        }
    }

    #[cfg(test)]
    pub fn deserialize<'de, D, T>(self, deserializer: D) -> Result<T, D::Error>
        where D: Deserializer<'de>,
              T: GcSerialize<'de>
    {
        <T::Seed>::from(self).deserialize(deserializer)
    }
}

pub struct SeSeed {
    interner: Symbols,
}

pub struct Seed<T> {
    state: DeSeed,
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

pub mod value {
    use super::*;
    use value::{Value, ValueTag};

    impl<'de> GcSerialize<'de> for Value {
        type Seed = Seed<ValueTag>;
    }
}

pub mod gc {
    use super::*;
    use base::symbol::Symbol;
    use serde::{Deserialize, Deserializer};
    use serde::de::{DeserializeSeed, Error, SeqSeed};
    use value::{DataStruct, GcStr, Value, ValueArray, ValueTag};
    use types::VmTag;

    impl<'de, T> GcSerialize<'de> for GcPtr<T>
        where T: GcSerialize<'de> + ::gc::Traverseable + 'static
    {
        type Seed = Seed<GcPtrTag<T>>;
    }

    #[derive(Default)]
    pub struct GcPtrTag<T>(PhantomData<T>);

    impl<'de, T> DeserializeSeed<'de> for Seed<GcPtrTag<T>>
        where T: GcSerialize<'de> + ::gc::Traverseable + 'static,
              T::Seed: DeserializeSeed<'de>
    {
        type Value = GcPtr<T>;

        fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where D: Deserializer<'de>
        {
            <T::Seed>::from(self.state.clone())
                .deserialize(deserializer)
                .map(|s| {
                         self.state
                             .thread
                             .context()
                             .alloc_with(&self.state.thread, ::gc::Move(s))
                             .unwrap()
                     })
        }
    }

    pub fn deserialize<'de, D, T, U>(seed: &mut Seed<U>,
                                     deserializer: D)
                                     -> Result<GcPtr<T>, D::Error>
        where D: Deserializer<'de>,
              T: GcSerialize<'de> + ::gc::Traverseable + 'static,
              T::Seed: DeserializeSeed<'de>
    {
        Seed::<GcPtrTag<T>>::from(seed.state.clone()).deserialize(deserializer)
    }

    #[derive(Default)]
    pub struct GcPtrArraySeed;

    impl<'de> DeserializeSeed<'de> for Seed<GcPtrArraySeed> {
        type Value = GcPtr<ValueArray>;

        fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where D: Deserializer<'de>
        {
            use value::ArrayDef;
            SeqSeed::new(Seed::<ValueTag>::from(self.state.clone()),
                         Vec::with_capacity)
                    .deserialize(deserializer)
                    .and_then(|s: Vec<Value>| {
                                  self.state
                                      .thread
                                      .context()
                                      .alloc(ArrayDef(&s))
                                      .map_err(D::Error::custom)
                              })
        }
    }

    pub fn deserialize_array<'de, D, T>(seed: &mut Seed<T>,
                                        deserializer: D)
                                        -> Result<GcPtr<ValueArray>, D::Error>
        where D: Deserializer<'de>
    {
        Seed::<GcPtrArraySeed>::from(seed.state.clone()).deserialize(deserializer)
    }

    fn deserialize_vec<'de, D, T, U>(seed: &mut Seed<T>,
                                     deserializer: D)
                                     -> Result<Vec<U>, D::Error>
        where D: Deserializer<'de>,
              U: GcSerialize<'de>,
              U::Seed: Clone
    {
        SeqSeed::new(U::Seed::from(seed.state.clone()), Vec::with_capacity)
            .deserialize(deserializer)
    }

    #[derive(Default)]
    pub struct GcPtrDataStructTag;
    #[derive(DeserializeSeed)]
    #[serde(deserialize_seed = "::serialization::Seed<GcPtrDataStructTag>")]
    struct Data {
        tag: VmTag,
        #[serde(deserialize_seed_with = "deserialize_vec")]
        elems: Vec<Value>,
    }

    pub fn deserialize_data<'de, D, T>(seed: &mut Seed<T>,
                                       deserializer: D)
                                       -> Result<GcPtr<DataStruct>, D::Error>
        where D: Deserializer<'de>
    {
        use value::Def;

        Seed::<GcPtrDataStructTag>::from(seed.state.clone())
            .deserialize(deserializer)
            .and_then(|data| {
                seed.state
                    .thread
                    .context()
                    .alloc(Def {
                               tag: data.tag,
                               elems: &data.elems,
                           })
                    .map_err(D::Error::custom)
            })
    }

    pub fn deserialize_str<'de, D, T>(seed: &mut Seed<T>,
                                      deserializer: D)
                                      -> Result<GcStr, D::Error>
        where D: Deserializer<'de>
    {
        String::deserialize(deserializer)
            .map(|s| unsafe {
                     GcStr::from_utf8_unchecked(seed.state
                                                    .thread
                                                    .context()
                                                    .alloc(s.as_bytes())
                                                    .unwrap())
                 })
    }
}

pub mod symbol {
    use super::DeSeed;
    use base::symbol::Symbol;
    use serde::{Deserialize, Deserializer};

    pub fn deserialize<'de, D>(seed: &mut DeSeed, deserializer: D) -> Result<Symbol, D::Error>
        where D: Deserializer<'de>
    {
        String::deserialize(deserializer).map(|s| seed.symbols.borrow_mut().symbol(s))
    }
}

pub mod intern {
    use super::DeSeed;
    use interner::InternedStr;
    use thread::ThreadInternal;

    use serde::{Deserialize, Deserializer};
    use serde::de::{DeserializeSeed, SeqSeed};

    pub fn deserialize<'de, D>(seed: &mut DeSeed,
                               deserializer: D)
                               -> Result<Vec<InternedStr>, D::Error>
        where D: Deserializer<'de>
    {
        Vec::<String>::deserialize(deserializer).map(|v| {
            v.into_iter()
                .map(|s| seed.thread.global_env().intern(&s).unwrap())
                .collect()
        })
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
