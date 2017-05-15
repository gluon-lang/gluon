use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;

use serde::Deserializer;
use serde::de::{DeserializeSeed, SeqSeed};

use base::symbol::Symbols;
use gc::GcPtr;
use thread::RootedThread;

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
    use value::{DataStruct, GcStr, Value, ValueArray};
    use thread::ThreadInternal;
    use types::VmTag;

    impl<'de, T> GcSerialize<'de> for GcPtr<T>
        where T: GcSerialize<'de> + ::gc::Traverseable + 'static
    {
        type Seed = Seed<GcPtr<T>>;
    }

    impl<'de, T> DeserializeSeed<'de> for Seed<GcPtr<T>>
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

    #[derive(Default)]
    pub struct GcPtrArraySeed;

    impl<'de> DeserializeSeed<'de> for Seed<GcPtrArraySeed> {
        type Value = GcPtr<ValueArray>;

        fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where D: Deserializer<'de>
        {
            use value::ArrayDef;
            SeqSeed::new(Seed::<Value>::from(self.state.clone()), Vec::with_capacity)
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

    #[derive(DeserializeSeed)]
    #[serde(deserialize_seed = "::serialization::Seed<Data>")]
    pub struct Data {
        tag: VmTag,
        #[serde(deserialize_seed_with = "::serialization::deserialize")]
        elems: Vec<Value>,
    }

    pub fn deserialize_data<'de, D, T>(seed: &mut Seed<T>,
                                       deserializer: D)
                                       -> Result<GcPtr<DataStruct>, D::Error>
        where D: Deserializer<'de>
    {
        use value::Def;

        Seed::<Data>::from(seed.state.clone())
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

    impl<'de> GcSerialize<'de> for GcStr {
        type Seed = Seed<GcStr>;
    }

    impl<'de> DeserializeSeed<'de> for Seed<GcStr> {
        type Value = GcStr;

        fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where D: Deserializer<'de>
        {
            String::deserialize(deserializer)
                .map(|s| unsafe {
                         GcStr::from_utf8_unchecked(self.state
                                                        .thread
                                                        .context()
                                                        .alloc(s.as_bytes())
                                                        .unwrap())
                     })
        }
    }
}

pub mod symbol {
    use super::*;
    use base::symbol::Symbol;
    use serde::{Deserialize, Deserializer};

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
}

pub mod intern {
    use super::*;
    use interner::InternedStr;
    use thread::ThreadInternal;

    use serde::{Deserialize, Deserializer};
    use serde::de::{DeserializeSeed, SeqSeed};

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
