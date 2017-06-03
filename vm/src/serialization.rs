use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;

use serde::Deserializer;
use serde::de::{DeserializeSeed, SeqSeed, Error};

use base::fnv::FnvMap;
use base::symbol::{Symbol, Symbols};
use gc::{DataDef, GcPtr, Traverseable, WriteOnly};
use thread::{RootedThread, Status, Thread, ThreadInternal};
use types::VmIndex;
use value::{BytecodeFunction, ClosureData, ClosureDataDef, ExternFunction, Value};

#[derive(Clone)]
pub struct DeSeed {
    thread: RootedThread,
    symbols: Rc<RefCell<Symbols>>,
    extern_functions: Rc<FnvMap<Symbol, extern "C" fn(&Thread) -> Status>>,
}

impl DeSeed {
    pub fn new(thread: RootedThread) -> DeSeed {
        DeSeed {
            thread: thread,
            symbols: Default::default(),
            extern_functions: Default::default(),
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

pub mod typ {
    use serde::de::{Deserialize, Deserializer, Error};
    use serde::ser::{Serialize, Serializer};

    use super::*;
    use base::types::ArcType;

    pub fn deserialize<'de, D, T>(seed: &mut Seed<T>, deserializer: D) -> Result<ArcType, D::Error>
        where D: Deserializer<'de>
    {
        let expr_str = String::deserialize(deserializer)?;
        let expr = ::parser::parse_expr(&mut *seed.state.symbols.borrow_mut(), &expr_str)
            .map_err(D::Error::custom)?;
        match expr.value {
            ::base::ast::Expr::TypeBindings(ref bindings, _) => {
                Ok(bindings[0].alias.unresolved_type().clone())
            }
            _ => Err(D::Error::custom("Invalid type")),
        }
    }

    pub fn serialize<S>(typ: &ArcType, serializer: S, _seed: &SeSeed) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        format!("type __T = {} in 0", typ).serialize(serializer)
    }
}

#[derive(DeserializeSeed)]
#[serde(deserialize_seed = "Seed<ClosureDataModel>")]
struct ClosureDataModel {
    #[serde(deserialize_seed_with = "deserialize")]
    function: GcPtr<BytecodeFunction>,
    #[serde(deserialize_seed_with = "deserialize")]
    upvars: Vec<Value>,
}

gc_serialize!{ ClosureDataModel }

unsafe impl DataDef for ClosureDataModel {
    type Value = ClosureData;

    fn size(&self) -> usize {
        ClosureDataDef(self.function, &self.upvars).size()
    }

    fn initialize<'w>(self, result: WriteOnly<'w, Self::Value>) -> &'w mut Self::Value {
        ClosureDataDef(self.function, &self.upvars).initialize(result)
    }
}

pub fn deserialize_closure<'de, T, D>(seed: &mut Seed<T>,
                                      deserializer: D)
                                      -> Result<GcPtr<ClosureData>, D::Error>
    where D: Deserializer<'de>
{
    DeserializeSeed::deserialize(Seed::<DataDefSeed<ClosureDataModel>>::from(seed.state.clone()),
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
        let def = DeserializeSeed::deserialize(T::Seed::from(self.state.clone()), deserializer)?;
        self.state
            .thread
            .context()
            .gc
            .alloc(def)
            .map_err(D::Error::custom)
    }
}

gc_serialize!{ ExternFunction }

impl<'de> DeserializeSeed<'de> for Seed<ExternFunction> {
    type Value = ExternFunction;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
        where D: Deserializer<'de>
    {
        #[derive(DeserializeSeed)]
        #[serde(deserialize_seed = "Seed<ExternFunction_>")]
        struct ExternFunction_ {
            #[serde(deserialize_seed_with = "deserialize")]
            id: Symbol,
            args: VmIndex,
        }
        let partial = Seed::<ExternFunction_>::from(self.state.clone())
            .deserialize(deserializer)?;
        let function = self.state
            .extern_functions
            .get(&partial.id)
            .ok_or_else(|| {
                            D::Error::custom(format!("Extern function `{}` is not defined",
                                                     partial.id))
                        })?;
        Ok(ExternFunction {
               id: partial.id,
               args: partial.args,
               function: *function,
           })
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
