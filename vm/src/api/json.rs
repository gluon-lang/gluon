extern crate serde_json;

use std::borrow::Borrow;
use std::fmt;
use std::result::Result as StdResult;

use crate::base::types::{ArcType, Type};

use crate::api::{Getable, OpaqueValue, VmType};
use crate::thread::{ActiveThread, RootedThread, Thread, ThreadInternal};
use crate::{ExternModule, Result, Variants};

use crate::serde::de::{self, DeserializeState, MapAccess, SeqAccess, Visitor};

pub fn load(vm: &Thread) -> Result<ExternModule> {
    fn deserialize(value: crate::api::WithVM<&str>) -> StdResult<JsonValue, String> {
        let crate::api::WithVM { vm, value: input } = value;
        let mut context = vm.current_context();
        JsonValue::deserialize_state(&mut context, &mut serde_json::Deserializer::from_str(input))
            .map_err(|err| err.to_string())
    }

    fn serialize<F>(value: crate::api::WithVM<Value>, formatter: F) -> StdResult<String, String>
    where
        F: serde_json::ser::Formatter,
    {
        let crate::api::WithVM { vm, value: input } = value;

        let mut output = Vec::new();
        SerializeState::serialize_state(
            &input,
            &mut serde_json::Serializer::with_formatter(&mut output, formatter),
            vm,
        )
        .map_err(|err| err.to_string())?;

        // serde_json outputs valid UTF-8
        unsafe { Ok(String::from_utf8_unchecked(output)) }
    }

    ExternModule::new(
        vm,
        record! {
            deserialize => primitive!(
                1,
                "std.json.prim.deserialize",
                deserialize
            ),
            serialize => primitive!(
                1,
                "std.json.prim.serialize",
                |v| serialize(v, serde_json::ser::CompactFormatter)
            ),
            serialize_pretty => primitive!(
                1,
                "std.json.prim.serialize_pretty",
                |v| serialize(v, serde_json::ser::PrettyFormatter::new())
            ),
        },
    )
}

#[derive(Pushable, Getable, SerializeState)]
#[serde(serialize_state = "Thread")]
#[gluon(gluon_vm)]
#[serde(untagged)]
pub enum Value {
    Null,
    Bool(bool),
    Int(i64),
    Float(f64),
    String(#[serde(state)] JsonString),
    Array(#[serde(state)] Vec<JsonValue>),
    Object(#[serde(state)] ::std::collections::BTreeMap<JsonString, JsonValue>),
}

#[derive(SerializeState, Ord, Eq, PartialEq, PartialOrd, Getable, Pushable)]
#[serde(serialize_state = "Thread")]
#[gluon(gluon_vm)]
pub struct JsonString(OpaqueValue<RootedThread, str>);

impl VmType for JsonString {
    type Type = String;
}

impl ::std::ops::Deref for JsonString {
    type Target = str;

    fn deref(&self) -> &str {
        &self.0
    }
}

impl Borrow<str> for JsonString {
    fn borrow(&self) -> &str {
        self
    }
}

impl<'de> de::DeserializeState<'de, ActiveThread<'de>> for JsonString {
    fn deserialize_state<D>(
        thread: &mut ActiveThread<'de>,
        deserializer: D,
    ) -> StdResult<Self, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        struct StringVisitor<'a, 'vm: 'a>(&'a mut ActiveThread<'vm>);

        impl<'a, 'de> Visitor<'de> for StringVisitor<'a, 'de> {
            type Value = JsonString;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a string")
            }

            #[inline]
            fn visit_str<E>(self, value: &str) -> StdResult<Self::Value, E>
            where
                E: de::Error,
            {
                crate::api::convert_with_active_thread(self.0, value).map_err(E::custom)
            }
        }

        deserializer.deserialize_string(StringVisitor(thread))
    }
}

impl VmType for Value {
    type Type = Self;
    fn make_type(vm: &Thread) -> ArcType {
        JsonValue::make_type(vm)
    }
}

pub struct JsonValue(crate::vm::RootedValue<RootedThread>);

impl VmType for JsonValue {
    type Type = <Value as VmType>::Type;
    fn make_type(vm: &Thread) -> ArcType {
        vm.find_type_info("std.json.value.Value")
            .map(|t| t.clone().into_type())
            .ok()
            .unwrap_or_else(Type::error)
    }
}

impl<'vm> crate::api::Pushable<'vm> for JsonValue {
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        crate::api::Pushable::push(self.0, context)
    }
}

impl<'vm, 'value> crate::api::Getable<'vm, 'value> for JsonValue {
    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Self {
        JsonValue(crate::api::Getable::from_value(vm, value))
    }
}

use crate::serde::ser::{SerializeState, Serializer};
impl SerializeState<Thread> for JsonValue {
    fn serialize_state<S>(&self, serializer: S, vm: &Thread) -> StdResult<S::Ok, S::Error>
    where
        S: Serializer,
    {
        Value::from_value(vm, self.0.get_variant()).serialize_state(serializer, vm)
    }
}

impl<'de> de::DeserializeState<'de, ActiveThread<'de>> for JsonValue {
    fn deserialize_state<D>(
        thread: &mut ActiveThread<'de>,
        deserializer: D,
    ) -> StdResult<Self, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        struct ValueVisitor<'a, 'vm: 'a>(&'a mut ActiveThread<'vm>);

        impl<'a, 'vm> ValueVisitor<'a, 'vm> {
            fn marshal<T>(&mut self, value: T) -> JsonValue
            where
                T: crate::api::Pushable<'vm>,
            {
                let context = &mut *self.0;
                value.push(context).unwrap_or_else(|err| panic!("{}", err));
                let thread = context.thread();
                let value = context.pop();
                JsonValue(thread.root_value(*value))
            }
        }

        impl<'a, 'de> Visitor<'de> for ValueVisitor<'a, 'de> {
            type Value = JsonValue;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("any valid JSON value")
            }

            #[inline]
            fn visit_bool<E>(mut self, value: bool) -> StdResult<Self::Value, E> {
                Ok(self.marshal(Value::Bool(value)))
            }

            #[inline]
            fn visit_i64<E>(mut self, value: i64) -> StdResult<Self::Value, E> {
                Ok(self.marshal(Value::Int(value.into())))
            }

            #[inline]
            fn visit_u64<E>(mut self, value: u64) -> StdResult<Self::Value, E> {
                Ok(self.marshal(Value::Int(value as i64)))
            }

            #[inline]
            fn visit_f64<E>(mut self, value: f64) -> StdResult<Self::Value, E> {
                Ok(self.marshal(Value::Float(value)))
            }

            #[inline]
            fn visit_str<E>(mut self, value: &str) -> StdResult<Self::Value, E>
            where
                E: de::Error,
            {
                let value = crate::api::convert_with_active_thread(self.0, value).map_err(E::custom)?;
                Ok(self.marshal(Value::String(value)))
            }

            #[inline]
            fn visit_string<E>(mut self, value: String) -> StdResult<Self::Value, E>
            where
                E: de::Error,
            {
                let value = crate::api::convert_with_active_thread(self.0, value).map_err(E::custom)?;
                Ok(self.marshal(Value::String(value)))
            }

            #[inline]
            fn visit_none<E>(mut self) -> StdResult<Self::Value, E> {
                Ok(self.marshal(Value::Null))
            }

            #[inline]
            fn visit_some<D>(self, deserializer: D) -> StdResult<Self::Value, D::Error>
            where
                D: de::Deserializer<'de>,
            {
                de::DeserializeState::deserialize_state(&mut *self.0, deserializer)
            }

            #[inline]
            fn visit_unit<E>(mut self) -> StdResult<Self::Value, E> {
                Ok(self.marshal(Value::Null))
            }

            #[inline]
            fn visit_seq<V>(mut self, mut visitor: V) -> StdResult<Self::Value, V::Error>
            where
                V: SeqAccess<'de>,
            {
                let mut vec = Vec::new();

                while let Some(elem) = visitor.next_element_seed(de::Seed::new(&mut *self.0))? {
                    vec.push(elem);
                }

                Ok(self.marshal(Value::Array(vec)))
            }

            fn visit_map<V>(mut self, mut visitor: V) -> StdResult<Self::Value, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut values = ::std::collections::BTreeMap::new();

                while let Some(key) = visitor.next_key_seed(de::Seed::new(&mut *self.0))? {
                    let value = visitor.next_value_seed(de::Seed::new(&mut *self.0))?;
                    values.insert(key, value);
                }

                Ok(self.marshal(Value::Object(values)))
            }
        }

        deserializer.deserialize_any(ValueVisitor(thread))
    }
}
