//! Rust -> Gluon value conversion via the `serde::Serialize` trait
//!
//! _This module requires Gluon to be built with the `serde` feature._

use std::{
    fmt,
    ops::{Deref, DerefMut},
};

use crate::{
    api::{Pushable, VmType},
    base::types::ArcType,
    interner::InternedStr,
    serde::ser::{self, Serialize},
    thread::{ActiveThread, Thread},
    types::{VmIndex, VmTag},
    value::{Def, RecordDef, ValueRepr},
    Error, Result, Variants,
};

/**
`Pushable` wrapper which pushes `T` by serializing it.

## Struct

```
use serde::Serialize;

use gluon_vm::{field_decl, record_type};

use gluon::{
    Thread, ThreadExt, new_vm_async,
    base::types::ArcType,
    vm::api::{ser::Ser, FunctionRef, VmType},
};

# #[tokio::main]
# async fn main() {

#[derive(Serialize)]
struct Vec2 {
    x: i32,
    y: i32,
}

impl VmType for Vec2 {
    type Type = Self;

    fn make_type(thread: &Thread) -> ArcType {
        field_decl!{ x, y }
        type T = record_type! {
            x => i32,
            y => i32
        };
        T::make_type(thread)
    }
}

# if ::std::env::var("GLUON_PATH").is_err() {
#     ::std::env::set_var("GLUON_PATH", "..");
# }

let thread = new_vm_async().await;

let (mut f, _): (FunctionRef<fn (Ser<Vec2>) -> i32>, _) = thread
    .run_expr_async("", r#"let f v: _ -> Int = v.x + v.y in f"#)
    .await
    .unwrap_or_else(|err| panic!("{}", err));
let vec = Vec2 {
    x: 3,
    y: 10
};
let result = f.call_async(Ser(vec)).await.unwrap_or_else(|err| panic!("{}", err));
assert_eq!(result, 13);
# }

```

## Enum

```
#[macro_use]
extern crate serde_derive;

#[macro_use]
extern crate gluon_vm;

use gluon::{Thread, ThreadExt, new_vm};
use gluon::base::types::ArcType;
use gluon::vm::api::{FunctionRef, VmType};
use gluon::vm::api::ser::Ser;
# fn main() {


#[derive(Serialize)]
enum Enum {
    A(i32),
    B(String, i32),
    C { foo: f64, bar: i32 },
}

impl VmType for Enum {
    type Type = Self;

    fn make_type(thread: &Thread) -> ArcType {
        // Use the enum type declared in gluon
        thread.find_type_info("test.Enum").unwrap().into_type()
    }
}

# if ::std::env::var("GLUON_PATH").is_err() {
#     ::std::env::set_var("GLUON_PATH", "..");
# }

let thread = new_vm();
# thread.get_database_mut().implicit_prelude(false);

let expr = r#"
type Enum = | A Int | B String Int | C { foo : Float, bar : Int }

let extract_bar r : { bar : Int | r } -> Int = r.bar

let f e =
    match e with
    | A a -> a
    | B b c -> c
    | C c -> extract_bar c

{ Enum, f }
"#;
thread
    .load_script("test", expr)
    .unwrap_or_else(|err| panic!("{}", err));

let mut f: FunctionRef<fn (Ser<Enum>) -> i32> = thread
    .get_global("test.f")
    .unwrap_or_else(|err| panic!("{}", err));

let result1 = f.call(Ser(Enum::B("".to_string(), 4)))
    .unwrap_or_else(|err| panic!("{}", err));
assert_eq!(result1, 4);

let result2 = f.call(Ser(Enum::C { foo: 3.14, bar: 10 }))
    .unwrap_or_else(|err| panic!("{}", err));
assert_eq!(result2, 10);

# }
```
*/
pub struct Ser<T>(pub T);

impl<T> VmType for Ser<T>
where
    T: VmType,
{
    type Type = T::Type;

    fn make_type(thread: &Thread) -> ArcType {
        T::make_type(thread)
    }
}

impl<'vm, T> Pushable<'vm> for Ser<T>
where
    T: Serialize,
{
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let mut serializer = Serializer::new(context);
        self.0.serialize(&mut serializer)
    }
}

impl ser::Error for Error {
    fn custom<T>(msg: T) -> Self
    where
        T: fmt::Display,
    {
        Error::Message(format!("{}", msg))
    }
}

pub struct Serializer<'a, 't: 'a> {
    thread: &'t Thread,
    context: &'a mut ActiveThread<'t>,
}

impl<'a, 't> Serializer<'a, 't> {
    pub fn new(context: &'a mut ActiveThread<'t>) -> Self {
        Serializer {
            thread: context.thread(),
            context,
        }
    }

    fn to_value<T>(&mut self, value: T) -> Result<()>
    where
        T: Pushable<'t>,
    {
        value.vm_push(self.context)
    }

    fn alloc(&mut self, tag: VmTag, values: VmIndex) -> Result<()> {
        let mut context = self.context.context();
        let value = context.gc.alloc(Def {
            tag: tag,
            elems: &context.stack[context.stack.len() - values..],
        })?;
        context.stack.pop_many(values);
        context.stack.push(Variants::from(value));
        Ok(())
    }

    fn alloc_record(&mut self, fields: &[InternedStr], values: VmIndex) -> Result<()> {
        let mut context = self.context.context();
        let value = context.gc.alloc(RecordDef {
            elems: &context.stack[context.stack.len() - values..],
            fields,
        })?;
        context.stack.pop_many(values);
        context.stack.push(Variants::from(value));
        Ok(())
    }
}

#[doc(hidden)]
pub struct RecordSerializer<'s, 'a: 's, 'vm: 'a> {
    serializer: &'s mut Serializer<'a, 'vm>,
    variant_index: VmTag,
    values: VmIndex,
    fields: Vec<InternedStr>,
}

impl<'s, 'a, 'vm> Deref for RecordSerializer<'s, 'a, 'vm> {
    type Target = Serializer<'a, 'vm>;
    fn deref(&self) -> &Self::Target {
        self.serializer
    }
}

impl<'s, 'a, 'vm> DerefMut for RecordSerializer<'s, 'a, 'vm> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.serializer
    }
}

impl<'s, 'a, 'vm> RecordSerializer<'s, 'a, 'vm> {
    fn new(serializer: &'s mut Serializer<'a, 'vm>, variant_index: u32) -> Self {
        RecordSerializer {
            serializer: serializer,
            variant_index: variant_index,
            values: 0,
            fields: Vec::new(),
        }
    }
}

impl<'s, 'a, 'vm> ser::Serializer for &'s mut Serializer<'a, 'vm> {
    type Ok = ();

    // The error type when some error occurs during serialization.
    type Error = Error;

    // Associated types for keeping track of additional state while serializing
    // compound data structures like sequences and maps. In this case no
    // additional state is required beyond what is already stored in the
    // Serializer struct.
    type SerializeSeq = RecordSerializer<'s, 'a, 'vm>;
    type SerializeTuple = RecordSerializer<'s, 'a, 'vm>;
    type SerializeTupleStruct = RecordSerializer<'s, 'a, 'vm>;
    type SerializeTupleVariant = RecordSerializer<'s, 'a, 'vm>;
    type SerializeMap = RecordSerializer<'s, 'a, 'vm>;
    type SerializeStruct = RecordSerializer<'s, 'a, 'vm>;
    type SerializeStructVariant = RecordSerializer<'s, 'a, 'vm>;

    // Here we go with the simple methods. The following 12 methods receive one
    // of the primitive types of the data model and map it to JSON by appending
    // into the output string.
    fn serialize_bool(self, v: bool) -> Result<Self::Ok> {
        self.to_value(v)
    }

    // JSON does not distinguish between different sizes of integers, so all
    // signed integers will be serialized the same and all unsigned integers
    // will be serialized the same. Other formats, especially compact binary
    // formats, may need independent logic for the different sizes.
    fn serialize_i8(self, v: i8) -> Result<Self::Ok> {
        self.serialize_i64(v as i64)
    }

    fn serialize_i16(self, v: i16) -> Result<Self::Ok> {
        self.serialize_i64(v as i64)
    }

    fn serialize_i32(self, v: i32) -> Result<Self::Ok> {
        self.serialize_i64(v as i64)
    }

    // Not particularly efficient but this is example code anyway. A more
    // performant approach would be to use the `itoa` crate.
    fn serialize_i64(self, v: i64) -> Result<Self::Ok> {
        self.to_value(v as isize)
    }

    fn serialize_u8(self, v: u8) -> Result<Self::Ok> {
        self.serialize_u64(v as u64)
    }

    fn serialize_u16(self, v: u16) -> Result<Self::Ok> {
        self.serialize_u64(v as u64)
    }

    fn serialize_u32(self, v: u32) -> Result<Self::Ok> {
        self.serialize_u64(v as u64)
    }

    fn serialize_u64(self, v: u64) -> Result<Self::Ok> {
        self.to_value(v as isize)
    }

    fn serialize_f32(self, v: f32) -> Result<Self::Ok> {
        self.serialize_f64(v as f64)
    }

    fn serialize_f64(self, v: f64) -> Result<Self::Ok> {
        self.to_value(v)
    }

    fn serialize_char(self, v: char) -> Result<Self::Ok> {
        self.serialize_str(&v.to_string())
    }

    fn serialize_str(self, v: &str) -> Result<Self::Ok> {
        self.to_value(v)
    }

    fn serialize_bytes(self, v: &[u8]) -> Result<Self::Ok> {
        self.to_value(v)
    }

    // An absent optional is represented as the JSON `null`.
    fn serialize_none(self) -> Result<Self::Ok> {
        self.serialize_unit()
    }

    // A present optional is represented as just the contained value. Note that
    // this is a lossy representation. For example the values `Some(())` and
    // `None` both serialize as just `null`. Unfortunately this is typically
    // what people expect when working with JSON. Other formats are encouraged
    // to behave more intelligently if possible.
    fn serialize_some<T>(self, value: &T) -> Result<Self::Ok>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    fn serialize_unit(self) -> Result<Self::Ok> {
        self.context.push(ValueRepr::Tag(0));
        Ok(())
    }

    fn serialize_unit_struct(self, _name: &'static str) -> Result<Self::Ok> {
        self.serialize_unit()
    }

    fn serialize_unit_variant(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
    ) -> Result<Self::Ok> {
        self.context.push(ValueRepr::Tag(variant_index));
        Ok(())
    }

    // As is done here, serializers are encouraged to treat newtype structs as
    // insignificant wrappers around the data they contain.
    fn serialize_newtype_struct<T>(self, _name: &'static str, value: &T) -> Result<Self::Ok>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(self)
    }

    // Note that newtype variant (and all of the other variant serialization
    // methods) refer exclusively to the "externally tagged" enum
    // representation.
    //
    // Serialize this to JSON in externally tagged form as `{ NAME: VALUE }`.
    fn serialize_newtype_variant<T>(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        value: &T,
    ) -> Result<Self::Ok>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(&mut *self)?;
        self.alloc(variant_index, 1)
    }

    fn serialize_seq(self, _len: Option<usize>) -> Result<Self::SerializeSeq> {
        Ok(RecordSerializer::new(self, 0))
    }

    fn serialize_tuple(self, len: usize) -> Result<Self::SerializeTuple> {
        self.serialize_seq(Some(len))
    }

    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        len: usize,
    ) -> Result<Self::SerializeTupleStruct> {
        self.serialize_seq(Some(len))
    }

    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeTupleVariant> {
        Ok(RecordSerializer::new(self, variant_index))
    }

    fn serialize_map(self, _len: Option<usize>) -> Result<Self::SerializeMap> {
        Ok(RecordSerializer::new(self, 0))
    }

    fn serialize_struct(self, _name: &'static str, len: usize) -> Result<Self::SerializeStruct> {
        self.serialize_map(Some(len))
    }

    fn serialize_struct_variant(
        self,
        _name: &'static str,
        variant_index: u32,
        _variant: &'static str,
        _len: usize,
    ) -> Result<Self::SerializeStructVariant> {
        Ok(RecordSerializer::new(self, variant_index))
    }
}

impl<'s, 'a, 'vm> ser::SerializeSeq for RecordSerializer<'s, 'a, 'vm> {
    type Ok = ();
    type Error = Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(&mut **self)?;
        self.values += 1;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok> {
        self.serializer.alloc(self.variant_index, self.values)
    }
}

impl<'s, 'a, 'vm> ser::SerializeTuple for RecordSerializer<'s, 'a, 'vm> {
    type Ok = ();
    type Error = Error;

    fn serialize_element<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(&mut **self)?;
        self.values += 1;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok> {
        self.serializer.alloc(self.variant_index, self.values)
    }
}

impl<'s, 'a, 'vm> ser::SerializeTupleStruct for RecordSerializer<'s, 'a, 'vm> {
    type Ok = ();
    type Error = Error;

    fn serialize_field<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(&mut **self)?;
        self.values += 1;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok> {
        self.serializer.alloc(self.variant_index, self.values)
    }
}

impl<'s, 'a, 'vm> ser::SerializeTupleVariant for RecordSerializer<'s, 'a, 'vm> {
    type Ok = ();
    type Error = Error;

    fn serialize_field<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(&mut **self)?;
        self.values += 1;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok> {
        self.serializer.alloc(self.variant_index, self.values)
    }
}

impl<'s, 'a, 'vm> ser::SerializeMap for RecordSerializer<'s, 'a, 'vm> {
    type Ok = ();
    type Error = Error;

    fn serialize_key<T>(&mut self, _key: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        Ok(())
    }

    fn serialize_value<T>(&mut self, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        value.serialize(&mut **self)?;
        self.values += 1;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok> {
        self.serializer.alloc(self.variant_index, self.values)
    }
}

impl<'s, 'a, 'vm> ser::SerializeStruct for RecordSerializer<'s, 'a, 'vm> {
    type Ok = ();
    type Error = Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        let field = self.thread.global_env().intern(key)?;
        self.fields.push(field);
        value.serialize(&mut **self)?;
        self.values += 1;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok> {
        self.serializer.alloc_record(&self.fields, self.values)
    }
}

// Similar to `SerializeTupleVariant`, here the `end` method is responsible for
// closing both of the curly braces opened by `serialize_struct_variant`.
impl<'s, 'a, 'vm> ser::SerializeStructVariant for RecordSerializer<'s, 'a, 'vm> {
    type Ok = ();
    type Error = Error;

    fn serialize_field<T>(&mut self, key: &'static str, value: &T) -> Result<()>
    where
        T: ?Sized + Serialize,
    {
        let field = self.thread.global_env().intern(key)?;
        self.fields.push(field);
        value.serialize(&mut **self)?;
        self.values += 1;
        Ok(())
    }

    fn end(self) -> Result<Self::Ok> {
        self.serializer.alloc_record(&self.fields, self.values)?;
        self.serializer.alloc(self.variant_index, 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{thread::RootedThread, value::Value};

    #[test]
    fn bool() {
        let thread = RootedThread::new();
        assert_eq!(
            true.marshal::<&Thread>(&thread).unwrap().get_value(),
            &Value::tag(1)
        );
    }
}
