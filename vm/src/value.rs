use std::fmt;
use std::any::Any;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::result::Result as StdResult;

use base::symbol::Symbol;
use types::*;
use interner::InternedStr;
use gc::{Gc, GcPtr, Traverseable, DataDef, WriteOnly};
use array::{Array, Str};
use thread::{Thread, Status};
use {Error, Result};

use self::Value::{Int, Float, String, Function, PartialApplication, Closure};

mopafy!(Userdata);
pub trait Userdata: ::mopa::Any + Traverseable + Send + Sync {}

impl PartialEq for Userdata {
    fn eq(&self, other: &Userdata) -> bool {
        self as *const _ == other as *const _
    }
}

impl<T> Userdata for T where T: Any + Traverseable + Send + Sync {}

impl fmt::Debug for Userdata {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Userdata")
    }
}

#[derive(Debug)]
pub struct ClosureData {
    pub function: GcPtr<BytecodeFunction>,
    pub upvars: Array<Value>,
}

impl PartialEq for ClosureData {
    fn eq(&self, _: &ClosureData) -> bool {
        false
    }
}

impl Traverseable for ClosureData {
    fn traverse(&self, gc: &mut Gc) {
        self.function.traverse(gc);
        self.upvars.traverse(gc);
    }
}

pub struct ClosureDataDef<'b>(pub GcPtr<BytecodeFunction>, pub &'b [Value]);
impl<'b> Traverseable for ClosureDataDef<'b> {
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc);
        self.1.traverse(gc);
    }
}

unsafe impl<'b> DataDef for ClosureDataDef<'b> {
    type Value = ClosureData;
    fn size(&self) -> usize {
        use std::mem::size_of;
        size_of::<GcPtr<BytecodeFunction>>() + Array::<Value>::size_of(self.1.len())
    }
    fn initialize<'w>(self, mut result: WriteOnly<'w, ClosureData>) -> &'w mut ClosureData {
        unsafe {
            let result = &mut *result.as_mut_ptr();
            result.function = self.0;
            result.upvars.initialize(self.1.iter().cloned());
            result
        }
    }
}

pub struct ClosureInitDef(pub GcPtr<BytecodeFunction>, pub usize);

impl Traverseable for ClosureInitDef {
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc);
    }
}

unsafe impl DataDef for ClosureInitDef {
    type Value = ClosureData;
    fn size(&self) -> usize {
        use std::mem::size_of;
        size_of::<GcPtr<BytecodeFunction>>() + Array::<Value>::size_of(self.1)
    }
    fn initialize<'w>(self, mut result: WriteOnly<'w, ClosureData>) -> &'w mut ClosureData {
        use std::ptr;
        unsafe {
            let result = &mut *result.as_mut_ptr();
            result.function = self.0;
            result.upvars.set_len(self.1);
            for var in &mut result.upvars {
                ptr::write(var, Int(0));
            }
            result
        }
    }
}


#[derive(Debug)]
pub struct BytecodeFunction {
    pub name: Symbol,
    pub args: VMIndex,
    pub instructions: Vec<Instruction>,
    pub inner_functions: Vec<GcPtr<BytecodeFunction>>,
    pub strings: Vec<InternedStr>,
    pub globals: Vec<Value>,
}

impl Traverseable for BytecodeFunction {
    fn traverse(&self, gc: &mut Gc) {
        self.inner_functions.traverse(gc);
        self.globals.traverse(gc);
    }
}

pub struct DataStruct {
    pub tag: VMTag,
    pub fields: Array<Value>,
}

impl Traverseable for DataStruct {
    fn traverse(&self, gc: &mut Gc) {
        self.fields.traverse(gc);
    }
}

impl PartialEq for DataStruct {
    fn eq(&self, other: &DataStruct) -> bool {
        self.tag == other.tag && self.fields == other.fields
    }
}

/// Definition for data values in the VM
pub struct Def<'b> {
    pub tag: VMTag,
    pub elems: &'b [Value],
}
unsafe impl<'b> DataDef for Def<'b> {
    type Value = DataStruct;
    fn size(&self) -> usize {
        use std::mem::size_of;
        size_of::<usize>() + Array::<Value>::size_of(self.elems.len())
    }
    fn initialize<'w>(self, mut result: WriteOnly<'w, DataStruct>) -> &'w mut DataStruct {
        unsafe {
            let result = &mut *result.as_mut_ptr();
            result.tag = self.tag;
            result.fields.initialize(self.elems.iter().cloned());
            result
        }
    }
}

impl<'b> Traverseable for Def<'b> {
    fn traverse(&self, gc: &mut Gc) {
        self.elems.traverse(gc);
    }
}

#[derive(Copy, Clone, PartialEq)]
pub enum Value {
    Int(VMInt),
    Float(f64),
    String(GcPtr<Str>),
    Data(GcPtr<DataStruct>),
    Array(GcPtr<ValueArray>),
    Function(GcPtr<ExternFunction>),
    Closure(GcPtr<ClosureData>),
    PartialApplication(GcPtr<PartialApplicationData>),
    Userdata(GcPtr<Box<Userdata>>),
    Thread(GcPtr<Thread>),
}

impl Value {
    pub fn generation(self) -> usize {
        match self {
            String(p) => p.generation(),
            Value::Data(p) => p.generation(),
            Function(p) => p.generation(),
            Closure(p) => p.generation(),
            Value::Array(p) => p.generation(),
            PartialApplication(p) => p.generation(),
            Value::Userdata(p) => p.generation(),
            Value::Thread(p) => p.generation(),
            Int(_) | Float(_) => 0,
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Callable {
    Closure(GcPtr<ClosureData>),
    Extern(GcPtr<ExternFunction>),
}

impl Callable {
    pub fn name(&self) -> &Symbol {
        match *self {
            Callable::Closure(ref closure) => &closure.function.name,
            Callable::Extern(ref ext) => &ext.id,
        }
    }

    pub fn args(&self) -> VMIndex {
        match *self {
            Callable::Closure(ref closure) => closure.function.args,
            Callable::Extern(ref ext) => ext.args,
        }
    }
}

impl PartialEq for Callable {
    fn eq(&self, _: &Callable) -> bool {
        false
    }
}

impl Traverseable for Callable {
    fn traverse(&self, gc: &mut Gc) {
        match *self {
            Callable::Closure(ref closure) => closure.traverse(gc),
            Callable::Extern(_) => (),
        }
    }
}

#[derive(Debug)]
pub struct PartialApplicationData {
    pub function: Callable,
    pub arguments: Array<Value>,
}

impl PartialEq for PartialApplicationData {
    fn eq(&self, _: &PartialApplicationData) -> bool {
        false
    }
}

impl Traverseable for PartialApplicationData {
    fn traverse(&self, gc: &mut Gc) {
        self.function.traverse(gc);
        self.arguments.traverse(gc);
    }
}

pub struct PartialApplicationDataDef<'b>(pub Callable, pub &'b [Value]);
impl<'b> Traverseable for PartialApplicationDataDef<'b> {
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc);
        self.1.traverse(gc);
    }
}
unsafe impl<'b> DataDef for PartialApplicationDataDef<'b> {
    type Value = PartialApplicationData;
    fn size(&self) -> usize {
        use std::mem::size_of;
        size_of::<Callable>() + Array::<Value>::size_of(self.1.len())
    }
    fn initialize<'w>(self,
                      mut result: WriteOnly<'w, PartialApplicationData>)
                      -> &'w mut PartialApplicationData {
        unsafe {
            let result = &mut *result.as_mut_ptr();
            result.function = self.0;
            result.arguments.initialize(self.1.iter().cloned());
            result
        }
    }
}

impl Traverseable for Value {
    fn traverse(&self, gc: &mut Gc) {
        match *self {
            String(ref data) => data.traverse(gc),
            Value::Data(ref data) => data.traverse(gc),
            Value::Array(ref data) => data.traverse(gc),
            Function(ref data) => data.traverse(gc),
            Closure(ref data) => data.traverse(gc),
            Value::Userdata(ref data) => data.traverse(gc),
            PartialApplication(ref data) => data.traverse(gc),
            Value::Thread(ref thread) => thread.traverse(gc),
            Int(_) | Float(_) => (),
        }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        struct Level<'b>(i32, &'b Value);
        struct LevelSlice<'b>(i32, &'b [Value]);
        impl<'b> fmt::Debug for LevelSlice<'b> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let level = self.0;
                if level <= 0 || self.1.is_empty() {
                    return Ok(());
                }
                try!(write!(f, "{:?}", Level(level - 1, &self.1[0])));
                for v in &self.1[1..] {
                    try!(write!(f, ", {:?}", Level(level - 1, v)));
                }
                Ok(())
            }
        }
        impl<'b> fmt::Debug for Level<'b> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let level = self.0;
                if level <= 0 {
                    return Ok(());
                }
                match *self.1 {
                    Int(i) => write!(f, "{:?}", i),
                    Float(x) => write!(f, "{:?}f", x),
                    String(x) => write!(f, "{:?}", &*x),
                    Value::Data(ref data) => {
                        write!(f,
                               "{{{:?}: {:?}}}",
                               data.tag,
                               LevelSlice(level - 1, &data.fields))
                    }
                    Value::Array(ref array) => {
                        let mut first = true;
                        try!(write!(f, "["));
                        for value in array.iter() {
                            if !first {
                                try!(write!(f, ", "));
                            }
                            first = false;
                            try!(write!(f, "{:?}", Level(level - 1, &value)));
                        }
                        write!(f, "]")
                    }
                    Function(ref func) => write!(f, "<EXTERN {:?}>", &**func),
                    Closure(ref closure) => {
                        let p: *const _ = &*closure.function;
                        write!(f, "<{:?} {:?}>", closure.function.name, p)
                    }
                    PartialApplication(ref app) => {
                        let name = match app.function {
                            Callable::Closure(_) => "<CLOSURE>",
                            Callable::Extern(_) => "<EXTERN>",
                        };
                        write!(f,
                               "<App {:?}{:?}>",
                               name,
                               LevelSlice(level - 1, &app.arguments))
                    }
                    Value::Userdata(ref data) => write!(f, "<Userdata {:p}>", &**data),
                    Value::Thread(_) => write!(f, "<thread>"),
                }
            }
        }
        write!(f, "{:?}", Level(3, self))
    }
}

pub struct ExternFunction {
    pub id: Symbol,
    pub args: VMIndex,
    pub function: Box<Fn(&Thread) -> Status + Send + Sync>,
}

impl PartialEq for ExternFunction {
    fn eq(&self, _: &ExternFunction) -> bool {
        false
    }
}

impl fmt::Debug for ExternFunction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // read the v-table pointer of the Fn(..) type and print that
        let p: *const () = unsafe { ::std::mem::transmute_copy(&&*self.function) };
        write!(f, "{:?}", p)
    }
}

impl Traverseable for ExternFunction {
    fn traverse(&self, _: &mut Gc) {}
}


#[derive(Copy, Clone, PartialEq, Debug)]
pub enum ValueType {
    Int,
    Float,
    String,
    Data,
    Array,
    Function,
    Closure,
    PartialApplication,
    Userdata,
    Thread,
}

macro_rules! on_array {
    ($array: expr, $f: expr) => {
        {
            let ref array = $array;
            unsafe {
                match array.typ {
                    ValueType::Int => $f(array.unsafe_array::<VMInt>()),
                    ValueType::Float => $f(array.unsafe_array::<f64>()),
                    ValueType::String => $f(array.unsafe_array::<GcPtr<Str>>()),
                    ValueType::Data => $f(array.unsafe_array::<GcPtr<DataStruct>>()),
                    ValueType::Array => $f(array.unsafe_array::<GcPtr<ValueArray>>()),
                    ValueType::Function => $f(array.unsafe_array::<GcPtr<ExternFunction>>()),
                    ValueType::Closure => $f(array.unsafe_array::<GcPtr<ClosureData>>()),
                    ValueType::PartialApplication => {
                        $f(array.unsafe_array::<GcPtr<PartialApplicationData>>())
                    }
                    ValueType::Userdata => $f(array.unsafe_array::<GcPtr<Box<Userdata>>>()),
                    ValueType::Thread => $f(array.unsafe_array::<GcPtr<Thread>>()),
                }
            }
        }
    }
}


#[derive(Debug)]
pub struct ValueArray {
    pub typ: ValueType,
    array: Array<()>,
}

impl PartialEq for ValueArray {
    fn eq(&self, other: &ValueArray) -> bool {
        self.typ == other.typ && self.iter().zip(other.iter()).all(|(l, r)| l == r)
    }
}

pub struct Iter<'a> {
    array: &'a ValueArray,
    index: usize,
}
impl<'a> Iterator for Iter<'a> {
    type Item = Value;
    fn next(&mut self) -> Option<Value> {
        if self.index < self.array.len() {
            let value = self.array.get(self.index);
            self.index += 1;
            Some(value)
        } else {
            None
        }
    }
}

impl Traverseable for ValueArray {
    fn traverse(&self, gc: &mut Gc) {
        on_array!(*self, |array: &Array<_>| array.traverse(gc))
    }
}

impl ValueArray {
    pub fn get(&self, index: usize) -> Value {
        unsafe {
            match self.typ {
                ValueType::Int => Value::Int(self.unsafe_get(index)),
                ValueType::Float => Value::Float(self.unsafe_get(index)),
                ValueType::String => Value::String(self.unsafe_get(index)),
                ValueType::Data => Value::Data(self.unsafe_get(index)),
                ValueType::Array => Value::Array(self.unsafe_get(index)),
                ValueType::Function => Value::Function(self.unsafe_get(index)),
                ValueType::Closure => Value::Closure(self.unsafe_get(index)),
                ValueType::PartialApplication => Value::PartialApplication(self.unsafe_get(index)),
                ValueType::Userdata => Value::Userdata(self.unsafe_get(index)),
                ValueType::Thread => Value::Thread(self.unsafe_get(index)),
            }
        }
    }

    pub fn len(&self) -> usize {
        self.array.len()
    }

    pub fn iter(&self) -> Iter {
        Iter {
            array: self,
            index: 0,
        }
    }

    unsafe fn unsafe_get<T: Copy>(&self, index: usize) -> T {
        ::std::mem::transmute::<&Array<()>, &Array<T>>(&self.array)[index]
    }

    unsafe fn unsafe_array<T: Copy>(&self) -> &Array<T> {
        ::std::mem::transmute::<&Array<()>, &Array<T>>(&self.array)
    }

    pub unsafe fn unsafe_array_mut<T: Copy>(&mut self) -> &mut Array<T> {
        ::std::mem::transmute::<&mut Array<()>, &mut Array<T>>(&mut self.array)
    }

    unsafe fn initialize<I>(&mut self, iterable: I)
        where I: IntoIterator,
              I::Item: Copy
    {
        self.unsafe_array_mut().initialize(iterable)
    }
}

unsafe impl<'a> DataDef for &'a ValueArray {
    type Value = ValueArray;
    fn size(&self) -> usize {
        use std::mem::size_of;
        fn size_of_opt<T>(_: Option<&T>) -> usize {
            size_of::<T>()
        }
        let array_elems_size = on_array!(self, |array: &Array<_>| {
            array.len() * size_of_opt(array.first())
        });
        size_of::<ValueArray>() + array_elems_size
    }
    
    #[allow(unused_unsafe)]
    fn initialize<'w>(self, mut result: WriteOnly<'w, ValueArray>) -> &'w mut ValueArray {
        unsafe {
            let result = &mut *result.as_mut_ptr();
            result.typ = self.typ;
            on_array!(self, |array: &Array<_>| {
                result.unsafe_array_mut().initialize(array.iter().cloned())
            });
            result
        }
    }
}

pub struct ArrayDef<'b>(pub &'b [Value]);
impl<'b> Traverseable for ArrayDef<'b> {
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc);
    }
}

unsafe impl<'b> DataDef for ArrayDef<'b> {
    type Value = ValueArray;
    fn size(&self) -> usize {
        use std::mem::{size_of, size_of_val};
        let size = match self.0.first() {
            Some(value) => {
                let size = match *value {
                    Value::Int(ref x) => size_of_val(x),
                    Value::Float(ref x) => size_of_val(x),
                    Value::String(ref x) => size_of_val(x),
                    Value::Data(ref x) => size_of_val(x),
                    Value::Array(ref x) => size_of_val(x),
                    Value::Function(ref x) => size_of_val(x),
                    Value::Closure(ref x) => size_of_val(x),
                    Value::PartialApplication(ref x) => size_of_val(x),
                    Value::Userdata(ref x) => size_of_val(x),
                    Value::Thread(ref x) => size_of_val(x),
                };
                self.0.len() * size
            }
            None => 0,
        };
        size_of::<ValueArray>() + size
    }
    fn initialize<'w>(self, mut result: WriteOnly<'w, ValueArray>) -> &'w mut ValueArray {
        unsafe {
            let result = &mut *result.as_mut_ptr();
            match self.0.first() {
                Some(value) => {
                    match *value {
                        Value::Int(_) => {
                            result.typ = ValueType::Int;
                            let iter = self.0.iter().map(|v| match *v {
                                Value::Int(x) => x,
                                _ => unreachable!(),
                            });
                            result.initialize(iter);
                        }
                        Value::Float(_) => {
                            result.typ = ValueType::Float;
                            let iter = self.0.iter().map(|v| match *v {
                                Value::Float(x) => x,
                                _ => unreachable!(),
                            });
                            result.initialize(iter);
                        }
                        Value::String(_) => {
                            result.typ = ValueType::String;
                            let iter = self.0.iter().map(|v| match *v {
                                Value::String(x) => x,
                                _ => unreachable!(),
                            });
                            result.initialize(iter);
                        }
                        Value::Data(_) => {
                            result.typ = ValueType::Data;
                            let iter = self.0.iter().map(|v| match *v {
                                Value::Data(x) => x,
                                _ => unreachable!(),
                            });
                            result.initialize(iter);
                        }
                        Value::Array(_) => {
                            result.typ = ValueType::Array;
                            let iter = self.0.iter().map(|v| match *v {
                                Value::Array(x) => x,
                                _ => unreachable!(),
                            });
                            result.initialize(iter);
                        }
                        Value::Function(_) => {
                            result.typ = ValueType::Function;
                            let iter = self.0.iter().map(|v| match *v {
                                Value::Function(x) => x,
                                _ => unreachable!(),
                            });
                            result.initialize(iter);
                        }
                        Value::Closure(_) => {
                            result.typ = ValueType::Closure;
                            let iter = self.0.iter().map(|v| match *v {
                                Value::Closure(x) => x,
                                _ => unreachable!(),
                            });
                            result.initialize(iter);
                        }
                        Value::PartialApplication(_) => {
                            result.typ = ValueType::PartialApplication;
                            let iter = self.0.iter().map(|v| match *v {
                                Value::PartialApplication(x) => x,
                                _ => unreachable!(),
                            });
                            result.initialize(iter);
                        }
                        Value::Userdata(_) => {
                            result.typ = ValueType::Userdata;
                            let iter = self.0.iter().map(|v| match *v {
                                Value::Userdata(x) => x,
                                _ => unreachable!(),
                            });
                            result.initialize(iter);
                        }
                        Value::Thread(_) => {
                            result.typ = ValueType::Thread;
                            let iter = self.0.iter().map(|v| match *v {
                                Value::Thread(x) => x,
                                _ => unreachable!(),
                            });
                            result.initialize(iter);
                        }
                    }
                }
                None => result.typ = ValueType::Int,
            }
            result
        }
    }
}


fn deep_clone_ptr<T, A>(value: GcPtr<T>,
                        visited: &mut HashMap<*const (), Value>,
                        alloc: A)
                        -> StdResult<Value, GcPtr<T>>
    where A: FnOnce(&T) -> (Value, GcPtr<T>)
{
    let key = &*value as *const T as *const ();
    let new_ptr = match visited.entry(key) {
        Entry::Occupied(entry) => return Ok(*entry.get()),
        Entry::Vacant(entry) => {
            // FIXME Should allocate the real `Value` and possibly fill it later
            let (value, new_ptr) = alloc(&value);
            entry.insert(value);
            new_ptr
        }
    };
    Err(new_ptr)
}

fn deep_clone_str(data: GcPtr<Str>,
                  visited: &mut HashMap<*const (), Value>,
                  gc: &mut Gc)
                  -> Result<Value> {
    Ok(deep_clone_ptr(data, visited, |data| {
           let ptr = gc.alloc(&data[..]);
           (String(ptr), ptr)
       })
           .unwrap_or_else(String))
}
fn deep_clone_data(data: GcPtr<DataStruct>,
                   visited: &mut HashMap<*const (), Value>,
                   gc: &mut Gc)
                   -> Result<GcPtr<DataStruct>> {
    let result = deep_clone_ptr(data, visited, |data| {
        let ptr = gc.alloc(Def {
            tag: data.tag,
            elems: &data.fields,
        });
        (Value::Data(ptr), ptr)
    });
    match result {
        Ok(Value::Data(ptr)) => Ok(ptr),
        Ok(_) => unreachable!(),
        Err(mut new_data) => {
            {
                let new_fields = unsafe { &mut new_data.as_mut().fields };
                for (new, old) in new_fields.iter_mut().zip(&data.fields) {
                    *new = try!(deep_clone(old, visited, gc));
                }
            }
            Ok(new_data)
        }
    }
}

fn deep_clone_array(array: GcPtr<ValueArray>,
                    visited: &mut HashMap<*const (), Value>,
                    gc: &mut Gc)
                    -> Result<GcPtr<ValueArray>> {
    type CloneFn<T> = fn(GcPtr<T>, &mut HashMap<*const (), Value>, &mut Gc) -> Result<GcPtr<T>>;
    unsafe fn deep_clone_elems<T>(deep_clone: CloneFn<T>,
                                  mut new_array: GcPtr<ValueArray>,
                                  visited: &mut HashMap<*const (), Value>,
                                  gc: &mut Gc)
                                  -> Result<()> {
        let new_array = new_array.as_mut().unsafe_array_mut::<GcPtr<T>>();
        for field in new_array.iter_mut() {
            *field = try!(deep_clone(*field, visited, gc));
        }
        Ok(())
    }

    let result = deep_clone_ptr(array, visited, |array| {
        let ptr = gc.alloc(array);
        (Value::Array(ptr), ptr)
    });
    match result {
        Ok(Value::Array(ptr)) => Ok(ptr),
        Ok(_) => unreachable!(),
        Err(new_array) => {
            unsafe {
                try!(match new_array.typ {
                    ValueType::Int | ValueType::Float | ValueType::String => Ok(()),
                    ValueType::Data => deep_clone_elems(deep_clone_data, new_array, visited, gc),
                    ValueType::Array => deep_clone_elems(deep_clone_array, new_array, visited, gc),
                    ValueType::Closure => {
                        deep_clone_elems(deep_clone_closure, new_array, visited, gc)
                    }
                    ValueType::PartialApplication => {
                        deep_clone_elems(deep_clone_app, new_array, visited, gc)
                    }
                    ValueType::Function | ValueType::Userdata | ValueType::Thread => {
                        return Err(Error::Message("Threads, Userdata and Extern functions cannot \
                                                   be deep cloned yet"
                                                      .into()))
                    }
                });
            }
            Ok(new_array)
        }
    }
}

fn deep_clone_closure(data: GcPtr<ClosureData>,
                      visited: &mut HashMap<*const (), Value>,
                      gc: &mut Gc)
                      -> Result<GcPtr<ClosureData>> {
    let result = deep_clone_ptr(data, visited, |data| {
        let ptr = gc.alloc(ClosureDataDef(data.function, &data.upvars));
        (Closure(ptr), ptr)
    });
    match result {
        Ok(Value::Closure(ptr)) => Ok(ptr),
        Ok(_) => unreachable!(),
        Err(mut new_data) => {
            {
                let new_upvars = unsafe { &mut new_data.as_mut().upvars };
                for (new, old) in new_upvars.iter_mut().zip(&data.upvars) {
                    *new = try!(deep_clone(old, visited, gc));
                }
            }
            Ok(new_data)
        }
    }
}
fn deep_clone_app(data: GcPtr<PartialApplicationData>,
                  visited: &mut HashMap<*const (), Value>,
                  gc: &mut Gc)
                  -> Result<GcPtr<PartialApplicationData>> {
    let result = deep_clone_ptr(data, visited, |data| {
        let ptr = gc.alloc(PartialApplicationDataDef(data.function, &data.arguments));
        (PartialApplication(ptr), ptr)
    });
    match result {
        Ok(Value::PartialApplication(ptr)) => Ok(ptr),
        Ok(_) => unreachable!(),
        Err(mut new_data) => {
            {
                let new_arguments = unsafe { &mut new_data.as_mut().arguments };
                for (new, old) in new_arguments.iter_mut()
                                               .zip(&data.arguments) {
                    *new = try!(deep_clone(old, visited, gc));
                }
            }
            Ok(new_data)
        }
    }
}
pub fn deep_clone(value: &Value,
                  visited: &mut HashMap<*const (), Value>,
                  gc: &mut Gc)
                  -> Result<Value> {
    // Only need to clone values which belong to a younger generation than the gc that the new
    // value will live in
    if value.generation() <= gc.generation() {
        return Ok(*value);
    }
    match *value {
        String(data) => deep_clone_str(data, visited, gc),
        Value::Data(data) => deep_clone_data(data, visited, gc).map(Value::Data),
        Value::Array(data) => deep_clone_array(data, visited, gc).map(Value::Array),
        Closure(data) => deep_clone_closure(data, visited, gc).map(Value::Closure),
        PartialApplication(data) => {
            deep_clone_app(data, visited, gc).map(Value::PartialApplication)
        }
        Function(_) |
        Value::Userdata(_) |
        Value::Thread(_) => {
            return Err(Error::Message("Threads, Userdata and Extern functions cannot be deep \
                                       cloned yet"
                                          .into()))
        }
        Int(i) => Ok(Int(i)),
        Float(f) => Ok(Float(f)),
    }
}
