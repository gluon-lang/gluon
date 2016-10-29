use std::fmt;
use std::collections::hash_map::Entry;
use std::result::Result as StdResult;

use base::symbol::Symbol;
use types::*;
use base::fnv::FnvMap;

use interner::InternedStr;
use gc::{Gc, GcPtr, Traverseable, DataDef, Move, WriteOnly};
use array::{Array, Str};
use thread::{Thread, Status};
use {Error, Result};

use self::Value::{Int, Float, String, Function, PartialApplication, Closure};

mopafy!(Userdata);
pub trait Userdata: ::mopa::Any + Traverseable + fmt::Debug + Send + Sync {}

impl PartialEq for Userdata {
    fn eq(&self, other: &Userdata) -> bool {
        self as *const _ == other as *const _
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
    pub args: VmIndex,
    pub max_stack_size: VmIndex,
    pub instructions: Vec<Instruction>,
    pub inner_functions: Vec<GcPtr<BytecodeFunction>>,
    pub strings: Vec<InternedStr>,
    pub globals: Vec<Value>,
    pub records: Vec<Vec<InternedStr>>,
}

impl Traverseable for BytecodeFunction {
    fn traverse(&self, gc: &mut Gc) {
        self.inner_functions.traverse(gc);
        self.globals.traverse(gc);
    }
}

#[derive(Debug)]
pub struct DataStruct {
    pub tag: VmTag,
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
    pub tag: VmTag,
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
    Byte(u8),
    Int(VmInt),
    Float(f64),
    String(GcPtr<Str>),
    Tag(VmTag),
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
            Value::Tag(_) | Value::Byte(_) | Int(_) | Float(_) => 0,
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

    pub fn args(&self) -> VmIndex {
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
    pub args: Array<Value>,
}

impl PartialEq for PartialApplicationData {
    fn eq(&self, _: &PartialApplicationData) -> bool {
        false
    }
}

impl Traverseable for PartialApplicationData {
    fn traverse(&self, gc: &mut Gc) {
        self.function.traverse(gc);
        self.args.traverse(gc);
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
            result.args.initialize(self.1.iter().cloned());
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
            Value::Tag(_) | Value::Byte(_) | Int(_) | Float(_) => (),
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
                    Value::Byte(i) => write!(f, "{:?}b", i),
                    Int(i) => write!(f, "{:?}", i),
                    Float(x) => write!(f, "{:?}f", x),
                    String(x) => write!(f, "{:?}", &*x),
                    Value::Tag(tag) => write!(f, "{{{:?}: }}", tag),
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
                        write!(f, "<App {:?}{:?}>", name, LevelSlice(level - 1, &app.args))
                    }
                    Value::Userdata(ref data) => write!(f, "<Userdata {:?}>", &**data),
                    Value::Thread(_) => write!(f, "<thread>"),
                }
            }
        }
        write!(f, "{:?}", Level(3, self))
    }
}

pub struct ExternFunction {
    pub id: Symbol,
    pub args: VmIndex,
    pub function: extern "C" fn(&Thread) -> Status,
}

impl Clone for ExternFunction {
    fn clone(&self) -> ExternFunction {
        ExternFunction {
            id: self.id.clone(),
            args: self.args,
            function: self.function,
        }
    }
}

impl PartialEq for ExternFunction {
    fn eq(&self, _: &ExternFunction) -> bool {
        false
    }
}

impl fmt::Debug for ExternFunction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // read the v-table pointer of the Fn(..) type and print that
        let p: *const () = unsafe { ::std::mem::transmute(self.function) };
        write!(f, "{:?}", p)
    }
}

impl Traverseable for ExternFunction {
    fn traverse(&self, _: &mut Gc) {}
}


/// Representation of values which can be stored directly in an array
#[derive(Copy, Clone, PartialEq, Debug)]
pub enum Repr {
    Byte,
    Int,
    Float,
    String,
    Array,
    Unknown,
    Userdata,
    Thread,
}

pub unsafe trait ArrayRepr {
    fn matches(repr: Repr) -> bool;
}

macro_rules! impl_repr {
    ($($id: ty, $repr: path),*) => {
        $(
        unsafe impl ArrayRepr for $id {
            fn matches(repr: Repr) -> bool { repr == $repr }
        }

        unsafe impl<'a> DataDef for &'a [$id] {
            type Value = ValueArray;
            fn size(&self) -> usize {
                use std::mem::size_of;
                size_of::<ValueArray>() + self.len() * size_of::<$id>()
            }
            fn initialize<'w>(self, mut result: WriteOnly<'w, ValueArray>) -> &'w mut ValueArray {
                unsafe {
                    let result = &mut *result.as_mut_ptr();
                    result.set_repr($repr);
                    result.unsafe_array_mut::<$id>().initialize(self.iter().cloned());
                    result
                }
            }
        }
        )*
        impl Repr {
            fn size_of(self) -> usize {
                use std::mem::size_of;
                match self {
                    $(
                        $repr => size_of::<$id>(),
                    )*
                }
            }
        }
    }
}

impl_repr! {
    u8, Repr::Byte,
    VmInt, Repr::Int,
    f64, Repr::Float,
    GcPtr<Str>, Repr::String,
    GcPtr<ValueArray>, Repr::Array,
    Value, Repr::Unknown,
    GcPtr<Box<Userdata>>, Repr::Userdata,
    GcPtr<Thread>, Repr::Thread
}

impl Repr {
    fn from_value(value: Value) -> Repr {
        match value {
            Value::Byte(_) => Repr::Byte,
            Value::Int(_) => Repr::Int,
            Value::Float(_) => Repr::Float,
            Value::String(_) => Repr::String,
            Value::Array(_) => Repr::Array,
            Value::Data(_) |
            Value::Tag(_) |
            Value::Function(_) |
            Value::Closure(_) |
            Value::PartialApplication(_) => Repr::Unknown,
            Value::Userdata(_) => Repr::Userdata,
            Value::Thread(_) => Repr::Thread,
        }
    }
}

#[macro_export]
macro_rules! on_array {
    ($array: expr, $f: expr) => {
        {
            let ref array = $array;
            unsafe {
                match array.repr() {
                    Repr::Byte => $f(array.unsafe_array::<u8>()),
                    Repr::Int => $f(array.unsafe_array::<VmInt>()),
                    Repr::Float => $f(array.unsafe_array::<f64>()),
                    Repr::String => $f(array.unsafe_array::<GcPtr<Str>>()),
                    Repr::Array => $f(array.unsafe_array::<GcPtr<ValueArray>>()),
                    Repr::Unknown => $f(array.unsafe_array::<Value>()),
                    Repr::Userdata => $f(array.unsafe_array::<GcPtr<Box<Userdata>>>()),
                    Repr::Thread => $f(array.unsafe_array::<GcPtr<Thread>>()),
                }
            }
        }
    }
}


#[derive(Debug)]
pub struct ValueArray {
    repr: Repr,
    array: Array<()>,
}

impl PartialEq for ValueArray {
    fn eq(&self, other: &ValueArray) -> bool {
        self.repr == other.repr && self.iter().zip(other.iter()).all(|(l, r)| l == r)
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

    fn size_hint(&self) -> (usize, Option<usize>) {
        let i = self.array.len() - self.index;
        (i, Some(i))
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
            match self.repr {
                Repr::Byte => Value::Byte(self.unsafe_get(index)),
                Repr::Int => Value::Int(self.unsafe_get(index)),
                Repr::Float => Value::Float(self.unsafe_get(index)),
                Repr::String => Value::String(self.unsafe_get(index)),
                Repr::Array => Value::Array(self.unsafe_get(index)),
                Repr::Unknown => self.unsafe_get(index),
                Repr::Userdata => Value::Userdata(self.unsafe_get(index)),
                Repr::Thread => Value::Thread(self.unsafe_get(index)),
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

    pub fn size_of(repr: Repr, len: usize) -> usize {
        ::std::mem::size_of::<ValueArray>() + repr.size_of() * len
    }

    pub fn repr(&self) -> Repr {
        self.repr
    }

    pub unsafe fn set_repr(&mut self, repr: Repr) {
        self.repr = repr;
    }

    pub unsafe fn initialize<I>(&mut self, iter: I)
        where I: IntoIterator<Item = Value>,
    {
        let iter = iter.into_iter();
        match self.repr {
            Repr::Byte => {
                let iter = iter.map(|v| match v {
                    Value::Byte(x) => x,
                    _ => unreachable!(),
                });
                self.unsafe_array_mut().initialize(iter);
            }
            Repr::Int => {
                let iter = iter.map(|v| match v {
                    Value::Int(x) => x,
                    _ => unreachable!(),
                });
                self.unsafe_array_mut().initialize(iter);
            }
            Repr::Float => {
                let iter = iter.map(|v| match v {
                    Value::Float(x) => x,
                    _ => unreachable!(),
                });
                self.unsafe_array_mut().initialize(iter);
            }
            Repr::String => {
                let iter = iter.map(|v| match v {
                    Value::String(x) => x,
                    _ => unreachable!(),
                });
                self.unsafe_array_mut().initialize(iter);
            }
            Repr::Array => {
                let iter = iter.map(|v| match v {
                    Value::Array(x) => x,
                    _ => unreachable!(),
                });
                self.unsafe_array_mut().initialize(iter);
            }
            Repr::Unknown => {
                self.unsafe_array_mut().initialize(iter);
            }
            Repr::Userdata => {
                let iter = iter.map(|v| match v {
                    Value::Userdata(x) => x,
                    _ => unreachable!(),
                });
                self.unsafe_array_mut().initialize(iter);
            }
            Repr::Thread => {
                let iter = iter.map(|v| match v {
                    Value::Thread(x) => x,
                    _ => unreachable!(),
                });
                self.unsafe_array_mut().initialize(iter);
            }
        }
    }

    pub fn as_slice<T: ArrayRepr + Copy>(&self) -> Option<&[T]> {
        unsafe {
            if T::matches(self.repr) {
                Some(self.unsafe_array::<T>())
            } else {
                None
            }
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
}

unsafe impl<'a> DataDef for &'a ValueArray {
    type Value = ValueArray;
    fn size(&self) -> usize {
        ValueArray::size_of(self.repr, self.len())
    }

    #[allow(unused_unsafe)]
    fn initialize<'w>(self, mut result: WriteOnly<'w, ValueArray>) -> &'w mut ValueArray {
        unsafe {
            let result = &mut *result.as_mut_ptr();
            result.repr = self.repr;
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
        use std::mem::size_of;
        let size = match self.0.first() {
            Some(value) => Repr::from_value(*value).size_of() * self.0.len(),
            None => 0,
        };
        size_of::<ValueArray>() + size
    }
    fn initialize<'w>(self, mut result: WriteOnly<'w, ValueArray>) -> &'w mut ValueArray {
        unsafe {
            let result = &mut *result.as_mut_ptr();
            match self.0.first() {
                Some(value) => {
                    result.repr = Repr::from_value(*value);
                    result.initialize(self.0.iter().cloned());
                }
                None => {
                    result.repr = Repr::Unknown;
                    result.initialize(None);
                }
            }
            result
        }
    }
}

fn deep_clone_ptr<T, A>(value: GcPtr<T>,
                        visited: &mut FnvMap<*const (), Value>,
                        alloc: A)
                        -> Result<StdResult<Value, GcPtr<T>>>
    where A: FnOnce(&T) -> Result<(Value, GcPtr<T>)>,
{
    let key = &*value as *const T as *const ();
    let new_ptr = match visited.entry(key) {
        Entry::Occupied(entry) => return Ok(Ok(*entry.get())),
        Entry::Vacant(entry) => {
            // FIXME Should allocate the real `Value` and possibly fill it later
            let (value, new_ptr) = try!(alloc(&value));
            entry.insert(value);
            new_ptr
        }
    };
    Ok(Err(new_ptr))
}

fn deep_clone_str(data: GcPtr<Str>,
                  visited: &mut FnvMap<*const (), Value>,
                  gc: &mut Gc)
                  -> Result<Value> {
    Ok(try!(deep_clone_ptr(data, visited, |data| {
            let ptr = try!(gc.alloc(&data[..]));
            Ok((String(ptr), ptr))
        }))
        .unwrap_or_else(String))
}
fn deep_clone_data(data: GcPtr<DataStruct>,
                   visited: &mut FnvMap<*const (), Value>,
                   gc: &mut Gc)
                   -> Result<GcPtr<DataStruct>> {
    let result = try!(deep_clone_ptr(data, visited, |data| {
        let ptr = try!(gc.alloc(Def {
            tag: data.tag,
            elems: &data.fields,
        }));
        Ok((Value::Data(ptr), ptr))
    }));
    match result {
        Ok(Value::Data(ptr)) => Ok(ptr),
        Ok(_) => unreachable!(),
        Err(mut new_data) => {
            {
                let new_fields = unsafe { &mut new_data.as_mut().fields };
                for (new, old) in new_fields.iter_mut().zip(&data.fields) {
                    *new = try!(deep_clone(*old, visited, gc));
                }
            }
            Ok(new_data)
        }
    }
}

fn deep_clone_array(array: GcPtr<ValueArray>,
                    visited: &mut FnvMap<*const (), Value>,
                    gc: &mut Gc)
                    -> Result<GcPtr<ValueArray>> {
    type CloneFn<T> = fn(T, &mut FnvMap<*const (), Value>, &mut Gc) -> Result<T>;
    unsafe fn deep_clone_elems<T: Copy>(deep_clone: CloneFn<T>,
                                        mut new_array: GcPtr<ValueArray>,
                                        visited: &mut FnvMap<*const (), Value>,
                                        gc: &mut Gc)
                                        -> Result<()> {
        let new_array = new_array.as_mut().unsafe_array_mut::<T>();
        for field in new_array.iter_mut() {
            *field = try!(deep_clone(*field, visited, gc));
        }
        Ok(())
    }

    let result = try!(deep_clone_ptr(array, visited, |array| {
        let ptr = try!(gc.alloc(array));
        Ok((Value::Array(ptr), ptr))
    }));
    match result {
        Ok(Value::Array(ptr)) => Ok(ptr),
        Ok(_) => unreachable!(),
        Err(new_array) => {
            unsafe {
                try!(match new_array.repr() {
                    Repr::Byte | Repr::Int | Repr::Float | Repr::String => Ok(()),
                    Repr::Array => deep_clone_elems(deep_clone_array, new_array, visited, gc),
                    Repr::Unknown => deep_clone_elems(deep_clone, new_array, visited, gc),
                    Repr::Userdata | Repr::Thread => {
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
                      visited: &mut FnvMap<*const (), Value>,
                      gc: &mut Gc)
                      -> Result<GcPtr<ClosureData>> {
    let result = try!(deep_clone_ptr(data, visited, |data| {
        let ptr = try!(gc.alloc(ClosureDataDef(data.function, &data.upvars)));
        Ok((Closure(ptr), ptr))
    }));
    match result {
        Ok(Value::Closure(ptr)) => Ok(ptr),
        Ok(_) => unreachable!(),
        Err(mut new_data) => {
            {
                let new_upvars = unsafe { &mut new_data.as_mut().upvars };
                for (new, old) in new_upvars.iter_mut().zip(&data.upvars) {
                    *new = try!(deep_clone(*old, visited, gc));
                }
            }
            Ok(new_data)
        }
    }
}
fn deep_clone_app(data: GcPtr<PartialApplicationData>,
                  visited: &mut FnvMap<*const (), Value>,
                  gc: &mut Gc)
                  -> Result<GcPtr<PartialApplicationData>> {
    let result = try!(deep_clone_ptr(data, visited, |data| {
        let ptr = try!(gc.alloc(PartialApplicationDataDef(data.function, &data.args)));
        Ok((PartialApplication(ptr), ptr))
    }));
    match result {
        Ok(Value::PartialApplication(ptr)) => Ok(ptr),
        Ok(_) => unreachable!(),
        Err(mut new_data) => {
            {
                let new_args = unsafe { &mut new_data.as_mut().args };
                for (new, old) in new_args.iter_mut()
                    .zip(&data.args) {
                    *new = try!(deep_clone(*old, visited, gc));
                }
            }
            Ok(new_data)
        }
    }
}
pub fn deep_clone(value: Value,
                  visited: &mut FnvMap<*const (), Value>,
                  gc: &mut Gc)
                  -> Result<Value> {
    // Only need to clone values which belong to a younger generation than the gc that the new
    // value will live in
    if value.generation() <= gc.generation() {
        return Ok(value);
    }
    match value {
        String(data) => deep_clone_str(data, visited, gc),
        Value::Data(data) => deep_clone_data(data, visited, gc).map(Value::Data),
        Value::Array(data) => deep_clone_array(data, visited, gc).map(Value::Array),
        Closure(data) => deep_clone_closure(data, visited, gc).map(Value::Closure),
        PartialApplication(data) => {
            deep_clone_app(data, visited, gc).map(Value::PartialApplication)
        }
        Function(ref f) => gc.alloc(Move(ExternFunction::clone(f))).map(Value::Function),
        Value::Userdata(_) |
        Value::Thread(_) => {
            return Err(Error::Message("Threads and Userdata cannot be deep cloned yet".into()))
        }
        Value::Tag(i) => Ok(Value::Tag(i)),
        Value::Byte(i) => Ok(Value::Byte(i)),
        Int(i) => Ok(Int(i)),
        Float(f) => Ok(Float(f)),
    }
}
