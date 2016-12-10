use std::fmt;
use std::collections::hash_map::Entry;
use std::result::Result as StdResult;

use itertools::Itertools;

use pretty::{Arena, DocAllocator, DocBuilder};

use base::symbol::Symbol;
use base::types::{ArcType, Type, TypeEnv};
use types::*;
use base::fnv::FnvMap;

use interner::InternedStr;
use gc::{Gc, GcPtr, Traverseable, DataDef, Move, WriteOnly};
use array::{Array, Str};
use source_map::SourceMap;
use thread::{Thread, Status};
use {Error, Result};

use self::Value::{Int, Float, String, Function, PartialApplication, Closure};

mopafy!(Userdata);
pub trait Userdata: ::mopa::Any + Traverseable + fmt::Debug + Send + Sync {
    fn deep_clone(&self,
                  visited: &mut FnvMap<*const (), Value>,
                  gc: &mut Gc,
                  thread: &Thread)
                  -> Result<GcPtr<Box<Userdata>>> {
        let _ = (visited, gc, thread);
        Err(Error::Message("Userdata cannot be cloned".into()))
    }
}

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
    pub source_map: SourceMap,
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

#[derive(PartialEq, Copy, Clone, PartialOrd)]
enum Prec {
    Top,
    Constructor,
}

pub struct ValuePrinter<'a> {
    typ: &'a ArcType,
    env: &'a TypeEnv,
    prec: Prec,
    value: Value,
}

impl<'a> fmt::Display for ValuePrinter<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        const WIDTH: usize = 80;

        let arena = Arena::new();
        let mut s = Vec::new();
        self.pretty(&arena)
            .group()
            .1
            .render(WIDTH, &mut s)
            .map_err(|_| fmt::Error)?;
        write!(f, "{}", ::std::str::from_utf8(&s).expect("utf-8"))
    }
}

fn p<'t>(typ: &'t ArcType, env: &'t TypeEnv, prec: Prec, value: Value) -> ValuePrinter<'t> {
    ValuePrinter {
        typ: typ,
        env: env,
        prec: prec,
        value: value,
    }
}

impl<'t> ValuePrinter<'t> {
    pub fn new(typ: &'t ArcType, env: &'t TypeEnv, value: Value) -> ValuePrinter<'t> {
        p(typ, env, Prec::Top, value)
    }

    pub fn pretty<'a>(&self, arena: &'a Arena<'a>) -> DocBuilder<'a, Arena<'a>> {
        fn enclose<'a>(p: Prec,
                       limit: Prec,
                       arena: &'a Arena<'a>,
                       doc: DocBuilder<'a, Arena<'a>>)
                       -> DocBuilder<'a, Arena<'a>> {
            if p >= limit {
                chain![arena; "(", doc, ")"]
            } else {
                doc
            }
        }
        fn pretty_data<'a, I>(tag: VmTag,
                              fields: I,
                              prec: Prec,
                              env: &TypeEnv,
                              typ: &ArcType,
                              arena: &'a Arena<'a>)
                              -> DocBuilder<'a, Arena<'a>>
            where I: IntoIterator<Item = Value>,
        {
            let typ = remove_aliases_cow(env, typ);
            match **typ {
                Type::Record(ref row) => {
                        chain![arena;
                            "{",
                            arena.concat(fields.into_iter().zip(row.row_iter())
                                .map(|(field, type_field)| {
                                    arena.space().append(p(&type_field.typ, env, Top, field).pretty(arena))
                                }).intersperse(arena.text(","))),
                            arena.space(),
                            "}"
                        ]
                    }
                Type::Variant(ref row) => {
                    let type_field = row.row_iter()
                        .nth(tag as usize)
                        .expect("Variant tag is out of bounds");
                    let mut empty = true;
                    let doc = chain![arena;
                            type_field.name.declared_name().to_string(),
                            arena.concat(fields.into_iter().zip(arg_iter(&type_field.typ))
                                .map(|(field, typ)| {
                                    empty = false;
                                    arena.space().append(p(typ, env, Constructor, field).pretty(arena))
                                }))
                        ];
                    if empty {
                        doc
                    } else {
                        enclose(prec, Constructor, arena, doc)
                    }
                }
                _ => {
                    chain![arena;
                        "{",
                        arena.concat(fields.into_iter().map(|field| {
                            arena.space().append(p(&Type::hole(), env, Top, field).pretty(arena))
                        }).intersperse(arena.text(","))),
                        arena.space(),
                        "}"
                    ]
                }
            }
        }

        use self::Prec::*;
        use base::types::arg_iter;
        use base::resolve::remove_aliases_cow;

        use std::iter;

        let env = self.env;
        match self.value {
            Value::String(s) => arena.text(format!("{:?}", s)),
            Value::Data(ref data) => {
                pretty_data(data.tag,
                            data.fields.iter().cloned(),
                            self.prec,
                            env,
                            self.typ,
                            arena)
            }
            Value::Tag(tag) => pretty_data(tag, iter::empty(), self.prec, env, self.typ, arena),
            Value::Function(ref function) => {
                chain![arena;
                    "<extern ",
                    function.id.declared_name().to_string(),
                    ">"
                ]
            }
            Value::Closure(ref closure) => {
                chain![arena;
                    "{",
                    arena.concat(closure.upvars.iter().map(|field| {
                        arena.text(format!("{:?}", field))
                    })),
                    "}"
                ]
            }
            Value::Array(ref array) => {
                chain![arena;
                    "[",
                    arena.concat(array.iter().map(|field| {
                        match **self.typ {
                            Type::App(_, ref args) => p(&args[0], env, Top, field).pretty(arena),
                            _ => arena.text(format!("{:?}", field)),
                        }
                    }).intersperse(arena.text(",").append(arena.space()))),
                    "]"
                ]
            }
            Value::PartialApplication(p) => arena.text(format!("{:?}", p)),
            Value::Userdata(ref data) => arena.text(format!("{:?}", data)),
            Value::Thread(thread) => arena.text(format!("{:?}", thread)),
            Value::Byte(b) => arena.text(format!("{}", b)),
            Value::Int(i) => arena.text(format!("{}", i)),
            Value::Float(f) => arena.text(format!("{}", f)),
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
                write!(f, "{:?}", Level(level - 1, &self.1[0]))?;
                for v in &self.1[1..] {
                    write!(f, ", {:?}", Level(level - 1, v))?;
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
                        write!(f, "[")?;
                        for value in array.iter() {
                            if !first {
                                write!(f, ", ")?;
                            }
                            first = false;
                            write!(f, "{:?}", Level(level - 1, &value))?;
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
            on_array!(self,
                      |array: &Array<_>| result.unsafe_array_mut().initialize(array.iter().cloned()));
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
            let (value, new_ptr) = alloc(&value)?;
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
    Ok(deep_clone_ptr(data, visited, |data| {
            let ptr = gc.alloc(&data[..])?;
            Ok((String(ptr), ptr))
        })
        ?
        .unwrap_or_else(String))
}
fn deep_clone_data(data: GcPtr<DataStruct>,
                   visited: &mut FnvMap<*const (), Value>,
                   gc: &mut Gc,
                   thread: &Thread)
                   -> Result<GcPtr<DataStruct>> {
    let result = deep_clone_ptr(data, visited, |data| {
        let ptr = gc.alloc(Def {
                tag: data.tag,
                elems: &data.fields,
            })?;
        Ok((Value::Data(ptr), ptr))
    })?;
    match result {
        Ok(Value::Data(ptr)) => Ok(ptr),
        Ok(_) => unreachable!(),
        Err(mut new_data) => {
            {
                let new_fields = unsafe { &mut new_data.as_mut().fields };
                for (new, old) in new_fields.iter_mut().zip(&data.fields) {
                    *new = deep_clone(*old, visited, gc, thread)?;
                }
            }
            Ok(new_data)
        }
    }
}

fn deep_clone_userdata(ptr: GcPtr<Box<Userdata>>,
                       visited: &mut FnvMap<*const (), Value>,
                       gc: &mut Gc,
                       thread: &Thread)
                       -> Result<GcPtr<Box<Userdata>>> {
    ptr.deep_clone(visited, gc, thread)
}

fn deep_clone_array(array: GcPtr<ValueArray>,
                    visited: &mut FnvMap<*const (), Value>,
                    gc: &mut Gc,
                    thread: &Thread)
                    -> Result<GcPtr<ValueArray>> {
    type CloneFn<T> = fn(T, &mut FnvMap<*const (), Value>, &mut Gc, &Thread) -> Result<T>;
    unsafe fn deep_clone_elems<T: Copy>(deep_clone: CloneFn<T>,
                                        mut new_array: GcPtr<ValueArray>,
                                        visited: &mut FnvMap<*const (), Value>,
                                        gc: &mut Gc,
                                        thread: &Thread)
                                        -> Result<()> {
        let new_array = new_array.as_mut().unsafe_array_mut::<T>();
        for field in new_array.iter_mut() {
            *field = deep_clone(*field, visited, gc, thread)?;
        }
        Ok(())
    }

    let result = deep_clone_ptr(array, visited, |array| {
        let ptr = gc.alloc(array)?;
        Ok((Value::Array(ptr), ptr))
    })?;
    match result {
        Ok(Value::Array(ptr)) => Ok(ptr),
        Ok(_) => unreachable!(),
        Err(new_array) => {
            unsafe {
                match new_array.repr() {
                    Repr::Byte | Repr::Int | Repr::Float | Repr::String => Ok(()),
                    Repr::Array => {
                        deep_clone_elems(deep_clone_array, new_array, visited, gc, thread)
                    }
                    Repr::Unknown => deep_clone_elems(deep_clone, new_array, visited, gc, thread),
                    Repr::Userdata => {
                        deep_clone_elems(deep_clone_userdata, new_array, visited, gc, thread)
                    }
                    Repr::Thread => {
                        return Err(Error::Message("Threads cannot be deep cloned yet".into()))
                    }
                }?;
            }
            Ok(new_array)
        }
    }
}

fn deep_clone_closure(data: GcPtr<ClosureData>,
                      visited: &mut FnvMap<*const (), Value>,
                      gc: &mut Gc,
                      thread: &Thread)
                      -> Result<GcPtr<ClosureData>> {
    let result = deep_clone_ptr(data, visited, |data| {
        let ptr = gc.alloc(ClosureDataDef(data.function, &data.upvars))?;
        Ok((Closure(ptr), ptr))
    })?;
    match result {
        Ok(Value::Closure(ptr)) => Ok(ptr),
        Ok(_) => unreachable!(),
        Err(mut new_data) => {
            {
                let new_upvars = unsafe { &mut new_data.as_mut().upvars };
                for (new, old) in new_upvars.iter_mut().zip(&data.upvars) {
                    *new = deep_clone(*old, visited, gc, thread)?;
                }
            }
            Ok(new_data)
        }
    }
}
fn deep_clone_app(data: GcPtr<PartialApplicationData>,
                  visited: &mut FnvMap<*const (), Value>,
                  gc: &mut Gc,
                  thread: &Thread)
                  -> Result<GcPtr<PartialApplicationData>> {
    let result = deep_clone_ptr(data, visited, |data| {
        let ptr = gc.alloc(PartialApplicationDataDef(data.function, &data.args))?;
        Ok((PartialApplication(ptr), ptr))
    })?;
    match result {
        Ok(Value::PartialApplication(ptr)) => Ok(ptr),
        Ok(_) => unreachable!(),
        Err(mut new_data) => {
            {
                let new_args = unsafe { &mut new_data.as_mut().args };
                for (new, old) in new_args.iter_mut()
                    .zip(&data.args) {
                    *new = deep_clone(*old, visited, gc, thread)?;
                }
            }
            Ok(new_data)
        }
    }
}
pub fn deep_clone(value: Value,
                  visited: &mut FnvMap<*const (), Value>,
                  gc: &mut Gc,
                  thread: &Thread)
                  -> Result<Value> {
    // Only need to clone values which belong to a younger generation than the gc that the new
    // value will live in
    if value.generation() <= gc.generation() {
        return Ok(value);
    }
    match value {
        String(data) => deep_clone_str(data, visited, gc),
        Value::Data(data) => deep_clone_data(data, visited, gc, thread).map(Value::Data),
        Value::Array(data) => deep_clone_array(data, visited, gc, thread).map(Value::Array),
        Closure(data) => deep_clone_closure(data, visited, gc, thread).map(Value::Closure),
        PartialApplication(data) => {
            deep_clone_app(data, visited, gc, thread).map(Value::PartialApplication)
        }
        Function(f) => gc.alloc(Move(ExternFunction::clone(&f))).map(Value::Function),
        Value::Tag(i) => Ok(Value::Tag(i)),
        Value::Byte(i) => Ok(Value::Byte(i)),
        Int(i) => Ok(Int(i)),
        Float(f) => Ok(Float(f)),
        Value::Userdata(userdata) => userdata.deep_clone(visited, gc, thread).map(Value::Userdata),
        Value::Thread(_) => Err(Error::Message("Threads cannot be deep cloned yet".into())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use gc::Gc;
    use types::VmInt;

    use base::kind::{ArcKind, KindEnv};
    use base::types::{Alias, AliasData, ArcType, Field, Type, TypeEnv};
    use base::symbol::{Symbol, SymbolRef};

    struct MockEnv(Option<Alias<Symbol, ArcType>>);

    impl KindEnv for MockEnv {
        fn find_kind(&self, _type_name: &SymbolRef) -> Option<ArcKind> {
            None
        }
    }

    impl TypeEnv for MockEnv {
        fn find_type(&self, _id: &SymbolRef) -> Option<&ArcType> {
            None
        }

        fn find_type_info(&self, _id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>> {
            self.0.as_ref()
        }

        fn find_record(&self, _fields: &[Symbol]) -> Option<(&ArcType, &ArcType)> {
            None
        }
    }

    #[test]
    fn pretty_variant() {
        let mut gc = Gc::new(0, usize::max_value());

        let list = Symbol::from("List");
        let typ: ArcType = Type::variant(vec![Field {
                                                  name: Symbol::from("Cons"),
                                                  typ: Type::function(vec![Type::int(),
                                                                  Type::ident(list.clone())],
                                                                      Type::ident(list.clone())),
                                              },
                                              Field {
                                                  name: Symbol::from("Nil"),
                                                  typ: Type::ident(list.clone()),
                                              }]);

        let env = MockEnv(Some(Alias::from(AliasData {
            name: list.clone(),
            args: vec![],
            typ: typ.clone(),
        })));

        let nil = Value::Tag(1);
        assert_eq!(format!("{}", ValuePrinter::new(&typ, &env, nil)), "Nil");
        let list1 = Value::Data(gc.alloc(Def {
                tag: 0,
                elems: &[Value::Int(123), nil],
            })
            .unwrap());
        assert_eq!(format!("{}", ValuePrinter::new(&typ, &env, list1)),
                   "Cons 123 Nil");
        let list2 = Value::Data(gc.alloc(Def {
                tag: 0,
                elems: &[Value::Int(0), list1],
            })
            .unwrap());
        assert_eq!(format!("{}", ValuePrinter::new(&typ, &env, list2)),
                   "Cons 0 (Cons 123 Nil)");
    }

    #[test]
    fn pretty_array() {
        let mut gc = Gc::new(0, usize::max_value());

        let typ = Type::array(Type::int());

        let env = MockEnv(None);

        let nil = Value::Array(gc.alloc(&[1 as VmInt, 2, 3][..]).unwrap());
        assert_eq!(format!("{}", ValuePrinter::new(&typ, &env, nil)),
                   "[1, 2, 3]");
    }
}
