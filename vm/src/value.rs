use std::collections::hash_map::Entry;
use std::fmt;
use std::mem::size_of;
use std::result::Result as StdResult;

use itertools::Itertools;

use pretty::{Arena, DocAllocator, DocBuilder};

use base::symbol::Symbol;
use base::types::{ArcType, Type, TypeEnv};
use types::*;
use base::fnv::FnvMap;
use base::types::pretty_print::ident as pretty_ident;

use interner::InternedStr;
use compiler::DebugInfo;
use gc::{DataDef, Gc, GcPtr, Generation, Move, Traverseable, WriteOnly};
use array::Array;
use thread::{Status, Thread};
use {Error, Result, Variants};

use self::ValueRepr::{Closure, Float, Function, Int, PartialApplication, String};

mopafy!(Userdata);
pub trait Userdata: ::mopa::Any + Traverseable + fmt::Debug + Send + Sync {
    fn deep_clone(&self, deep_cloner: &mut Cloner) -> Result<GcPtr<Box<Userdata>>> {
        let _ = deep_cloner;
        Err(Error::Message("Userdata cannot be cloned".into()))
    }
}

impl PartialEq for Userdata {
    fn eq(&self, other: &Userdata) -> bool {
        self as *const _ == other as *const _
    }
}

pub(crate) type VariantIter<'a> =
    ::std::iter::Map<::std::slice::Iter<'a, Value>, fn(&'a Value) -> Variants<'a>>;

pub(crate) fn variant_iter<'a>(xs: &'a [Value]) -> VariantIter<'a> {
    xs.iter().map(|v| unsafe { Variants::new(v) })
}

#[derive(PartialEq)]
#[repr(C)]
pub struct ClosureData {
    pub(crate) function: GcPtr<BytecodeFunction>,
    pub(crate) upvars: Array<Value>,
}

impl fmt::Debug for ClosureData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("ClosureData")
            .field("function", &self.function.name)
            .field("upvars", &self.upvars)
            .finish()
    }
}

impl Traverseable for ClosureData {
    fn traverse(&self, gc: &mut Gc) {
        self.function.traverse(gc);
        self.upvars.traverse(gc);
    }
}

pub(crate) struct ClosureDataDef<'b>(pub GcPtr<BytecodeFunction>, pub &'b [Value]);
impl<'b> Traverseable for ClosureDataDef<'b> {
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc);
        self.1.traverse(gc);
    }
}

unsafe impl<'b> DataDef for ClosureDataDef<'b> {
    type Value = ClosureData;
    fn size(&self) -> usize {
        size_of::<ClosureData>() + self.1.len() * size_of::<Value>()
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
        size_of::<ClosureData>() + size_of::<Value>() * self.1
    }
    fn initialize<'w>(self, mut result: WriteOnly<'w, ClosureData>) -> &'w mut ClosureData {
        use std::ptr;
        unsafe {
            let result = &mut *result.as_mut_ptr();
            result.function = self.0;
            result.upvars.set_len(self.1);
            for var in &mut result.upvars {
                ptr::write(var, Value::from(Int(0)));
            }
            result
        }
    }
}

#[derive(Debug, PartialEq)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "::serialization::DeSeed"))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "::serialization::SeSeed"))]
pub struct BytecodeFunction {
    #[cfg_attr(feature = "serde_derive", serde(state_with = "::serialization::symbol"))]
    pub name: Symbol,
    pub args: VmIndex,
    pub max_stack_size: VmIndex,
    pub instructions: Vec<Instruction>,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub inner_functions: Vec<GcPtr<BytecodeFunction>>,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub strings: Vec<InternedStr>,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub records: Vec<Vec<InternedStr>>,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub debug_info: DebugInfo,
}

impl Traverseable for BytecodeFunction {
    fn traverse(&self, gc: &mut Gc) {
        self.inner_functions.traverse(gc);
    }
}

#[derive(Debug)]
#[repr(C)]
pub struct DataStruct {
    tag: VmTag,
    pub(crate) fields: Array<Value>,
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

impl DataStruct {
    pub fn record_bit() -> VmTag {
        1 << ((size_of::<VmTag>() * 8) - 1)
    }

    pub fn tag(&self) -> VmTag {
        self.tag & !Self::record_bit()
    }

    pub fn is_record(&self) -> bool {
        (self.tag & Self::record_bit()) != 0
    }
}

impl GcPtr<DataStruct> {
    pub(crate) fn get(&self, vm: &Thread, field: &str) -> Result<Option<Variants>> {
        use thread::ThreadInternal;

        let field = vm.global_env().intern(field)?;
        Ok(self.get_field(field))
    }

    pub(crate) fn get_field(&self, field: InternedStr) -> Option<Variants> {
        self.field_map()
            .get(&field)
            .map(|offset| unsafe { Variants::new(&self.fields[*offset as usize]) })
    }
}

/// Definition for data values in the VM
pub(crate) struct Def<'b> {
    pub tag: VmTag,
    pub elems: &'b [Value],
}
unsafe impl<'b> DataDef for Def<'b> {
    type Value = DataStruct;
    fn size(&self) -> usize {
        size_of::<DataStruct>() + size_of::<Value>() * self.elems.len()
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

pub(crate) struct RecordDef<'b> {
    pub elems: &'b [Value],
    pub fields: &'b [InternedStr],
}

unsafe impl<'b> DataDef for RecordDef<'b> {
    type Value = DataStruct;
    fn size(&self) -> usize {
        size_of::<DataStruct>() + size_of::<Value>() * self.elems.len()
    }
    fn initialize<'w>(self, mut result: WriteOnly<'w, DataStruct>) -> &'w mut DataStruct {
        unsafe {
            let result = &mut *result.as_mut_ptr();
            result.tag = 1 << ((size_of::<VmTag>() * 8) - 1);
            result.fields.initialize(self.elems.iter().cloned());
            result
        }
    }
    fn fields(&self) -> Option<&[InternedStr]> {
        Some(self.fields)
    }
}

impl<'b> Traverseable for RecordDef<'b> {
    fn traverse(&self, gc: &mut Gc) {
        self.elems.traverse(gc);
    }
}

mod gc_str {
    use super::ValueArray;
    use gc::{Gc, GcPtr, Generation, Traverseable};

    use std::fmt;
    use std::str;
    use std::ops::Deref;

    #[derive(Copy, Clone, PartialEq)]
    pub struct GcStr(GcPtr<ValueArray>);

    impl fmt::Debug for GcStr {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            f.debug_tuple("GcStr").field(&&**self).finish()
        }
    }

    impl Eq for GcStr {}

    impl GcStr {
        pub fn from_utf8(array: GcPtr<ValueArray>) -> Result<GcStr, ()> {
            unsafe {
                if array
                    .as_slice::<u8>()
                    .and_then(|bytes| str::from_utf8(bytes).ok())
                    .is_some()
                {
                    Ok(GcStr::from_utf8_unchecked(array))
                } else {
                    Err(())
                }
            }
        }
        pub unsafe fn from_utf8_unchecked(array: GcPtr<ValueArray>) -> GcStr {
            GcStr(array)
        }

        pub fn into_inner(self) -> GcPtr<ValueArray> {
            self.0
        }

        pub fn generation(&self) -> Generation {
            self.0.generation()
        }
    }

    impl Deref for GcStr {
        type Target = str;

        fn deref(&self) -> &str {
            unsafe { str::from_utf8_unchecked(self.0.as_slice::<u8>().unwrap()) }
        }
    }

    impl Traverseable for GcStr {
        fn traverse(&self, gc: &mut Gc) {
            self.0.traverse(gc)
        }
    }
}
pub use self::gc_str::GcStr;

#[derive(Copy, Clone, PartialEq)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "::serialization::DeSeed"))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "::serialization::SeSeed"))]
pub(crate) enum ValueRepr {
    Byte(u8),
    Int(VmInt),
    Float(f64),
    String(#[cfg_attr(feature = "serde_derive", serde(deserialize_state))] GcStr),
    Tag(VmTag),
    Data(
        #[cfg_attr(feature = "serde_derive",
                   serde(deserialize_state_with = "::serialization::gc::deserialize_data"))]
        #[cfg_attr(feature = "serde_derive", serde(serialize_state))]
        GcPtr<DataStruct>,
    ),
    Array(
        #[cfg_attr(feature = "serde_derive",
                   serde(deserialize_state_with = "::serialization::gc::deserialize_array"))]
        #[cfg_attr(feature = "serde_derive", serde(serialize_state))]
        GcPtr<ValueArray>,
    ),
    Function(#[cfg_attr(feature = "serde_derive", serde(state))] GcPtr<ExternFunction>),
    Closure(
        #[cfg_attr(feature = "serde_derive", serde(state_with = "::serialization::closure"))]
        GcPtr<ClosureData>,
    ),
    PartialApplication(
        #[cfg_attr(feature = "serde_derive",
                   serde(deserialize_state_with = "::serialization::deserialize_application"))]
        #[cfg_attr(feature = "serde_derive", serde(serialize_state))]
        GcPtr<PartialApplicationData>,
    ),
    // TODO Implement serializing of userdata
    #[cfg_attr(feature = "serde_derive", serde(skip_deserializing))]
    Userdata(
        #[cfg_attr(feature = "serde_derive",
                   serde(serialize_with = "::serialization::serialize_userdata"))]
        GcPtr<Box<Userdata>>,
    ),
    #[cfg_attr(feature = "serde_derive", serde(skip_deserializing))]
    #[cfg_attr(feature = "serde_derive", serde(skip_serializing))]
    Thread(#[cfg_attr(feature = "serde_derive", serde(deserialize_state))] GcPtr<Thread>),
}

// FIXME Remove Clone to make it harder to create unrooted values
#[derive(PartialEq, Clone)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "::serialization::DeSeed"))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "::serialization::SeSeed"))]
pub struct Value(#[cfg_attr(feature = "serde_derive", serde(state))] ValueRepr);

impl From<ValueRepr> for Value {
    #[inline]
    fn from(x: ValueRepr) -> Value {
        Value(x)
    }
}

impl Value {
    pub fn int(i: VmInt) -> Value {
        Value(ValueRepr::Int(i))
    }
    pub fn array(array: GcPtr<ValueArray>) -> Value {
        Value(ValueRepr::Array(array))
    }

    pub fn tag(tag: VmTag) -> Value {
        Value(ValueRepr::Tag(tag))
    }

    pub(crate) fn get_repr(&self) -> ValueRepr {
        self.0
    }

    pub fn generation(&self) -> Generation {
        match self.get_repr() {
            String(p) => p.generation(),
            ValueRepr::Data(p) => p.generation(),
            Function(p) => p.generation(),
            Closure(p) => p.generation(),
            ValueRepr::Array(p) => p.generation(),
            PartialApplication(p) => p.generation(),
            ValueRepr::Userdata(p) => p.generation(),
            ValueRepr::Thread(p) => p.generation(),
            ValueRepr::Tag(_) | ValueRepr::Byte(_) | Int(_) | Float(_) => Generation::default(),
        }
    }
}

#[derive(PartialEq, Copy, Clone, PartialOrd)]
enum Prec {
    Top,
    Constructor,
}
use self::Prec::*;

pub struct ValuePrinter<'a> {
    pub typ: &'a ArcType,
    pub env: &'a TypeEnv,
    pub value: Variants<'a>,
    pub max_level: i32,
    pub width: usize,
}

impl<'t> ValuePrinter<'t> {
    pub fn new(env: &'t TypeEnv, typ: &'t ArcType, value: Variants<'t>) -> ValuePrinter<'t> {
        ValuePrinter {
            typ,
            env,
            value,
            max_level: 50,
            width: 80,
        }
    }

    pub fn max_level(&mut self, max_level: i32) -> &mut ValuePrinter<'t> {
        self.max_level = max_level;
        self
    }

    pub fn width(&mut self, width: usize) -> &mut ValuePrinter<'t> {
        self.width = width;
        self
    }
}

const INDENT: usize = 4;

struct InternalPrinter<'a, 't> {
    typ: &'t ArcType,
    env: &'t TypeEnv,
    arena: &'a Arena<'a>,
    prec: Prec,
    level: i32,
}

impl<'a> fmt::Display for ValuePrinter<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let arena = Arena::new();
        let mut s = Vec::new();
        InternalPrinter {
            typ: self.typ,
            env: self.env,
            arena: &arena,
            prec: Top,
            level: self.max_level,
        }.pretty(self.value)
            .group()
            .1
            .render(self.width, &mut s)
            .map_err(|_| fmt::Error)?;
        write!(f, "{}", ::std::str::from_utf8(&s).expect("utf-8"))
    }
}

impl<'a, 't> InternalPrinter<'a, 't> {
    fn pretty(&self, value: Variants) -> DocBuilder<'a, Arena<'a>> {
        use std::iter;

        let arena = self.arena;
        match value.0 {
            _ if self.level == 0 => arena.text(".."),
            ValueRepr::String(s) => arena.text(format!("{:?}", &s[..])),
            ValueRepr::Data(ref data) => self.pretty_data(data.tag(), variant_iter(&data.fields)),
            ValueRepr::Tag(tag) => self.pretty_data(tag, iter::empty()),
            ValueRepr::Function(ref function) => chain![arena;
                    "<extern ",
                    function.id.declared_name().to_string(),
                    ">"
                ],
            ValueRepr::Closure(ref closure) => chain![arena;
                    "<",
                    arena.text(closure.function.name.declared_name().to_string()),
                    arena.concat(variant_iter(&closure.upvars).zip(&closure.function.debug_info.upvars)
                        .map(|(field, info)| {
                            chain![arena;
                                arena.space(),
                                info.name.clone(),
                                ":",
                                arena.space(),
                                self.p(&info.typ, Top).pretty(field)
                            ]
                        }).intersperse(arena.text(","))).nest(INDENT),
                    ">"
                ],
            ValueRepr::Array(ref array) => chain![arena;
                    "[",
                    arena.concat(array.iter().map(|field| {
                        match **self.typ {
                            Type::App(_, ref args) => self.p(&args[0], Top).pretty(field),
                            _ => arena.text(format!("{:?}", field)),
                        }
                    }).intersperse(arena.text(",").append(arena.space())))
                        .nest(INDENT),
                    "]"
                ],
            ValueRepr::PartialApplication(p) => arena.text(format!("{:?}", p)),
            ValueRepr::Userdata(ref data) => arena.text(format!("{:?}", data)),
            ValueRepr::Thread(thread) => arena.text(format!("{:?}", thread)),
            ValueRepr::Byte(b) => arena.text(format!("{}", b)),
            ValueRepr::Int(i) => {
                use base::types::BuiltinType;
                match **self.typ {
                    Type::Builtin(BuiltinType::Int) => arena.text(format!("{}", i)),
                    Type::Builtin(BuiltinType::Char) => match ::std::char::from_u32(i as u32) {
                        Some('"') => arena.text(format!("'{}'", '"')),
                        Some(c) => arena.text(format!("'{}'", c.escape_default())),
                        None => ice!(
                            "Invalid character (code point {}) passed to pretty printing",
                            i
                        ),
                    },
                    _ => arena.text(format!("{}", i)),
                }
            }
            ValueRepr::Float(f) => arena.text(format!("{}", f)),
        }
    }

    fn pretty_data<'b, I>(&self, tag: VmTag, fields: I) -> DocBuilder<'a, Arena<'a>>
    where
        I: IntoIterator<Item = Variants<'b>>,
    {
        fn enclose<'a>(
            p: Prec,
            limit: Prec,
            arena: &'a Arena<'a>,
            doc: DocBuilder<'a, Arena<'a>>,
        ) -> DocBuilder<'a, Arena<'a>> {
            if p >= limit {
                chain![arena; "(", doc, ")"]
            } else {
                doc
            }
        }

        use base::resolve::remove_aliases_cow;
        use base::types::arg_iter;

        let typ = remove_aliases_cow(self.env, self.typ);
        let arena = self.arena;
        match **typ {
            Type::Record(ref row) => {
                let mut is_empty = true;
                let fields_doc = arena.concat(
                    fields
                        .into_iter()
                        .zip(row.row_iter())
                        .map(|(field, type_field)| {
                            is_empty = false;
                            chain![arena;
                                pretty_ident(arena, type_field.name.declared_name().to_string()),
                                ":",
                                chain![arena;
                                    arena.space(),
                                    self.p(&type_field.typ, Top).pretty(field),
                                    arena.text(",")
                                ].nest(INDENT)
                            ].group()
                        })
                        .intersperse(arena.space()),
                );
                chain![arena;
                            "{",
                            chain![arena;
                                arena.space(),
                                fields_doc
                            ].nest(INDENT),
                            if is_empty {
                                arena.nil()
                            } else {
                                arena.space()
                            },
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
                                    arena.space().append(self.p(typ, Constructor).pretty(field))
                                }))
                                .nest(INDENT)
                        ];
                if empty {
                    doc
                } else {
                    enclose(self.prec, Constructor, arena, doc)
                }
            }
            _ => chain![arena;
                        "{",
                        arena.concat(fields.into_iter().map(|field| {
                            arena.space().append(self.p(&Type::hole(), Top).pretty(field))
                        }).intersperse(arena.text(",")))
                            .nest(INDENT),
                        arena.space(),
                        "}"
                    ],
        }
    }

    fn p(&self, typ: &'t ArcType, prec: Prec) -> InternalPrinter<'a, 't> {
        InternalPrinter {
            typ: typ,
            env: self.env,
            arena: self.arena,
            prec: prec,
            level: self.level - 1,
        }
    }
}

#[derive(Copy, Clone, Debug)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "::serialization::DeSeed"))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "::serialization::SeSeed"))]
pub enum Callable {
    Closure(
        #[cfg_attr(feature = "serde_derive", serde(state_with = "::serialization::closure"))]
        GcPtr<ClosureData>,
    ),
    Extern(#[cfg_attr(feature = "serde_derive", serde(state))] GcPtr<ExternFunction>),
}

impl Callable {
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
            Callable::Extern(ref ext) => ext.traverse(gc),
        }
    }
}

#[derive(Debug)]
#[repr(C)]
#[cfg_attr(feature = "serde_derive", derive(SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "::serialization::SeSeed"))]
pub struct PartialApplicationData {
    #[cfg_attr(feature = "serde_derive", serde(serialize_state))]
    pub(crate) function: Callable,
    #[cfg_attr(feature = "serde_derive", serde(serialize_state))]
    pub(crate) args: Array<Value>,
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

pub(crate) struct PartialApplicationDataDef<'b>(pub Callable, pub &'b [Value]);
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
        size_of::<PartialApplicationData>() + size_of::<Value>() * self.1.len()
    }
    fn initialize<'w>(
        self,
        mut result: WriteOnly<'w, PartialApplicationData>,
    ) -> &'w mut PartialApplicationData {
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
        self.get_repr().traverse(gc)
    }
}
impl Traverseable for ValueRepr {
    fn traverse(&self, gc: &mut Gc) {
        match *self {
            String(ref data) => data.traverse(gc),
            ValueRepr::Data(ref data) => data.traverse(gc),
            ValueRepr::Array(ref data) => data.traverse(gc),
            Function(ref data) => data.traverse(gc),
            Closure(ref data) => data.traverse(gc),
            ValueRepr::Userdata(ref data) => data.traverse(gc),
            PartialApplication(ref data) => data.traverse(gc),
            ValueRepr::Thread(ref thread) => thread.traverse(gc),
            ValueRepr::Tag(_) | ValueRepr::Byte(_) | Int(_) | Float(_) => (),
        }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}
impl fmt::Debug for ValueRepr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        struct Level<'b>(i32, Variants<'b>);
        struct LevelSlice<I>(i32, I);

        impl<'b, I> fmt::Debug for LevelSlice<I>
        where
            I: Iterator<Item = Variants<'b>> + Clone,
        {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let level = self.0;
                let mut iter = self.1.clone();
                let first = iter.next();
                if level <= 0 || first.is_none() {
                    return Ok(());
                }
                write!(f, "{:?}", Level(level - 1, first.unwrap()))?;
                for v in iter {
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
                match (self.1).0 {
                    ValueRepr::Byte(i) => write!(f, "{:?}b", i),
                    ValueRepr::Int(i) => write!(f, "{:?}", i),
                    ValueRepr::Float(x) => write!(f, "{:?}f", x),
                    ValueRepr::String(x) => write!(f, "{:?}", &*x),
                    ValueRepr::Tag(tag) => write!(f, "{{{:?}: }}", tag),
                    ValueRepr::Data(ref data) => write!(
                        f,
                        "{{{:?}: {:?}}}",
                        data.tag,
                        LevelSlice(level - 1, variant_iter(&data.fields))
                    ),
                    ValueRepr::Array(ref array) => {
                        let mut first = true;
                        write!(f, "[")?;
                        for value in array.iter() {
                            if !first {
                                write!(f, ", ")?;
                            }
                            first = false;
                            write!(f, "{:?}", Level(level - 1, value))?;
                        }
                        write!(f, "]")
                    }
                    ValueRepr::Function(ref func) => write!(f, "<EXTERN {:?}>", &**func),
                    ValueRepr::Closure(ref closure) => {
                        let p: *const _ = &*closure.function;
                        write!(f, "<{:?} {:?}>", closure.function.name, p)
                    }
                    ValueRepr::PartialApplication(ref app) => {
                        let name = match app.function {
                            Callable::Closure(ref c) => &c.function.name,
                            Callable::Extern(ref e) => &e.id,
                        };
                        write!(
                            f,
                            "<App {:?}, {:?}>",
                            name,
                            LevelSlice(level - 1, variant_iter(&app.args))
                        )
                    }
                    ValueRepr::Userdata(ref data) => write!(f, "<Userdata {:?}>", &**data),
                    ValueRepr::Thread(_) => write!(f, "<thread>"),
                }
            }
        }
        unsafe { write!(f, "{:?}", Level(7, Variants::new(&Value(*self)))) }
    }
}

#[cfg_attr(feature = "serde_derive", derive(SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "::serialization::SeSeed"))]
pub struct ExternFunction {
    #[cfg_attr(feature = "serde_derive",
               serde(serialize_state_with = "::serialization::symbol::serialize"))]
    pub id: Symbol,
    pub args: VmIndex,
    #[cfg_attr(feature = "serde_derive", serde(skip_serializing))]
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
    fn eq(&self, other: &ExternFunction) -> bool {
        self.id == other.id && self.args == other.args
            && self.function as usize == other.function as usize
    }
}

impl fmt::Debug for ExternFunction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // read the v-table pointer of the Fn(..) type and print that
        let p: *const () = unsafe { ::std::mem::transmute(self.function) };
        write!(f, "{} {:?}", self.id, p)
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

        unsafe impl DataDef for Vec<$id> {
            type Value = ValueArray;
            fn size(&self) -> usize {
                DataDef::size(&&self[..])
            }
            fn initialize<'w>(self, result: WriteOnly<'w, ValueArray>) -> &'w mut ValueArray {
                DataDef::initialize(&self[..], result)
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
    GcStr, Repr::String,
    GcPtr<ValueArray>, Repr::Array,
    Value, Repr::Unknown,
    GcPtr<Box<Userdata>>, Repr::Userdata,
    GcPtr<Thread>, Repr::Thread
}

impl Repr {
    fn from_value(value: &Value) -> Repr {
        match value.get_repr() {
            ValueRepr::Byte(_) => Repr::Byte,
            ValueRepr::Int(_) => Repr::Int,
            ValueRepr::Float(_) => Repr::Float,
            ValueRepr::String(_) => Repr::String,
            ValueRepr::Array(_) => Repr::Array,
            ValueRepr::Data(_)
            | ValueRepr::Tag(_)
            | ValueRepr::Function(_)
            | ValueRepr::Closure(_)
            | ValueRepr::PartialApplication(_) => Repr::Unknown,
            ValueRepr::Userdata(_) => Repr::Userdata,
            ValueRepr::Thread(_) => Repr::Thread,
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
                    Repr::String => $f(array.unsafe_array::<GcStr>()),
                    Repr::Array => $f(array.unsafe_array::<GcPtr<ValueArray>>()),
                    Repr::Unknown => $f(array.unsafe_array::<Value>()),
                    Repr::Userdata => $f(array.unsafe_array::<GcPtr<Box<Userdata>>>()),
                    Repr::Thread => $f(array.unsafe_array::<GcPtr<Thread>>()),
                }
            }
        }
    }
}

#[repr(C)]
pub struct ValueArray {
    repr: Repr,
    array: Array<Value>,
}

impl fmt::Debug for ValueArray {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("ValueArray")
            .field("repr", &self.repr)
            .field("array", on_array!(self, |x| x as &fmt::Debug))
            .finish()
    }
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
    type Item = Variants<'a>;
    fn next(&mut self) -> Option<Self::Item> {
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
    pub fn get(&self, index: usize) -> Variants {
        unsafe {
            let value = match self.repr {
                Repr::Byte => ValueRepr::Byte(self.unsafe_get(index)),
                Repr::Int => ValueRepr::Int(self.unsafe_get(index)),
                Repr::Float => ValueRepr::Float(self.unsafe_get(index)),
                Repr::String => ValueRepr::String(self.unsafe_get(index)),
                Repr::Array => ValueRepr::Array(self.unsafe_get(index)),
                Repr::Unknown => self.unsafe_get(index),
                Repr::Userdata => ValueRepr::Userdata(self.unsafe_get(index)),
                Repr::Thread => ValueRepr::Thread(self.unsafe_get(index)),
            };
            Variants::with_root(value, self)
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
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

    pub(crate) unsafe fn initialize<'a, I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = Variants<'a>>,
    {
        let iter = iter.into_iter().map(|v| v.0);

        macro_rules! initialize_variants {
            ($($id: ident)+) => {
        match self.repr {
                    $(Repr::$id => {
                let iter = iter.map(|v| match v {
                            ValueRepr::$id(x) => x,
                    _ => unreachable!(),
                });
                self.unsafe_array_mut().initialize(iter);
                    })+
            Repr::Unknown => {
                self.unsafe_array_mut().initialize(iter);
            }
            }
            }
        }

        initialize_variants! { Byte Int Float String Array Userdata Thread }
    }

    pub fn as_slice<T: ArrayRepr>(&self) -> Option<&[T]> {
        unsafe {
            // If the array is empty then it may not have the correct type representation set since
            // there was no value to take the correct representation from
            if T::matches(self.repr) || self.is_empty() {
                Some(self.unsafe_array::<T>())
            } else {
                None
            }
        }
    }

    unsafe fn unsafe_get<T: Copy>(&self, index: usize) -> T {
        ::std::mem::transmute::<&Array<_>, &Array<T>>(&self.array)[index]
    }

    unsafe fn unsafe_array<T>(&self) -> &Array<T> {
        ::std::mem::transmute::<&Array<_>, &Array<T>>(&self.array)
    }

    pub unsafe fn unsafe_array_mut<T>(&mut self) -> &mut Array<T> {
        ::std::mem::transmute::<&mut Array<_>, &mut Array<T>>(&mut self.array)
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
            on_array!(self, |array: &Array<_>| result
                .unsafe_array_mut()
                .initialize(array.iter().cloned()));
            result
        }
    }
}

pub(crate) struct ArrayDef<'b>(pub &'b [Value]);
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
            Some(value) => Repr::from_value(value).size_of() * self.0.len(),
            None => 0,
        };
        size_of::<ValueArray>() + size
    }
    fn initialize<'w>(self, mut result: WriteOnly<'w, ValueArray>) -> &'w mut ValueArray {
        unsafe {
            let result = &mut *result.as_mut_ptr();
            match self.0.first() {
                Some(value) => {
                    result.repr = Repr::from_value(value);
                    result.initialize(variant_iter(self.0))
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

pub struct Cloner<'t> {
    visited: FnvMap<*const (), ValueRepr>,
    thread: &'t Thread,
    gc: &'t mut Gc,
    receiver_generation: Generation,
}

impl<'t> Cloner<'t> {
    pub fn new(thread: &'t Thread, gc: &'t mut Gc) -> Cloner<'t> {
        Cloner {
            visited: FnvMap::default(),
            thread: thread,
            receiver_generation: gc.generation(),
            gc: gc,
        }
    }

    pub fn thread(&self) -> &'t Thread {
        self.thread
    }

    pub fn gc(&mut self) -> &mut Gc {
        self.gc
    }

    /// Deep clones the entire value doing no sharing
    pub fn force_full_clone(&mut self) -> &mut Self {
        self.receiver_generation = Generation::disjoint();
        self
    }

    pub(crate) fn deep_clone(&mut self, value: &Value) -> Result<Value> {
        // Only need to clone values which belong to a younger generation than the gc that the new
        // value will live in
        if self.receiver_generation
            .can_contain_values_from(value.generation())
        {
            return Ok(value.clone());
        }
        let result = match value.0 {
            String(data) => self.deep_clone_str(data),
            ValueRepr::Data(data) => self.deep_clone_data(data).map(ValueRepr::Data),
            ValueRepr::Array(data) => self.deep_clone_array(data).map(ValueRepr::Array),
            Closure(data) => self.deep_clone_closure(data).map(ValueRepr::Closure),
            PartialApplication(data) => {
                self.deep_clone_app(data).map(ValueRepr::PartialApplication)
            }
            Function(f) => self.gc
                .alloc(Move(ExternFunction::clone(&f)))
                .map(ValueRepr::Function),
            ValueRepr::Tag(i) => Ok(ValueRepr::Tag(i)),
            ValueRepr::Byte(i) => Ok(ValueRepr::Byte(i)),
            Int(i) => Ok(Int(i)),
            Float(f) => Ok(Float(f)),
            ValueRepr::Userdata(userdata) => userdata.deep_clone(self).map(ValueRepr::Userdata),
            ValueRepr::Thread(_) => Err(Error::Message("Threads cannot be deep cloned yet".into())),
        };
        result.map(Value::from)
    }

    fn deep_clone_ptr<T, A, R>(
        &mut self,
        value: GcPtr<T>,
        alloc: A,
    ) -> Result<StdResult<ValueRepr, R>>
    where
        A: FnOnce(&mut Gc, &T) -> Result<(ValueRepr, R)>,
    {
        let key = &*value as *const T as *const ();
        let new_ptr = match self.visited.entry(key) {
            Entry::Occupied(entry) => return Ok(Ok(*entry.get())),
            Entry::Vacant(entry) => {
                // FIXME Should allocate the real `Value` and possibly fill it later
                let (value, new_ptr) = alloc(self.gc, &value)?;
                entry.insert(value);
                new_ptr
            }
        };
        Ok(Err(new_ptr))
    }

    fn deep_clone_str(&mut self, data: GcStr) -> Result<ValueRepr> {
        unsafe {
            Ok(self.deep_clone_ptr(data.into_inner(), |gc, data| {
                let ptr = GcStr::from_utf8_unchecked(gc.alloc(data)?);
                Ok((String(ptr), ptr))
            })?
                .unwrap_or_else(String))
        }
    }
    fn deep_clone_data(&mut self, data_ptr: GcPtr<DataStruct>) -> Result<GcPtr<DataStruct>> {
        let result = self.deep_clone_ptr(data_ptr, |gc, data| {
            let ptr = if data.is_record() {
                gc.alloc(RecordDef {
                    fields: data_ptr.field_names(),
                    elems: &data.fields,
                })?
            } else {
                gc.alloc(Def {
                    tag: data.tag,
                    elems: &data.fields,
                })?
            };
            Ok((ValueRepr::Data(ptr), ptr))
        })?;
        match result {
            Ok(ValueRepr::Data(ptr)) => Ok(ptr),
            Ok(_) => unreachable!(),
            Err(mut new_data) => {
                {
                    let new_fields = unsafe { &mut new_data.as_mut().fields };
                    for (new, old) in new_fields.iter_mut().zip(&data_ptr.fields) {
                        *new = self.deep_clone(old)?;
                    }
                }
                Ok(new_data)
            }
        }
    }

    fn deep_clone_userdata(&mut self, ptr: GcPtr<Box<Userdata>>) -> Result<GcPtr<Box<Userdata>>> {
        ptr.deep_clone(self)
    }

    fn deep_clone_array(&mut self, array: GcPtr<ValueArray>) -> Result<GcPtr<ValueArray>> {
        unsafe fn deep_clone_elems<T, F>(
            mut new_array: GcPtr<ValueArray>,
            mut deep_clone: F,
        ) -> Result<()>
        where
            F: FnMut(&T) -> Result<T>,
        {
            let new_array = new_array.as_mut().unsafe_array_mut::<T>();
            for field in new_array.iter_mut() {
                *field = deep_clone(field)?;
            }
            Ok(())
        }

        let result = self.deep_clone_ptr(array, |gc, array| {
            let ptr = gc.alloc(array)?;
            Ok((ValueRepr::Array(ptr), ptr))
        })?;
        match result {
            Ok(ValueRepr::Array(ptr)) => Ok(ptr),
            Ok(_) => unreachable!(),
            Err(new_array) => {
                unsafe {
                    match new_array.repr() {
                        Repr::Byte | Repr::Int | Repr::Float | Repr::String => Ok(()),
                        Repr::Array => deep_clone_elems(new_array, |e| self.deep_clone_array(*e)),
                        Repr::Unknown => deep_clone_elems(new_array, |e| self.deep_clone(e)),
                        Repr::Userdata => {
                            deep_clone_elems(new_array, |e| self.deep_clone_userdata(*e))
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

    fn deep_clone_closure(&mut self, data: GcPtr<ClosureData>) -> Result<GcPtr<ClosureData>> {
        let result = self.deep_clone_ptr(data, |gc, data| {
            debug_assert!(data.function.generation().is_root());

            let ptr = gc.alloc(ClosureDataDef(data.function, &data.upvars))?;
            Ok((Closure(ptr), ptr))
        })?;
        match result {
            Ok(ValueRepr::Closure(ptr)) => Ok(ptr),
            Ok(_) => unreachable!(),
            Err(mut new_data) => {
                {
                    let new_upvars = unsafe { &mut new_data.as_mut().upvars };
                    for (new, old) in new_upvars.iter_mut().zip(&data.upvars) {
                        *new = self.deep_clone(old)?;
                    }
                }
                Ok(new_data)
            }
        }
    }
    fn deep_clone_app(
        &mut self,
        data: GcPtr<PartialApplicationData>,
    ) -> Result<GcPtr<PartialApplicationData>> {
        let function = match data.function {
            Callable::Closure(closure) => Callable::Closure(self.deep_clone_closure(closure)?),
            Callable::Extern(ext) => {
                Callable::Extern(self.gc.alloc(Move(ExternFunction::clone(&ext)))?)
            }
        };

        let result = self.deep_clone_ptr(data, |gc, data| {
            let ptr = gc.alloc(PartialApplicationDataDef(function, &data.args))?;
            Ok((ValueRepr::PartialApplication(ptr), ptr))
        })?;
        match result {
            Ok(ValueRepr::PartialApplication(ptr)) => Ok(ptr),
            Ok(_) => unreachable!(),
            Err(mut new_data) => {
                {
                    let new_args = unsafe { &mut new_data.as_mut().args };
                    for (new, old) in new_args.iter_mut().zip(&data.args) {
                        *new = self.deep_clone(old)?;
                    }
                }
                Ok(new_data)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use gc::{Gc, Generation};
    use types::VmInt;

    use base::kind::{ArcKind, KindEnv};
    use base::types::{Alias, ArcType, Field, Type, TypeEnv};
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
    }

    #[test]
    fn pretty_variant() {
        let mut gc = Gc::new(Generation::default(), usize::max_value());

        let list = Symbol::from("List");
        let typ: ArcType = Type::variant(vec![
            Field {
                name: Symbol::from("Cons"),
                typ: Type::function(
                    vec![Type::int(), Type::ident(list.clone())],
                    Type::ident(list.clone()),
                ),
            },
            Field {
                name: Symbol::from("Nil"),
                typ: Type::ident(list.clone()),
            },
        ]);

        let env = MockEnv(Some(Alias::new(list.clone(), typ.clone())));

        let nil = Value::tag(1);
        assert_eq!(
            format!(
                "{}",
                ValuePrinter::new(&env, &typ, unsafe { Variants::new(&nil) })
            ),
            "Nil"
        );
        let list1 = Value::from(ValueRepr::Data(gc.alloc(Def {
            tag: 0,
            elems: &[Value::from(ValueRepr::Int(123)), nil],
        }).unwrap()));
        assert_eq!(
            format!(
                "{}",
                ValuePrinter::new(&env, &typ, unsafe { Variants::new(&list1) })
            ),
            "Cons 123 Nil"
        );
        let list2 = Value::from(ValueRepr::Data(gc.alloc(Def {
            tag: 0,
            elems: &[ValueRepr::Int(0).into(), list1],
        }).unwrap()));
        assert_eq!(
            format!(
                "{}",
                ValuePrinter::new(&env, &typ, unsafe { Variants::new(&list2) })
            ),
            "Cons 0 (Cons 123 Nil)"
        );
    }

    #[test]
    fn pretty_array() {
        let mut gc = Gc::new(Generation::default(), usize::max_value());

        let typ = Type::array(Type::int());

        let env = MockEnv(None);

        let nil = Value::array(gc.alloc(&[1 as VmInt, 2, 3][..]).unwrap());
        assert_eq!(
            format!(
                "{}",
                ValuePrinter::new(&env, &typ, unsafe { Variants::new(&nil) })
            ),
            "[1, 2, 3]"
        );
    }

    #[test]
    fn closure_data_upvars_location() {
        use std::mem;
        use std::ptr;

        unsafe {
            let p: *const ClosureData = ptr::null();
            assert_eq!(p as *const u8, &(*p).function as *const _ as *const u8);
            assert!((p as *const u8).offset(mem::size_of::<*const ()>() as isize) != ptr::null());
        }
    }
}
