use std::cell::{Cell, RefCell, Ref};
use std::error::Error as StdError;
use std::fmt;
use std::intrinsics::type_name;
use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::cmp::Ordering;
use std::ops::Deref;
use std::rc::Rc;
use base::ast;
use base::ast::{Type, ASTType};
use check::typecheck::{Typecheck, TypeEnv, TypeInfos, Typed, TcIdent, TcType};
use types::*;
use base::interner::{Interner, InternedStr};
use base::gc::{Gc, GcPtr, Traverseable, DataDef, Move};
use compiler::{Compiler, CompiledFunction, Variable, CompilerEnv};
use fixed::*;
use api::define_function;
use lazy::Lazy;

use self::Named::*;

use self::Value::{
    Int,
    Float,
    String,
    Data,
    Function,
    PartialApplication,
    Closure,
    TraitObject,
    Userdata,
};


pub use stack::{Stack, StackFrame};

#[derive(Copy, Clone, Debug)]
pub struct Userdata_ {
    pub data: GcPtr<Box<Any>>
}

impl Userdata_ {
    pub fn new<T: Any>(vm: &VM, v: T) -> Userdata_ {
        let v: Box<Any> = Box::new(v);
        Userdata_ { data: vm.gc.borrow_mut().alloc(Move(v)) }
    }
    fn ptr(&self) -> *const () {
        let p: *const _ = &*self.data;
        p as *const ()
    }
}
impl PartialEq for Userdata_ {
    fn eq(&self, o: &Userdata_) -> bool {
        self.ptr() == o.ptr()
    }
}

#[derive(Debug)]
pub struct ClosureData<'a> {
    pub function: GcPtr<BytecodeFunction>,
    pub upvars: [Cell<Value<'a>>]
}

impl <'a> PartialEq for ClosureData<'a> {
    fn eq(&self, _: &ClosureData<'a>) -> bool {
        false
    }
}

impl <'a> Traverseable for ClosureData<'a> {
    fn traverse(&self, gc: &mut Gc) {
        self.function.traverse(gc);
        self.upvars.traverse(gc);
    }
}

struct ClosureDataDef<'a: 'b, 'b>(GcPtr<BytecodeFunction>, &'b [Value<'a>]);
impl <'a, 'b> Traverseable for ClosureDataDef<'a, 'b> {
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc);
        self.1.traverse(gc);
    }
}

unsafe impl <'a: 'b, 'b> DataDef for ClosureDataDef<'a, 'b> {
    type Value = ClosureData<'a>;
    fn size(&self) -> usize {
        use std::mem::size_of;
        size_of::<GcPtr<BytecodeFunction>>() + size_of::<Cell<Value<'a>>>() * self.1.len()
    }
    fn initialize(self, result: *mut ClosureData<'a>) {
        let result = unsafe { &mut *result };
        result.function = self.0;
        for (field, value) in result.upvars.iter().zip(self.1.iter()) {
            field.set(value.clone());
        }
    }
    fn make_ptr(&self, ptr: *mut ()) -> *mut ClosureData<'a> {
        let x = unsafe {
            use std::raw::Slice;
            let x = Slice { data: &*ptr, len: self.1.len() };
            ::std::mem::transmute(x)
        };
        x
    }
}

#[derive(Debug)]
pub struct BytecodeFunction {
    name: Option<InternedStr>,
    args: VMIndex,
    instructions: Vec<Instruction>,
    inner_functions: Vec<GcPtr<BytecodeFunction>>,
    strings: Vec<InternedStr>
}

impl BytecodeFunction {
    pub fn empty() -> BytecodeFunction {
        BytecodeFunction { name: None, args: 0, instructions: Vec::new(), inner_functions: Vec::new(), strings: Vec::new() }
    }

    pub fn new(gc: &mut Gc, f: CompiledFunction) -> GcPtr<BytecodeFunction> {
        let CompiledFunction { id, args, instructions, inner_functions, strings, .. } = f;
        let fs = inner_functions.into_iter()
            .map(|inner| BytecodeFunction::new(gc, inner))
            .collect();
        gc.alloc(Move(BytecodeFunction {
            name: Some(id),
            args: args,
            instructions: instructions,
            inner_functions: fs,
            strings: strings
        }))
    }
}

impl Traverseable for BytecodeFunction {
    fn traverse(&self, gc: &mut Gc) {
        self.inner_functions.traverse(gc);
    }
}

pub struct DataStruct<'a> {
    pub tag: VMTag,
    pub fields: [Cell<Value<'a>>]
}

impl <'a> Traverseable for DataStruct<'a> {
    fn traverse(&self, gc: &mut Gc) {
        self.fields.traverse(gc);
    }
}

impl <'a> PartialEq for DataStruct<'a> {
    fn eq(&self, other: &DataStruct<'a>) -> bool {
        self.tag == other.tag && self.fields == other.fields
    }
}

pub type VMInt = isize;

#[derive(Copy, Clone, PartialEq)]
pub enum Value<'a> {
    Int(VMInt),
    Float(f64),
    String(GcPtr<str>),
    Data(GcPtr<DataStruct<'a>>),
    Function(GcPtr<ExternFunction<'a>>),
    Closure(GcPtr<ClosureData<'a>>),
    PartialApplication(GcPtr<PartialApplicationData<'a>>),
    TraitObject(GcPtr<DataStruct<'a>>),
    Userdata(Userdata_),
    Lazy(GcPtr<Lazy<'a>>)
}

#[derive(Copy, Clone, Debug)]
enum Callable<'a> {
    Closure(GcPtr<ClosureData<'a>>),
    Extern(GcPtr<ExternFunction<'a>>)
}

impl <'a> Callable<'a> {
    fn args(&self) -> VMIndex {
        match *self {
            Callable::Closure(ref closure) => closure.function.args,
            Callable::Extern(ref ext) => ext.args
        }
    }
}

impl <'a> PartialEq for Callable<'a> {
    fn eq(&self, _: &Callable<'a>) -> bool {
        false
    }
}

impl <'a> Traverseable for Callable<'a> {
    fn traverse(&self, gc: &mut Gc) {
        match *self {
            Callable::Closure(ref closure) => closure.traverse(gc),
            Callable::Extern(_) => ()
        }
    }
}

#[derive(Debug)]
pub struct PartialApplicationData<'a> {
    function: Callable<'a>,
    arguments: [Cell<Value<'a>>]
}

impl <'a> PartialEq for PartialApplicationData<'a> {
    fn eq(&self, _: &PartialApplicationData<'a>) -> bool {
        false
    }
}

impl <'a> Traverseable for PartialApplicationData<'a> {
    fn traverse(&self, gc: &mut Gc) {
        self.function.traverse(gc);
        self.arguments.traverse(gc);
    }
}

struct PartialApplicationDataDef<'a: 'b, 'b>(Callable<'a>, &'b [Value<'a>]);
impl <'a, 'b> Traverseable for PartialApplicationDataDef<'a, 'b> {
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc);
        self.1.traverse(gc);
    }
}
unsafe impl <'a: 'b, 'b> DataDef for PartialApplicationDataDef<'a, 'b> {
    type Value = PartialApplicationData<'a>;
    fn size(&self) -> usize {
        use std::mem::size_of;
        size_of::<Callable<'a>>() + size_of::<Cell<Value<'a>>>() * self.1.len()
    }
    fn initialize(self, result: *mut PartialApplicationData<'a>) {
        let result = unsafe { &mut *result };
        result.function = self.0;
        for (field, value) in result.arguments.iter().zip(self.1.iter()) {
            field.set(value.clone());
        }
    }
    fn make_ptr(&self, ptr: *mut ()) -> *mut PartialApplicationData<'a> {
        unsafe {
            use std::raw::Slice;
            let x = Slice { data: &*ptr, len: self.1.len() };
            ::std::mem::transmute(x)
        }
    }
}

impl <'a> PartialEq<Value<'a>> for Cell<Value<'a>> {
    fn eq(&self, other: &Value<'a>) -> bool {
        self.get() == *other
    }
}
impl <'a> PartialEq<Cell<Value<'a>>> for Value<'a> {
    fn eq(&self, other: &Cell<Value<'a>>) -> bool {
        *self == other.get()
    }
}

impl <'a> Traverseable for Value<'a> {
    fn traverse(&self, gc: &mut Gc) {
        match *self {
            String(ref data) => data.traverse(gc),
            Data(ref data) => data.traverse(gc),
            Function(ref data) => data.traverse(gc),
            Closure(ref data) => data.traverse(gc),
            TraitObject(ref data) => data.traverse(gc),
            Userdata(ref data) => data.data.traverse(gc),
            PartialApplication(ref data) => data.traverse(gc),
            Value::Lazy(ref lazy) => lazy.traverse(gc),
            Int(_) | Float(_) => ()
        }
    }
}

impl <'a> fmt::Debug for Value<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        struct Level<'a: 'b, 'b>(i32, &'b Value<'a>);
        struct LevelSlice<'a: 'b, 'b>(i32, &'b [Cell<Value<'a>>]);
        impl <'a, 'b> fmt::Debug for LevelSlice<'a, 'b> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let level = self.0;
                if level <= 0 { return Ok(()) }
                for v in self.1 {
                    try!(write!(f, "{:?}", Level(level - 1, &v.get())));
                }
                Ok(())
            }
        }
        impl <'a, 'b> fmt::Debug for Level<'a, 'b> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let level = self.0;
                if level <= 0 { return Ok(()) }
                match *self.1 {
                    Int(i) => write!(f, "{:?}", i),
                    Float(x) => write!(f, "{:?}f", x),
                    String(x) => write!(f, "{:?}", &*x),
                    Data(ref data) => {
                        write!(f, "{{{:?} {:?}}}", data.tag, LevelSlice(level - 1, &data.fields))
                    }
                    Function(ref func) => write!(f, "<{} {:?}>", func.id, &**func),
                    Closure(ref closure) => {
                        let p: *const _ = &*closure.function;
                        let name = match closure.function.name {
                            Some(ref name) => &name[..],
                            None => ""
                        };
                        write!(f, "<{:?} {:?} {:?}>", name, p, LevelSlice(level - 1, &closure.upvars))
                    }
                    PartialApplication(ref app) => {
                        let name = match app.function {
                            Callable::Closure(ref closure) => {
                                closure.function.name.as_ref().map(|n| &n[..])
                                    .unwrap_or("")
                            }
                            Callable::Extern(ref func) => &func.id[..],
                        };
                        write!(f, "<App {:?} {:?}>", name, LevelSlice(level - 1, &app.arguments))
                    }
                    TraitObject(ref object) => write!(f, "<{:?} {:?}>", object.tag, LevelSlice(level - 1, &object.fields)),
                    Userdata(ref data) => write!(f, "<Userdata {:?}>", data.ptr()),
                    Value::Lazy(_) => write!(f, "<lazy>"),
                }
            }
        }
        write!(f, "{:?}", Level(3, self))
    }
}

macro_rules! get_global {
    ($vm: ident, $i: expr) => (
        match $vm.globals[$i].value.get() {
            x => x
        }
    )
}

pub struct Root<'a, T: ?Sized + 'a> {
    roots: &'a RefCell<Vec<GcPtr<Traverseable + 'static>>>,
    ptr: *const T
}

impl <'a, T: ?Sized> Drop for Root<'a, T> {
    fn drop(&mut self) {
        self.roots.borrow_mut().pop();//TODO not safe if the root changes order of being dropped with another root
    }
}

impl <'a, T: ?Sized> Deref for Root<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.ptr }
    }
}

pub struct RootStr<'a>(Root<'a, str>);

impl <'a> Deref for RootStr<'a> {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

pub enum Status {
    Ok,
    Error
}

pub struct ExternFunction<'a> {
    id: InternedStr,
    args: VMIndex,
    function: Box<Fn(&VM<'a>) -> Status + 'static>
}

impl <'a> PartialEq for ExternFunction<'a> {
    fn eq(&self, _: &ExternFunction<'a>) -> bool { false }
}

impl <'a> fmt::Debug for ExternFunction<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let p: *const () = unsafe { ::std::mem::transmute_copy(& &*self.function) };
        write!(f, "{:?}", p)
    }
}

impl <'a> Traverseable for ExternFunction<'a> {
    fn traverse(&self, _: &mut Gc) { }
}

#[derive(Debug)]
pub struct Global<'a> {
    pub id: InternedStr,
    pub typ: TcType,
    pub value: Cell<Value<'a>>
}

impl <'a> Traverseable for Global<'a> {
    fn traverse(&self, gc: &mut Gc) {
        self.id.traverse(gc);
        self.value.traverse(gc);
    }
}

impl <'a> Typed for Global<'a> {
    type Id = InternedStr;
    fn env_type_of(&self, _: &TypeEnv) -> ASTType<InternedStr> {
        self.typ.clone()
    }
}

#[derive(Debug)]
enum Named {
    GlobalFn(usize)
}

pub struct VM<'a> {
    globals: FixedVec<Global<'a>>,
    type_infos: RefCell<TypeInfos>,
    typeids: FixedMap<TypeId, TcType>,
    pub interner: RefCell<Interner>,
    names: RefCell<HashMap<InternedStr, Named>>,
    pub gc: RefCell<Gc>,
    roots: RefCell<Vec<GcPtr<Traverseable>>>,
    //Since the vm will be retrieved often and the borrowing from a RefCell does not work
    //it needs to be in a unsafe cell
    pub stack: RefCell<Stack<'a>>
}

pub type VMResult<T> = Result<T, Error>;

#[derive(Debug)]
pub enum Error {
    Message(::std::string::String)
}

impl StdError for Error {
    fn description(&self) -> &str {
        "VM error"
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Message(ref msg) => msg.fmt(f)
        }
    }
}

#[derive(Debug)]
pub struct VMEnv<'a: 'b, 'b> {
    type_infos: Ref<'b, TypeInfos>,
    globals: &'b FixedVec<Global<'a>>,
    names: Ref<'b, HashMap<InternedStr, Named>>,
    io_arg: [ast::Generic<InternedStr>; 1]
}

impl <'a, 'b> CompilerEnv for VMEnv<'a, 'b> {
    fn find_var(&self, id: &InternedStr) -> Option<Variable> {
        match self.names.get(id) {
            Some(&GlobalFn(index)) if index < self.globals.len() => {
                let g = &self.globals[index];
                Some(Variable::Global(index as VMIndex, &g.typ))
            }
            _ => self.type_infos.find_var(id)
        }
    }
    fn find_field(&self, data_name: &InternedStr, field_name: &InternedStr) -> Option<VMIndex> {
        self.type_infos.id_to_type.get(data_name)
            .and_then(|&(_, ref typ)| {
                match **typ {
                    ast::Type::Record(ref fields) => {
                        fields.iter()
                            .enumerate()
                            .find(|&(_, f)| f.name == *field_name)
                            .map(|(i, _)| i as VMIndex)
                    }
                    _ => None
                }
            })
    }

    fn find_tag(&self, data_name: &InternedStr, ctor_name: &InternedStr) -> Option<VMTag> {
        match self.type_infos.id_to_type.get(data_name).map(|&(_, ref typ)| &**typ) {
            Some(&Type::Variants(ref ctors)) => {
                ctors.iter()
                    .enumerate()
                    .find(|&(_, c)| c.0 == *ctor_name)
                    .map(|(i, _)| i as VMIndex)
            }
            _ => None
        }
    }
}

impl <'a, 'b> TypeEnv for VMEnv<'a, 'b> {
    fn find_type(&self, id: &InternedStr) -> Option<&TcType> {
        match self.names.get(id) {
            Some(&GlobalFn(index)) if index < self.globals.len() => {
                let g = &self.globals[index];
                Some(&g.typ)
            }
            _ => {
                self.type_infos.id_to_type.values()
                    .filter_map(|tuple| match *tuple.1 {
                        Type::Variants(ref ctors) => ctors.iter().find(|ctor| ctor.0 == *id).map(|t| &t.1),
                        _ => None
                    })
                    .next()
                    .map(|ctor| ctor)
            }
        }
    }
    fn find_type_info(&self, id: &InternedStr) -> Option<(&[ast::Generic<InternedStr>], Option<&TcType>)> {
        self.type_infos.find_type_info(id)
            .or_else(|| {
                if &id[..] == "IO" {
                    Some((&self.io_arg, None))
                }
                else {
                    None
                }
            })
    }
    fn find_type_name(&self, typ: &TcType) -> Option<TcType> {
        self.type_infos.find_id(typ)
    }
    fn find_record(&self, fields: &[InternedStr]) -> Option<(&TcType, &TcType)> {
        self.type_infos.find_record(fields)
    }
}

struct Def<'a:'b, 'b> {
    tag: VMTag,
    elems: &'b [Value<'a>]
}
unsafe impl <'a, 'b> DataDef for Def<'a, 'b> {
    type Value = DataStruct<'a>;
    fn size(&self) -> usize {
        use std::mem::size_of;
        size_of::<usize>() + size_of::<Value<'a>>() * self.elems.len()
    }
    fn initialize(self, result: *mut DataStruct<'a>) {
        let result = unsafe { &mut *result };
        result.tag = self.tag;
        for (field, value) in result.fields.iter().zip(self.elems.iter()) {
            field.set(value.clone());
        }
    }
    fn make_ptr(&self, ptr: *mut ()) -> *mut DataStruct<'a> {
        unsafe {
            use std::raw::Slice;
            let x = Slice { data: &*ptr, len: self.elems.len() };
            ::std::mem::transmute(x)
        }
    }
}

impl <'a, 'b> Traverseable for Def<'a, 'b> {
    fn traverse(&self, gc: &mut Gc) {
        self.elems.traverse(gc);
    }
}

struct Roots<'a: 'b, 'b> {
    globals: &'b FixedVec<Global<'a>>,
    stack: &'b mut [Value<'a>],
    interner: &'b mut Interner,
    roots: Ref<'b, Vec<GcPtr<Traverseable>>>
}
impl <'a, 'b> Traverseable for Roots<'a, 'b> {
    fn traverse(&self, gc: &mut Gc) {
        for g in self.globals.borrow().iter() {
            g.traverse(gc);
        }
        self.stack.traverse(gc);
        //Also need to check the interned string table
        self.interner.traverse(gc);
        self.roots.traverse(gc);
    }
}

impl <'a> VM<'a> {
    
    pub fn new() -> VM<'a> {
        let vm = VM {
            globals: FixedVec::new(),
            type_infos: RefCell::new(TypeInfos::new()),
            typeids: FixedMap::new(),
            interner: RefCell::new(Interner::new()),
            names: RefCell::new(HashMap::new()),
            gc: RefCell::new(Gc::new()),
            stack: RefCell::new(Stack::new()),
            roots: RefCell::new(Vec::new())
        };
        vm.add_types()
            .unwrap();
        vm.add_primitives()
            .unwrap();
        vm
    }

    fn add_types(&self) -> Result<(), (TypeId, TcType)> {
        let ref ids = self.typeids;
        try!(ids.try_insert(TypeId::of::<()>(), Type::unit()));
        try!(ids.try_insert(TypeId::of::<bool>(), Type::bool()));
        try!(ids.try_insert(TypeId::of::<VMInt>(), Type::int()));
        try!(ids.try_insert(TypeId::of::<f64>(), Type::float()));
        try!(ids.try_insert(TypeId::of::<::std::string::String>(), Type::string()));
        Ok(())
    }

    fn add_primitives(&self) -> VMResult<()> {
        use primitives as prim;
        fn f1<A, R>(f: fn (A) -> R) -> fn (A) -> R {
            f
        }
        fn f2<A, B, R>(f: fn (A, B) -> R) -> fn (A, B) -> R {
            f
        }
        fn f3<A, B, C, R>(f: fn (A, B, C) -> R) -> fn (A, B, C) -> R {
            f
        }
        let a = Type::generic(ast::Generic { kind: Rc::new(ast::Kind::Star), id: self.intern("a") });
        let b = Type::generic(ast::Generic { kind: Rc::new(ast::Kind::Star), id: self.intern("b") });
        let array_a = Type::array(a.clone());
        let io = |t| ASTType::from(ast::type_con(self.intern("IO"), vec![t]));
        try!(self.extern_function("array_length", vec![array_a.clone()], Type::int().clone(), Box::new(prim::array_length)));
        try!(define_function(self, "string_length", f1(prim::string_length)));
        try!(define_function(self, "string_find", f2(prim::string_find)));
        try!(define_function(self, "string_rfind", f2(prim::string_rfind)));
        try!(define_function(self, "string_trim", f1(prim::string_trim)));
        try!(define_function(self, "string_compare", f2(prim::string_compare)));
        try!(self.extern_function("string_append", vec![Type::string().clone(), Type::string().clone()], Type::string().clone(), Box::new(prim::string_append)));
        try!(self.extern_function("string_eq", vec![Type::string().clone(), Type::string().clone()], Type::bool().clone(), Box::new(prim::string_eq)));
        try!(define_function(self, "string_slice", f3(prim::string_slice)));
        try!(self.extern_function("show_Int_prim", vec![Type::int().clone()], Type::string().clone(), Box::new(prim::show)));
        try!(self.extern_function("show_Float_prim", vec![Type::float().clone()], Type::string().clone(), Box::new(prim::show)));
        try!(self.extern_function("#error", vec![Type::string().clone()], a.clone(), Box::new(prim::error)));
        try!(self.extern_function("error", vec![Type::string().clone()], a.clone(), Box::new(prim::error)));
        try!(self.extern_function("trace", vec![a.clone()], Type::unit(), Box::new(prim::trace)));
        let lazy = |t| ASTType::from(ast::type_con(self.intern("Lazy"), vec![t]));
        try!(self.extern_function("lazy",
                                  vec![Type::function(vec![Type::unit()], a.clone())],
                                  lazy(a.clone()),
                                  Box::new(::lazy::lazy)));
        try!(self.extern_function("force",
                                  vec![lazy(a.clone())],
                                  a.clone(),
                                  Box::new(::lazy::force)));

        //IO functions
        try!(define_function(self, "print_int", f1(prim::print_int)));
        let catch_fn = Type::function(vec![Type::string().clone()], io(a.clone()));
        try!(self.extern_function_io("catch_IO",
                                        3,
                                        Type::function(vec![io(a.clone()), catch_fn], io(a.clone())),
                                        Box::new(prim::catch_io)));
        try!(self.extern_function_io("read_file",
                                        2,
                                        Type::function(vec![Type::string().clone()], io(Type::string().clone())),
                                        Box::new(prim::read_file)));
        try!(self.extern_function_io("read_line",
                                        1,
                                        io(Type::string().clone()),
                                        Box::new(prim::read_line)));
        try!(self.extern_function_io("print",
                                        2,
                                        Type::function(vec![Type::string().clone()], io(Type::unit().clone())),
                                        Box::new(prim::print)));
        try!(self.extern_function_io("run_expr",
                                        2,
                                        Type::function(vec![Type::string().clone()], io(Type::string().clone())),
                                     Box::new(prim::run_expr)));
        try!(self.extern_function_io("load_script",
                                        3,
                                        Type::function(vec![Type::string().clone(), Type::string().clone()], io(Type::string().clone())),
                                     Box::new(prim::load_script)));
        
        // io_bind m f (): IO a -> (a -> IO b) -> IO b
        //     = f (m ())
        let io_bind = vec![Pop(1), Push(0), PushInt(0), Call(1), PushInt(0), TailCall(2)];
        let f = Type::function(vec![a.clone()], io(b.clone()));
        let io_bind_type = Type::function(vec![io(a.clone()), f], io(b.clone()));
        self.add_bytecode("io_bind", io_bind_type, 3, io_bind);


        self.add_bytecode("io_return",
            Type::function(vec![a.clone()], io(a.clone())),
                          2,
                          vec![Pop(1)]);
        Ok(())
    }
    fn add_bytecode(&self, name: &str, typ: TcType, args: VMIndex, instructions: Vec<Instruction>) -> VMIndex {
        let id = self.intern(name);
        let compiled_fn = CompiledFunction {
            args: args,
            id: id,
            typ: typ.clone(),
            instructions: instructions,
            inner_functions: vec![],
            strings: vec![]
        };
        let f = self.new_function(compiled_fn);
        let closure = self.new_closure_and_collect(&mut self.stack.borrow_mut().values, f, &[]);
        self.names.borrow_mut().insert(id, GlobalFn(self.globals.len()));
        self.globals.push(Global { id: id, typ: typ, value: Cell::new(Closure(closure)) });
        self.globals.len() as VMIndex - 1
    }

    pub fn push(&self, v: Value<'a>) {
        self.stack.borrow_mut().push(v)
    }

    pub fn pop(&self) -> Value<'a> {
        self.stack.borrow_mut()
            .pop()
    }

    pub fn new_function(&self, f: CompiledFunction) -> GcPtr<BytecodeFunction> {
        BytecodeFunction::new(&mut self.gc.borrow_mut(), f)
    }

    pub fn get_global(&self, name: &str) -> Option<&Global<'a>> {
        let n = self.intern(name);
        self.globals.find(|g| n == g.id).map(|tup| tup.1)
    }

    pub fn get_type<T: ?Sized + Any>(&self) -> &TcType {
        let id = TypeId::of::<T>();
        self.typeids.get(&id)
            .unwrap_or_else(|| {
                let name = unsafe { type_name::<T>() };
                panic!("Expected type {} to be inserted before get_type call", name)
            })
    }

    pub fn run_function(&self, cf: &Global<'a>) -> VMResult<Value<'a>> {
        self.call_function(0, cf)
    }

    pub fn execute_call(&self, args: VMIndex) -> VMResult<Value<'a>> {
        let stack = self.stack.borrow_mut();
        let frame = StackFrame::new_scope(stack, args + 1, None, |frame| {
            self.execute(frame, &[Call(args)], &BytecodeFunction::empty())
        });
        frame.map(|mut frame| {
            if frame.len() > 0 {
                frame.pop()
            }
            else {
                Int(0)
            }
        })

    }

    pub fn execute_instructions(&self, instructions: &[Instruction]) -> VMResult<Value<'a>> {
        let stack = self.stack.borrow_mut();
        let frame = StackFrame::new_scope(stack, 0, None, |frame| {
            self.execute(frame, instructions, &BytecodeFunction::empty())
        });
        frame.map(|mut frame| {
            if frame.len() > 0 {
                frame.pop()
            }
            else {
                Int(0)
            }
        })
    }

    pub fn extern_function(&self, name: &str, args: Vec<TcType>, return_type: TcType, f: Box<Fn(&VM<'a>) -> Status + 'static>) -> Result<(), Error> {
        let num_args = args.len() as VMIndex;
        self.extern_function_io(name, num_args, Type::function(args, return_type), f)
    }
    pub fn extern_function_io(&self, name: &str, num_args: VMIndex, typ: TcType, f: Box<Fn(&VM<'a>) -> Status + 'static>) -> Result<(), Error> {
        let id = self.intern(name);
        if self.names.borrow().contains_key(&id) {
            return Err(Error::Message(format!("{} is already defined", name)))
        }
        let global = Global {
            id: id,
            typ: typ,
            value: Cell::new(Function(self.gc.borrow_mut().alloc(Move(
                ExternFunction {
                    id: id,
                    args: num_args,
                    function: f
                }))))
        };
        self.names.borrow_mut().insert(id, GlobalFn(self.globals.len()));
        self.globals.push(global);
        Ok(())
    }

    pub fn register_type<T: ?Sized + Any>(&self, name: &str) -> Result<&TcType, ()> {
        let n = self.intern(name);
        let mut type_infos = self.type_infos.borrow_mut();
        if type_infos.id_to_type.contains_key(&n) {
            Err(())
        }
        else {
            let id = TypeId::of::<T>();
            let typ = Type::data(ast::TypeConstructor::Data(n), Vec::new());
            try!(self.typeids.try_insert(id, typ.clone()).map_err(|_| ()));
            let t = self.typeids.get(&id).unwrap();
            let ctor = Type::variants(vec![(n, typ)]);
            type_infos.id_to_type.insert(n, (Vec::new(), ctor.clone()));
            type_infos.type_to_id.insert(ctor, Type::data(ast::TypeConstructor::Data(n), vec![]));
            Ok(t)
        }
    }

    pub fn intern(&self, s: &str) -> InternedStr {
        self.interner.borrow_mut().intern(&mut *self.gc.borrow_mut(), s)
    }

    pub fn env<'b>(&'b self) -> VMEnv<'a, 'b> {
        VMEnv {
            type_infos: self.type_infos.borrow(),
            globals: &self.globals,
            names: self.names.borrow(),
            io_arg: [ast::Generic { id: self.intern("a"), kind: Rc::new(ast::Kind::Star) }]
        }
    }

    pub fn collect(&self) {
        let mut stack = self.stack.borrow_mut();
        self.with_roots(&mut stack.values, |gc, mut roots| {
            unsafe { gc.collect(&mut roots); }
        })
    }

    pub fn root<T: Any>(&self, v: GcPtr<Box<Any>>) -> Option<Root<T>> {
        match v.downcast_ref::<T>().or_else(|| v.downcast_ref::<Box<T>>().map(|p| &**p)) {
            Some(ptr) => {
                self.roots.borrow_mut().push(v.as_traverseable());
                Some(Root { roots: &self.roots, ptr: ptr })
            }
            None => None
        }
    }

    pub fn root_string(&self, ptr: GcPtr<str>) -> RootStr {
        self.roots.borrow_mut().push(ptr.as_traverseable_string());
        RootStr(Root { roots: &self.roots, ptr: &*ptr })
    }

    pub fn new_data(&self, tag: VMTag, fields: &[Value<'a>]) -> Value<'a> {
        Data(self.gc.borrow_mut().alloc(Def { tag: tag, elems: fields }))
    }
    fn new_data_and_collect(&self, stack: &mut [Value<'a>], tag: VMTag, fields: &mut [Value<'a>]) -> GcPtr<DataStruct<'a>> {
       self.alloc(stack, Def { tag: tag, elems: fields })
    }
    fn new_closure(&self, func: GcPtr<BytecodeFunction>, fields: &[Value<'a>]) -> GcPtr<ClosureData<'a>> {
        self.gc.borrow_mut().alloc(ClosureDataDef(func, fields))
    }
    fn new_closure_and_collect(&self, stack: &mut [Value<'a>], func: GcPtr<BytecodeFunction>, fields: &[Value<'a>]) -> GcPtr<ClosureData<'a>> {
        self.alloc(stack, ClosureDataDef(func, fields))
    }

    fn with_roots<F, R>(&self, stack: &mut [Value<'a>], f: F) -> R
        where F: for<'b> FnOnce(&mut Gc, Roots<'a, 'b>) -> R {
        let mut interner = self.interner.borrow_mut();
        let roots = Roots {
            globals: &self.globals,
            stack: stack,
            interner: &mut *interner,
            roots: self.roots.borrow()
        };
        let mut gc = self.gc.borrow_mut();
        f(&mut gc, roots)
    }

    pub fn alloc<T: ?Sized, D>(&self, stack: &mut [Value<'a>], def: D) -> GcPtr<T>
        where D: DataDef<Value=T> + Traverseable {
        self.with_roots(stack, |gc, mut roots| {
            unsafe { gc.alloc_and_collect(&mut roots, def) }
        })
    }

    pub fn call_function(&self, args: VMIndex, global: &Global<'a>) -> VMResult<Value<'a>>  {
        debug!("Call function {:?}", global);
        match global.value.get() {
            Function(ptr) => {
                let stack = StackFrame::frame(self.stack.borrow_mut(), args, None);
                let stack = self.execute_function(stack, &ptr);
                stack.map(|mut stack| { if stack.len() > 0 { stack.pop() } else { Int(0) } })
            }
            Closure(closure) => self.call_bytecode(args, closure),
            x => Err(Error::Message(format!("Tried to call a non function object: '{:?}'", x)))
        }
    }

    ///Calls a module, allowed to to run IO expressions
    pub fn call_module(&self, typ: &TcType, closure: GcPtr<ClosureData<'a>>) -> VMResult<Value<'a>> {
        let value = try!(self.call_bytecode(0, closure));
        if let Type::Data(ast::TypeConstructor::Data(id), _) = **typ {
            if id == "IO" {
                debug!("Run IO {:?}", value);
                self.push(value);
                self.push(Int(0));
                let mut stack = StackFrame::frame(self.stack.borrow_mut(), 2, None);
                stack = try!(self.execute(stack, &[Call(1)], &BytecodeFunction::empty()));
                return Ok(if stack.len() > 0 { stack.pop() } else { Int(0) })
            }
        }
        Ok(value)
    }

    pub fn call_bytecode(&self, args: VMIndex, closure: GcPtr<ClosureData<'a>>) -> VMResult<Value<'a>> {
        self.push(Closure(closure));
        let mut stack = StackFrame::frame(self.stack.borrow_mut(), args, Some(closure));
        stack = try!(self.execute(stack, &closure.function.instructions, &closure.function));
        let x = if stack.len() > 0 { stack.pop() } else { Int(0) };
        Ok(x)
    }

    fn execute_callable<'b>(&'b self, mut stack: StackFrame<'a, 'b>, function: &Callable<'a>, excess: bool)
            -> Result<StackFrame<'a, 'b>, Error> {
        match *function {
            Callable::Closure(closure) => {
                stack = stack.enter_scope(closure.function.args, Some(closure));
                stack.frame.excess = excess;
                stack.stack.frames.last_mut().unwrap().excess = excess;
                Ok(stack)
            }
            Callable::Extern(ref ext) => self.execute_function(stack, ext)
        }
    }

    fn execute_function<'b>(&'b self, stack: StackFrame<'a, 'b>, function: &ExternFunction<'a>) -> Result<StackFrame<'a, 'b>, Error> {
        //Make sure that the stack is not borrowed during the external function call
        //Necessary since we do not know what will happen during the function call
        assert!(stack.len() >= function.args + 1);
        let function_index = stack.len() - function.args - 1;
        debug!("------- {} {:?}", function_index, &stack[..]);
        let StackFrame { stack, frame } = stack;
        drop(stack);
        let status = (function.function)(self);
        let mut stack = StackFrame { stack: self.stack.borrow_mut(), frame: frame };
        let result = stack.pop();
        while stack.len() > function_index {
            debug!("{} {:?}", stack.len(), &stack[..]);
            stack.pop();
        }
        stack.push(result);
        debug!("------- {} {:?}", function_index, &stack[..]);
        match status {
            Status::Ok => Ok(stack),
            Status::Error => {
                match stack.pop() {
                    String(s) => Err(Error::Message(s.to_string())),
                    _ => Err(Error::Message("Unexpected panic in VM".to_string()))
                }
            }
        }
    }

    fn call_function_with_upvars<'b>(&'b self
                                    , mut stack: StackFrame<'a, 'b>
                                    , args: VMIndex
                                    , required_args: VMIndex
                                    , callable: Callable<'a>
                                    ) -> Result<StackFrame<'a, 'b>, Error> {
        debug!("cmp {} {}", args, required_args);
        match args.cmp(&required_args) {
            Ordering::Equal => self.execute_callable(stack, &callable, false),
            Ordering::Less => {
                let app = {
                    let whole_stack = &mut stack.stack.values[..];
                    let arg_start = whole_stack.len() - args as usize;
                    let (pre_stack, fields) = whole_stack.split_at_mut(arg_start);
                    let def = PartialApplicationDataDef(callable, fields);
                    PartialApplication(self.alloc(pre_stack, def))
                };
                for _ in 0..(args+1) {
                    stack.pop();
                }
                stack.push(app);
                Ok(stack)
            }
            Ordering::Greater => {
                let excess_args = args - required_args;
                let d = {
                    let whole_stack = &mut stack.stack.values[..];
                    let arg_start = whole_stack.len() - excess_args as usize;
                    let (pre_stack, fields) = whole_stack.split_at_mut(arg_start);
                    self.new_data_and_collect(pre_stack, 0, fields)
                };
                for _ in 0..excess_args {
                    stack.pop();
                }
                //Insert the excess args before the actual closure so it does not get
                //collected
                let offset = stack.len() - required_args - 1;
                stack.insert_slice(offset, &[Cell::new(Data(d))]);
                debug!("xxxxxx {:?}\n{:?}", &(*stack)[..], stack.stack.frames);
                self.execute_callable(stack, &callable, true)
            }
        }
    }

    fn do_call<'b>(&'b self, mut stack: StackFrame<'a, 'b>, args: VMIndex) -> Result<StackFrame<'a, 'b>, Error> {
        let function_index = stack.len() - 1 - args;
        debug!("Do call {:?} {:?}", stack[function_index], &(*stack)[(function_index + 1) as usize..]);
        match stack[function_index].clone() {
            Function(ref f) => {
                let callable = Callable::Extern(f.clone());
                self.call_function_with_upvars(stack, args, f.args, callable)
            }
            Closure(ref closure) => {
                let callable = Callable::Closure(closure.clone());
                self.call_function_with_upvars(stack, args, closure.function.args, callable)
            }
            PartialApplication(app) => {
                let total_args = app.arguments.len() as VMIndex + args;
                let offset = stack.len() - args;
                stack.insert_slice(offset, &app.arguments);
                self.call_function_with_upvars(stack, total_args, app.function.args(), app.function)
            }
            x => return Err(Error::Message(format!("Cannot call {:?}", x)))
        }
    }

    pub fn execute<'b>(&'b self, stack: StackFrame<'a, 'b>, instructions: &[Instruction], function: &BytecodeFunction) -> Result<StackFrame<'a, 'b>, Error> {
        let  mut stack = try!(self.execute_(stack, 0, instructions, function));
        loop {
            let (closure, i) = match stack.frame.upvars {
                None => break,
                Some(closure) => {
                    //Tail calls into extern functions at the top level will drop the last
                    //stackframe so just return immedietly
                    if stack.stack.frames.len() == 0 {
                        return Ok(stack)
                    }
                    (closure, stack.frame.instruction_index)
                }
            };
            debug!("Continue with {:?}\nAt: {}/{}",
                   closure.function.name, i, closure.function.instructions.len());
            let new_stack = try!(self.execute_(stack, i, &closure.function.instructions, &closure.function));
            debug!("Result {:?} {:?}", new_stack.frame.upvars, new_stack.stack.values);
            stack = new_stack;
        }
        Ok(stack)
    }
    fn execute_<'b>(&'b self,
                        mut stack: StackFrame<'a, 'b>,
                        mut index: usize,
                        instructions: &[Instruction],
                        function: &BytecodeFunction
                       ) -> Result<StackFrame<'a, 'b>, Error> {
        debug!(">>>\nEnter frame {:?}: {:?}\n{:?}", function.name, &stack[..], stack.frame);
        while let Some(&instr) = instructions.get(index) {
            debug_instruction(&stack, index, instr);
            match instr {
                Push(i) => {
                    let v = stack[i].clone();
                    stack.push(v);
                }
                PushInt(i) => {
                    stack.push(Int(i));
                }
                PushString(string_index) => {
                    stack.push(String(function.strings[string_index as usize].inner()));
                }
                PushGlobal(i) => {
                    let x = get_global!(self, i as usize);
                    stack.push(x);
                }
                PushFloat(f) => stack.push(Float(f)),
                Store(i) => {
                    stack[i] = stack.pop();
                }
                StoreGlobal(i) => {
                    let v = stack.pop();
                    self.globals[i as usize].value.set(v);
                }
                Call(args) => {
                    stack.frame.instruction_index = index + 1;
                    return self.do_call(stack, args);
                }
                TailCall(mut args) => {
                    let mut amount = stack.len() - args;
                    if stack.frame.excess {
                        amount += 1;
                        let i = stack.stack.values.len() - stack.len() as usize - 2;
                        match stack.stack.values[i] {
                            Data(excess) => {
                                debug!("Push excess args {:?}", &excess.fields);
                                for value in &excess.fields {
                                    stack.push(value.get());
                                }
                                args += excess.fields.len() as VMIndex;
                            }
                            _ => panic!("Expected excess args")
                        }
                    }
                    stack = stack.exit_scope();
                    debug!("{:?}", &stack[..]);
                    let end = stack.len() - args - 1;
                    stack.remove_range(end - amount, end);
                    debug!("{:?}", &stack[..]);
                    return self.do_call(stack, args);
                }
                Construct(tag, args) => {
                    let d = {
                        let whole_stack = &mut stack.stack.values[..];
                        let arg_start = whole_stack.len() - args as usize;
                        let (pre_stack, fields) = whole_stack.split_at_mut(arg_start);
                        self.new_data_and_collect(pre_stack, tag, fields)
                    };
                    for _ in 0..args {
                        stack.pop();
                    } 
                    stack.push(Data(d));
                }
                GetField(i) => {
                    match stack.pop() {
                        Data(data) => {
                            let v = data.fields[i as usize].get();
                            stack.push(v);
                        }
                        x => return Err(Error::Message(format!("GetField on {:?}", x)))
                    }
                }
                SetField(i) => {
                    let value = stack.pop();
                    let data = stack.pop();
                    match data {
                        Data(data) => {
                            data.fields[i as usize].set(value);
                        }
                        _ => return Err(Error::Message("Op SetField called on non data type".to_string()))
                    }
                }
                TestTag(tag) => {
                    let x = match *stack.top() {
                        Data(ref data) => if data.tag == tag { 1 } else { 0 },
                        _ => return Err(Error::Message("Op TestTag called on non data type".to_string()))
                    };
                    stack.push(Int(x));
                }
                Split => {
                    match stack.pop() {
                        Data(data) => {
                            for field in data.fields.iter().map(|x| x.get()) {
                                stack.push(field.clone());
                            }
                        }
                        _ => return Err(Error::Message("Op Split called on non data type".to_string()))
                    }
                }
                Jump(i) => {
                    index = i as usize;
                    continue
                }
                CJump(i) => {
                    match stack.pop() {
                        Int(0) => (),
                        _ => {
                            index = i as usize;
                            continue
                        }
                    }
                }
                Pop(n) => {
                    for _ in 0..n {
                        stack.pop();
                    }
                }
                Slide(n) => {
                    debug!("{:?}", &stack[..]);
                    let v = stack.pop();
                    for _ in 0..n {
                        stack.pop();
                    }
                    stack.push(v);
                }
                GetIndex => {
                    let index = stack.pop();
                    let array = stack.pop();
                    match (array, index) {
                        (Data(array), Int(index)) => {
                            let v = array.fields[index as usize].get();
                            stack.push(v);
                        }
                        (x, y) => return Err(Error::Message(format!("Op GetIndex called on invalid types {:?} {:?}", x, y)))
                    }
                }
                SetIndex => {
                    let value = stack.pop();
                    let index = stack.pop();
                    let array = stack.pop();
                    match (array, index) {
                        (Data(array), Int(index)) => {
                            array.fields[index as usize].set(value);
                        }
                        (x, y) => return Err(Error::Message(format!("Op SetIndex called on invalid types {:?} {:?}", x, y)))
                    }
                }
                MakeClosure(fi, n) => {
                    let closure = {
                        let i = stack.stack.len() - n;
                        let (stack_after, args) = stack.stack.values.split_at_mut(i as usize);
                        let func = function.inner_functions[fi as usize];
                        Closure(self.new_closure_and_collect(stack_after, func, args))
                    };
                    for _ in 0..n {
                        stack.pop();
                    }
                    stack.push(closure);
                }
                NewClosure(fi, n) => {
                    let closure = {
                        //Use dummy variables until it is filled
                        let mut args = [Int(0); 128];
                        let func = function.inner_functions[fi as usize];
                        Closure(self.new_closure_and_collect(&mut stack.stack.values[..], func, &mut args[..n as usize]))
                    };
                    stack.push(closure);
                }
                CloseClosure(n) => {
                    let i = stack.len() - n - 1;
                    match stack[i] {
                        Closure(closure) => {
                            for var in closure.upvars.iter().rev() {
                                var.set(stack.pop());
                            }
                            stack.pop();//Remove the closure
                        }
                        x => panic!("Expected closure, got {:?}", x)
                    }
                }
                InstantiateConstrained(gi) => {
                    let closure = {
                        let dict = stack.pop();
                        let func = match get_global!(self, gi as usize) {
                            Closure(closure) => closure.function,
                            _ => panic!()
                        };
                        Closure(self.new_closure_and_collect(&mut stack, func, &mut [dict]))
                    };
                    stack.push(closure);
                }
                PushUpVar(i) => {
                    let v = stack.get_upvar(i).clone();
                    stack.push(v);
                }
                StoreUpVar(i) => {
                    let v = stack.pop();
                    stack.set_upvar(i, v);
                }
                AddInt => binop_int(&mut stack, |l, r| l + r),
                SubtractInt => binop_int(&mut stack, |l, r| l - r),
                MultiplyInt => binop_int(&mut stack, |l, r| l * r),
                IntLT => binop_int(&mut stack, |l, r| if l < r { 1 } else { 0 }),
                IntEQ => binop_int(&mut stack, |l, r| if l == r { 1 } else { 0 }),

                AddFloat => binop_float(&mut stack, |l, r| l + r),
                SubtractFloat => binop_float(&mut stack, |l, r| l - r),
                MultiplyFloat => binop_float(&mut stack, |l, r| l * r),
                FloatLT => binop(&mut stack, |l, r| {
                    match (l, r) {
                        (Float(l), Float(r)) => Int(if l < r { 1 } else { 0 }),
                        _ => panic!()
                    }
                }),
                FloatEQ => binop(&mut stack, |l, r| {
                    match (l, r) {
                        (Float(l), Float(r)) => Int(if l == r { 1 } else { 0 }),
                        _ => panic!()
                    }
                })
            }
            index += 1;
        }
        if stack.len() != 0 {
            debug!("--> {:?}", stack.top());
        }
        else {
            debug!("--> ()");
        }
        let result = stack.pop();
        debug!("Return {:?}", result);
        let len = stack.len();
        for _ in 0..(len + 1) {
            stack.pop();
        }
        if stack.frame.excess {
            match stack.pop() {
                Data(excess) => {
                    debug!("Push excess args {:?}", &excess.fields);
                    stack.push(result);
                    for value in &excess.fields {
                        stack.push(value.get());
                    }
                    stack = stack.exit_scope();
                    self.do_call(stack, excess.fields.len() as VMIndex)
                }
                x => panic!("Expected excess arguments found {:?}", x)
            }
        }
        else {
            stack.push(result);
            Ok(stack.exit_scope())
        }
    }
}

#[inline]
fn binop<'a, 'b, F>(stack: &mut StackFrame<'a, 'b>, f: F)
    where F: FnOnce(Value<'a>, Value<'a>) -> Value<'a> {
    let r = stack.pop();
    let l = stack.pop();
    stack.push(f(l, r));
}
#[inline]
fn binop_int<F>(stack: &mut StackFrame, f: F)
    where F: FnOnce(VMInt, VMInt) -> VMInt {
    binop(stack, move |l, r| {
        match (l, r) {
            (Int(l), Int(r)) => Int(f(l, r)),
            (l, r) => panic!("{:?} `intOp` {:?}", l, r)
        }
    })
}
#[inline]
fn binop_float<F>(stack: &mut StackFrame, f: F)
    where F: FnOnce(f64, f64) -> f64 {
    binop(stack, move |l, r| {
        match (l, r) {
            (Float(l), Float(r)) => Float(f(l, r)),
            (l, r) => panic!("{:?} `floatOp` {:?}", l, r)
        }
    })
}

fn debug_instruction(stack: &StackFrame, index: usize, instr: Instruction) {
    debug!("{:?}: {:?} {:?}", index, instr, match instr {
        Push(i) => stack[i],
        NewClosure(..) => Int(stack.len() as isize),
        MakeClosure(..) => Int(stack.len() as isize),
        _ => Int(0)
    });
}

pub fn load_script(vm: &VM, name: &str, input: &str) -> Result<(), Box<StdError>> {
    let mut expr = try!(parse_expr(input, vm));
    let (type_infos, function, typ) = {
        let env = vm.env();
        let (typ, type_infos) = {
            let mut interner = vm.interner.borrow_mut();
            let mut gc = vm.gc.borrow_mut();
            let mut tc = Typecheck::new(&mut interner, &mut gc);
            tc.add_environment(&env);
            let typ = try!(tc.typecheck_expr(&mut expr));
            (typ, tc.type_infos)
        };
        let mut function = {
            let env = (&env, &type_infos);
            let mut interner = vm.interner.borrow_mut();
            let mut gc = vm.gc.borrow_mut();
            let mut compiler = Compiler::new(&env, &mut interner, &mut gc);
            compiler.compile_expr(&expr)
        };
        function.id = vm.interner.borrow_mut().intern(&mut vm.gc.borrow_mut(), name);
        (type_infos, function, typ)
    };
    let function = BytecodeFunction::new(&mut vm.gc.borrow_mut(), function);
    let closure = vm.new_closure(function, &[]);
    let value = try!(vm.call_module(&typ, closure));
    let id = vm.intern(name);
    vm.names.borrow_mut().insert(id, GlobalFn(vm.globals.len()));
    vm.globals.push(Global { id: id, typ: typ, value: Cell::new(value) });
    vm.type_infos.borrow_mut().extend(type_infos);
    Ok(())
}

pub fn load_file(vm: &VM, filename: &str) -> Result<(), Box<StdError>> {
    use std::fs::File;
    use std::io::Read;
    use std::path::Path;
    let path = Path::new(filename);
    let mut file = try!(File::open(path));
    let mut buffer = ::std::string::String::new();
    try!(file.read_to_string(&mut buffer));
    drop(file);
    let name = path.file_stem().and_then(|f| f.to_str()).expect("filename");
    load_script(vm, name, &buffer)
}

pub fn parse_expr(input: &str, vm: &VM) -> Result<ast::LExpr<TcIdent>, Box<StdError>> {
    let mut interner = vm.interner.borrow_mut();
    let mut gc = vm.gc.borrow_mut();
    Ok(try!(::parser::parse_tc(&mut gc, &mut interner, input)))
}
pub fn typecheck_expr<'a>(vm: &VM<'a>, expr_str: &str) -> Result<(ast::LExpr<TcIdent>, TypeInfos), Box<StdError>> {
    let mut expr = try!(parse_expr(&expr_str, vm));
    let env = vm.env();
    let mut interner = vm.interner.borrow_mut();
    let mut gc = vm.gc.borrow_mut();
    let mut tc = Typecheck::new(&mut interner, &mut gc);
    tc.add_environment(&env);
    try!(tc.typecheck_expr(&mut expr));
    Ok((expr, tc.type_infos))
}

pub fn run_expr<'a>(vm: &VM<'a>, expr_str: &str) -> Result<Value<'a>, Box<StdError>> {
    let mut function = {
        let (expr, type_infos) = try!(typecheck_expr(vm, expr_str));
        let env = (vm.env(), &type_infos);
        let mut interner = vm.interner.borrow_mut();
        let mut gc = vm.gc.borrow_mut();
        let mut compiler = Compiler::new(&env, &mut interner, &mut gc);
        compiler.compile_expr(&expr)
    };
    function.id = vm.interner.borrow_mut().intern(&mut vm.gc.borrow_mut(), "<top>");
    let typ = function.typ.clone();
    let function = vm.new_function(function);
    let closure = vm.new_closure(function, &[]);
    let value = try!(vm.call_module(&typ, closure));
    Ok(value)
}

pub fn run_function<'a: 'b, 'b>(vm: &'b VM<'a>, name: &str) -> VMResult<Value<'a>> {
    let func = match vm.globals.find(|g| &*g.id == name) {
        Some((_, f)) => f,
        None => return Err(Error::Message(format!("Undefined function {}", name)))
    };
    vm.run_function(func)
}

#[cfg(test)]
mod tests {
    use std::fs::File;
    use std::io::Read;

    use vm::{VM, Value, load_script};
    use vm::Value::{Float, Int};
    use stack::StackFrame;
    use check::typecheck::Typecheck;

    fn run_expr<'a>(vm: &VM<'a>, s: &str) -> Value<'a> {
        super::run_expr(vm, s)
            .unwrap_or_else(|err| panic!("{}", err))
    }

    #[test]
    fn pass_function_value() {
        let _ = ::env_logger::init();
        let text = 
r"
let lazy: () -> Int = \x -> 42 in
let test: (() -> Int) -> Int = \f -> f () #Int+ 10
in test lazy
";
        let mut vm = VM::new();
        let value = run_expr(&mut vm, text);
        assert_eq!(value, Int(52));
    }
    #[test]
    fn lambda() {
        let _ = ::env_logger::init();
        let text = 
r"
let y = 100 in
let f = \x -> y #Int+ x #Int+ 1
in f(22)
";
        let mut vm = VM::new();
        let value = run_expr(&mut vm, text);
        assert_eq!(value, Int(123));
    }
    #[test]
    fn add_operator() {
        let _ = ::env_logger::init();
        let text = 
r"
let (+) = \x y -> x #Int+ y in 1 + 2 + 3
";
        let mut vm = VM::new();
        let value = run_expr(&mut vm, text);
        assert_eq!(value, Int(6));
    }

    #[test]
    fn record() {
        let _ = ::env_logger::init();
        let text = 
r"
{ x = 0, y = 1.0, z = {} }
";
        let mut vm = VM::new();
        let value = run_expr(&mut vm, text);
        let unit = vm.new_data(0, &mut []);
        assert_eq!(value, vm.new_data(0, &mut [Int(0), Float(1.0), unit]));
    }

    #[test]
    fn add_record() {
        let _ = ::env_logger::init();
        let text = 
r"
type T = { x: Int, y: Int } in
let add = \l r -> { x = l.x #Int+ r.x, y = l.y #Int+ r.y } in
add { x = 0, y = 1 } { x = 1, y = 1 }
";
        let mut vm = VM::new();
        let value = run_expr(&mut vm, text);
        assert_eq!(value, vm.new_data(0, &mut [Int(1), Int(2)]));
    }
    #[test]
    fn script() {
        let _ = ::env_logger::init();
        let text = 
r"
type T = { x: Int, y: Int } in
let add = \l r -> { x = l.x #Int+ r.x, y = l.y #Int+ r.y } in
let sub = \l r -> { x = l.x #Int- r.x, y = l.y #Int- r.y } in
{ add = add, sub = sub }
";
        let mut vm = VM::new();
        load_script(&mut vm, "Vec", text)
            .unwrap_or_else(|err| panic!("{}", err));

        let value = run_expr(&mut vm, "Vec.add { x = 10, y = 5 } { x = 1, y = 2 }");
        assert_eq!(value, vm.new_data(0, &mut [Int(11), Int(7)]));
    }
    #[test]
    fn adt() {
        let _ = ::env_logger::init();
        let text = 
r"
type Option a = | None | Some a
in Some 1
";
        let mut vm = VM::new();
        let value = run_expr(&mut vm, text);
        assert_eq!(value, vm.new_data(1, &mut [Int(1)]));
    }
    #[test]
    fn recursive_function() {
        let _ = ::env_logger::init();
        let text = 
r"
let fib x = if x #Int< 3
            then 1
            else fib (x #Int- 1) #Int+ fib (x #Int- 2)
in fib 7
";
        let mut vm = VM::new();
        let value = run_expr(&mut vm, text);
        assert_eq!(value, Int(13));
    }
    #[test]
    fn mutually_recursive_function() {
        let _ = ::env_logger::init();
        let text = 
r"
let f x = if x #Int< 0
          then x
          else g x
and g x = f (x #Int- 1)
in g 3
";
        let mut vm = VM::new();
        let value = run_expr(&mut vm, text);
        assert_eq!(value, Int(-1));
    }
    #[test]
    fn no_capture_self_function() {
        let _ = ::env_logger::init();
        let text = 
r"
let x = 2 in
let f y = x
in f 4
";
        let mut vm = VM::new();
        let value = run_expr(&mut vm, text);
        assert_eq!(value, Int(2));
    }
    #[test]
    fn insert_stack_slice() {
        use std::cell::Cell;
        let _ = ::env_logger::init();
        let vm = VM::new();
        let _: Result<_, ()> = StackFrame::new_scope(vm.stack.borrow_mut(), 0, None, |mut stack| {
            stack.push(Int(0));
            stack.insert_slice(0, &[Cell::new(Int(2)), Cell::new(Int(1))]);
            assert_eq!(&stack[..], [Int(2), Int(1), Int(0)]);
            stack.scope(2, None, |mut stack| {
                stack.insert_slice(1, &[Cell::new(Int(10))]);
                assert_eq!(&stack[..], [Int(1), Int(10), Int(0)]);
                stack.insert_slice(1, &[]);
                assert_eq!(&stack[..], [Int(1), Int(10), Int(0)]);
                stack.insert_slice(2, &[Cell::new(Int(4)), Cell::new(Int(5)), Cell::new(Int(6))]);
                assert_eq!(&stack[..], [Int(1), Int(10), Int(4), Int(5), Int(6), Int(0)]);
                Ok(stack)
            })
        });
    }
    #[test]
    fn partial_application() {
        let _ = ::env_logger::init();
        let text = 
r"
let f x y = x #Int+ y in
let g = f 10
in g 2 #Int+ g 3
";
        let mut vm = VM::new();
        let value = run_expr(&mut vm, text);
        assert_eq!(value, Int(25));
    }
    #[test]
    fn partial_application2() {
        let _ = ::env_logger::init();
        let text = 
r"
let f x y z = x #Int+ y #Int+ z in
let g = f 10 in
let h = g 20
in h 2 #Int+ g 10 3
";
        let mut vm = VM::new();
        let value = run_expr(&mut vm, text);
        assert_eq!(value, Int(55));
    }
    #[test]
    fn to_many_args_application() {
        let _ = ::env_logger::init();
        let text = 
r"
let f x = \y -> x #Int+ y in
let g = f 20
in f 10 2 #Int+ g 3
";
        let mut vm = VM::new();
        let value = run_expr(&mut vm, text);
        assert_eq!(value, Int(35));
    }
    #[test]
    fn to_many_args_partial_application_twice() {
        let _ = ::env_logger::init();
        let text = 
r"
let f x = \y z -> x #Int+ y #Int+ z in
let g = f 20 5
in f 10 2 1 #Int+ g 2
";
        let mut vm = VM::new();
        let value = run_expr(&mut vm, text);
        assert_eq!(value, Int(40));
    }
    #[test]
    fn print_int() {
        let _ = ::env_logger::init();
        let text = 
r"
print_int 123
";
        let mut vm = VM::new();
        run_expr(&mut vm, text);
    }
    #[test]
    fn no_io_eval() {
        let _ = ::env_logger::init();
        let text = 
r#"
let x = io_bind (print_int 1) (\x -> error "NOOOOOOOO")
in { x }
"#;
        let mut vm = VM::new();
        run_expr(&mut vm, text);
    }

    #[test]
    fn non_exhaustive_pattern() {
        let _ = ::env_logger::init();
        let text = 
r"
type AB = | A | B in
case A of
    | B -> True
";
        let mut vm = VM::new();
        let result = super::run_expr(&mut vm, text);
        assert!(result.is_err());
    }

    #[test]
    fn record_pattern() {
        let _ = ::env_logger::init();
        let text = 
r#"
case { x = 1, y = "abc" } of
    | { x, y = z } -> x #Int+ string_length z
"#;
        let mut vm = VM::new();
        let result = run_expr(&mut vm, text);
        assert_eq!(result, Int(4));
    }

    #[test]
    fn let_record_pattern() {
        let _ = ::env_logger::init();
        let text = 
r#"
let (+) x y = x #Int+ y
in
let a = { x = 10, y = "abc" }
in
let {x, y = z} = a
in x + string_length z
"#;
        let mut vm = VM::new();
        let result = run_expr(&mut vm, text);
        assert_eq!(result, Int(13));
    }

    #[test]
    fn partial_record_pattern() {
        let _ = ::env_logger::init();
        let text = 
r#"
type A = { x: Int, y: Float } in
let x = { x = 1, y = 2.0 }
in case x of
    | { y } -> y
"#;
        let mut vm = VM::new();
        let result = run_expr(&mut vm, text);
        assert_eq!(result, Float(2.0));
    }

    #[test]
    fn record_let_adjust() {
        let _ = ::env_logger::init();
        let text = 
r#"
let x = \z -> let { x, y } = { x = 1, y = 2 } in z in
let a = 3
in a
"#;
        let mut vm = VM::new();
        let result = run_expr(&mut vm, text);
        assert_eq!(result, Int(3));
    }

    #[test]
    fn unit_expr() {
        let _ = ::env_logger::init();
        let text = 
r#"
let x = ()
and y = 1
in y
"#;
        let mut vm = VM::new();
        let result = run_expr(&mut vm, text);
        assert_eq!(result, Int(1));
    }

    #[test]
    fn test_prelude() {
        let _ = ::env_logger::init();
        let mut text = String::new();
        File::open("../std/prelude.hs").unwrap().read_to_string(&mut text).unwrap();
        let mut vm = VM::new();
        run_expr(&mut vm, &text);
    }

    #[test]
    fn test_map() {
        let _ = ::env_logger::init();
        let mut vm = VM::new();
        let mut text = String::new();
        File::open("../std/prelude.hs").unwrap().read_to_string(&mut text).unwrap();
        load_script(&mut vm, "prelude", &text).unwrap();
        text.clear();
        File::open("../std/map.hs").unwrap().read_to_string(&mut text).unwrap();
        run_expr(&mut vm, &text);
    }

    #[test]
    fn test_state() {
        let _ = ::env_logger::init();
        let mut vm = VM::new();
        let mut text = String::new();
        File::open("../std/prelude.hs").unwrap().read_to_string(&mut text).unwrap();
        load_script(&mut vm, "prelude", &text).unwrap();
        text.clear();
        File::open("../std/state.hs").unwrap().read_to_string(&mut text).unwrap();
        run_expr(&mut vm, &text);
    }

    #[bench]
    fn prelude(b: &mut ::test::Bencher) {
        use vm::VM;
        let _ = ::env_logger::init();
        let vm = VM::new();
        let env = vm.env();
        let mut interner = vm.interner.borrow_mut();
        let mut gc = vm.gc.borrow_mut();
        let mut text = String::new();
        File::open("../std/prelude.hs").unwrap().read_to_string(&mut text).unwrap();
        let expr = ::parser::parse_tc(&mut *gc, &mut *interner, &text)
            .unwrap_or_else(|err| panic!("{:?}", err));
        b.iter(|| {
            let mut tc = Typecheck::new(&mut *interner, &mut *gc);
            tc.add_environment(&env);
            let result = tc.typecheck_expr(&mut expr.clone());
            if let Err(ref err) = result {
                println!("{}", err);
                assert!(false);
            }
            ::test::black_box(result)
        })
    }
}

