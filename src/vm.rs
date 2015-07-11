use std::cell::{Cell, RefCell, RefMut, Ref};
use std::fmt;
use std::intrinsics::type_name;
use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::cmp::Ordering;
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::fs::File;
use std::io::Read;
use base::ast;
use base::ast::Type;
use typecheck::{Typecheck, TypeEnv, TypeInfos, Typed, STRING_TYPE, INT_TYPE, FLOAT_TYPE, UNIT_TYPE, TcIdent, TcType};
use compiler::*;
use compiler::Instruction::*;
use base::interner::{Interner, InternedStr};
use base::gc::{Gc, GcPtr, Traverseable, DataDef, Move};
use fixed::*;

use self::Named::*;

use vm::Value::{
    Int,
    Float,
    String,
    Data,
    Function,
    PartialApplication,
    Closure,
    TraitObject,
    Userdata,
    Bottom
};

#[derive(Copy, Clone, Debug)]
pub struct Userdata_ {
    pub data: GcPtr<RefCell<Box<Any>>>
}

impl Userdata_ {
    pub fn new<T: Any>(vm: &VM, v: T) -> Userdata_ {
        let v: Box<Any> = box v;
        Userdata_ { data: vm.gc.borrow_mut().alloc(Move(RefCell::new(v))) }
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
    function: GcPtr<BytecodeFunction>,
    upvars: [Cell<Value<'a>>]
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
            unsafe {
                ::std::ptr::write(field.as_unsafe_cell().get(), value.clone());
            }
        }
    }
    fn make_ptr(&self, ptr: *mut ()) -> *mut ClosureData<'a> {
        unsafe {
            use std::raw::Slice;
            let x = Slice { data: &*ptr, len: self.1.len() };
            ::std::mem::transmute(x)
        }
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
    tag: VMTag,
    fields: [Cell<Value<'a>>]
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
    Bottom//Special value used to mark that a global was used before it was initialized
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
        size_of::<GcPtr<ClosureData<'a>>>() + size_of::<Cell<Value<'a>>>() * self.1.len()
    }
    fn initialize(self, result: *mut PartialApplicationData<'a>) {
        let result = unsafe { &mut *result };
        result.function = self.0;
        for (field, value) in result.arguments.iter().zip(self.1.iter()) {
            unsafe {
                ::std::ptr::write(field.as_unsafe_cell().get(), value.clone());
            }
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
            Int(_) | Float(_) | Bottom => ()
        }
    }
}

impl <'a> fmt::Debug for Value<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        struct OneLevel<'a: 'b, 'b>(&'b [Cell<Value<'a>>]);
        impl <'a, 'b> fmt::Debug for OneLevel<'a, 'b> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                if self.0.len() == 0 { return Ok(()) }
                try!(write!(f, "("));
                for a in self.0 {
                    try!(match a.get() {
                        Int(i) => write!(f, "{:?}", i),
                        Float(x) => write!(f, "{:?}f", x),
                        String(x) => write!(f, "\"{}\"", &*x),
                        Data(ref data) => write!(f, "{{{:?} ??}}", data.tag),
                        Function(ref func) => write!(f, "{:?}", &**func),
                        Closure(ref closure) => write!(f, "<{} {:?} ??>", closure.function.name.as_ref().map(|s| &s[..]).unwrap_or("anon:"),
                                                       { let p: *const _ = &*closure.function; p }),
                        PartialApplication(_) => write!(f, "<App ??>"),
                        TraitObject(ref object) => write!(f, "<{:?} ??>", object.tag),
                        Userdata(ref data) => write!(f, "<Userdata {:?}>", data.ptr()),
                        Bottom => write!(f, "Bottom")
                    });
                }
                write!(f, ")")
            }
        }
        match *self {
            Int(i) => write!(f, "{:?}", i),
            Float(x) => write!(f, "{:?}f", x),
            String(x) => write!(f, "\"{:?}\"", &*x),
            Data(ref data) => {
                write!(f, "{{{:?} {:?}}}", data.tag, OneLevel(&data.fields))
            }
            Function(ref func) => write!(f, "{:?}", &**func),
            Closure(ref closure) => {
                let p: *const _ = &*closure.function;
                let name = match closure.function.name {
                    Some(ref name) => &name[..],
                    None => ""
                };
                write!(f, "<{:?} {:?} {:?}>", name, p, OneLevel(&closure.upvars))
            }
            PartialApplication(ref app) => write!(f, "<App {:?}>", OneLevel(&app.arguments)),
            TraitObject(ref object) => write!(f, "<{:?} {:?}>", object.tag, OneLevel(&object.fields)),
            Userdata(ref data) => write!(f, "<Userdata {:?}>", data.ptr()),
            Bottom => write!(f, "Bottom")
        }
    }
}

macro_rules! get_global {
    ($vm: ident, $i: expr) => (
        match $vm.globals[$i].value.get() {
            Bottom => return Err(format!("Global '{}' was used before it was initialized", $vm.globals[$i].id)),
            x => x
        }
    )
}

pub enum Status {
    Ok,
    Error
}

pub struct ExternFunction<'a> {
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
    fn type_of(&self) -> &TcType {
        &self.typ
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
    interner: RefCell<Interner>,
    names: RefCell<HashMap<InternedStr, Named>>,
    gc: RefCell<Gc>,
    //Since the vm will be retrieved often and the borrowing from a RefCell does not work
    //it needs to be in a unsafe cell
    pub stack: RefCell<Stack<'a>>
}

pub type VMError = ::std::string::String;
pub type VMResult<T> = Result<T, VMError>;

pub struct VMEnv<'a: 'b, 'b> {
    type_infos: Ref<'b, TypeInfos>,
    globals: &'b FixedVec<Global<'a>>,
    names: Ref<'b, HashMap<InternedStr, Named>>
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
            .and_then(|typ| {
                debug!("a aaa {:?}", typ);
                match *typ {
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
        match self.type_infos.id_to_type.get(data_name) {
            Some(&Type::Variants(ref ctors)) => {
                ctors.iter()
                    .enumerate()
                    .find(|&(_, c)| c.0 == *ctor_name)
                    .map(|(i, _)| i as VMIndex)
            }
            _ => None
        }
    }
    fn next_global_index(&self) -> VMIndex {
        self.globals.len() as VMIndex
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
                    .filter_map(|typ| match *typ {
                        Type::Variants(ref ctors) => ctors.iter().find(|ctor| ctor.0 == *id).map(|t| &t.1),
                        _ => None
                    })
                    .next()
                    .map(|ctor| ctor)
            }
        }
    }
    fn find_type_info(&self, id: &InternedStr) -> Option<&TcType> {
        self.type_infos.find_type_info(id)
    }
    fn find_type_name(&self, typ: &TcType) -> Option<TcType> {
        self.type_infos.find_id(typ)
    }
    fn find_record(&self, fields: &[InternedStr]) -> Option<(&TcType, &TcType)> {
        self.type_infos.find_record(fields)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Frame<'a> {
    offset: VMIndex,
    instruction_index: usize,
    upvars: Option<GcPtr<ClosureData<'a>>>,
    excess: bool
}

#[derive(Debug)]
pub struct Stack<'a> {
    values: Vec<Value<'a>>,
    frames: Vec<Frame<'a>>
}

impl <'a> Stack<'a> {

    fn new() -> Stack<'a> {
        Stack { values: Vec::new(), frames: Vec::new() }
    }

    pub fn get(&self, index: usize) -> Value<'a> {
        self.values[index].clone()
    }

    pub fn pop(&mut self) -> Value<'a> {
        self.values
            .pop()
            .expect("pop on empty stack")
    }

    pub fn set(&mut self, index: usize, v: Value<'a>) {
        self.values[index] = v;
    }

    pub fn push(&mut self, v: Value<'a>) {
        self.values.push(v)
    }

    pub fn len(&self) -> VMIndex {
        self.values.len() as VMIndex
    }

}

pub struct StackFrame<'a: 'b, 'b> {
    stack: RefMut<'b, Stack<'a>>,
    frame: Frame<'a>
}
impl <'a: 'b, 'b> StackFrame<'a, 'b> {
    pub fn new(v: RefMut<'b, Stack<'a>>, args: VMIndex, upvars: Option<GcPtr<ClosureData<'a>>>) -> StackFrame<'a, 'b> {
        let offset = v.len() - args;
        StackFrame {
            stack: v,
            frame: Frame { offset: offset, upvars: upvars, instruction_index: 0, excess: false }
        }
    }

    pub fn new_empty(vm: &'b VM<'a>) -> StackFrame<'a, 'b> {
        let stack = vm.stack.borrow_mut();
        StackFrame::new(stack, 0, None)
    }

    pub fn len(&self) -> VMIndex {
        self.stack.len() - self.frame.offset
    }

    pub fn push(&mut self, v: Value<'a>) {
        self.stack.values.push(v);
    }

    pub fn top(&mut self) -> &Value<'a> {
        self.stack.values.last().expect("StackFrame: top")
    }

    pub fn pop(&mut self) -> Value<'a> {
        self.stack.pop()
    }

    fn insert_slice(&mut self, index: VMIndex, values: &[Cell<Value<'a>>]) {
        self.stack.values.reserve(values.len());
        unsafe {
            let old_len = self.len();
            for i in (index..old_len).rev() {
                *self.get_unchecked_mut(i as usize + values.len()) = self[i];
            }
            for (i, val) in (index..).zip(values) {
                *self.get_unchecked_mut(i as usize) = val.get();
            }
            let new_len = self.stack.values.len() + values.len();
            self.stack.values.set_len(new_len);
        }
    }

    fn set_upvar(&self, index: VMIndex, v: Value<'a>) {
        let upvars = self.frame.upvars.as_ref().expect("Attempted to access upvar in non closure function");
        upvars.upvars[index as usize].set(v)
    }

    fn get_upvar(&self, index: VMIndex) -> Value<'a> {
        let upvars = self.frame.upvars.as_ref().expect("Attempted to access upvar in non closure function");
        upvars.upvars[index as usize].get()
    }

    fn as_slice(&self) -> &[Value<'a>] {
        &self.stack.values[self.frame.offset as usize..]
    }

    fn new_scope<E, F>(stack: RefMut<'b, Stack<'a>>
            , args: VMIndex
            , upvars: Option<GcPtr<ClosureData<'a>>>
            , f: F) -> Result<StackFrame<'a, 'b>, E> 
        where F: FnOnce(StackFrame<'a, 'b>) -> Result<StackFrame<'a, 'b>, E> {
        let stack = StackFrame::frame(stack, args, upvars);
        let mut stack = try!(f(stack));
        stack.stack.frames.pop();
        Ok(stack)
    }

    fn enter_scope(mut self
            , args: VMIndex
            , new_upvars: Option<GcPtr<ClosureData<'a>>>) -> StackFrame<'a, 'b> {
        *self.stack.frames.last_mut().expect("Frame") = self.frame;
        StackFrame::frame(self.stack, args, new_upvars)
    }

    fn exit_scope(mut self) -> StackFrame<'a, 'b> {
        self.stack.frames.pop().expect("Expected frame");
        let frame = self.stack.frames.last().cloned()
            .unwrap_or(Frame { offset: 0, upvars: None, instruction_index: 0, excess: false });
        StackFrame {
            stack: self.stack,
            frame: frame
        }
    }

    fn scope<E, F>(self
            , args: VMIndex
            , upvars: Option<GcPtr<ClosureData<'a>>>
            , f: F) -> Result<StackFrame<'a, 'b>, E>
        where F: FnOnce(StackFrame<'a, 'b>) -> Result<StackFrame<'a, 'b>, E> {
        let mut stack = self.enter_scope(args, upvars);
        stack = try!(f(stack));
        stack = stack.exit_scope();
        Ok(stack)
    }

    fn frame(mut stack: RefMut<'b, Stack<'a>>,
             args: VMIndex,
             upvars: Option<GcPtr<ClosureData<'a>>>
            ) -> StackFrame<'a, 'b> {
        assert!(stack.len() >= args);
        let offset = stack.len() - args;
        let frame = Frame { offset: offset, instruction_index: 0, upvars: upvars, excess: false };
        stack.frames.push(frame);
        StackFrame { stack: stack, frame: frame }
    }
}

impl <'a, 'b> Deref for StackFrame<'a, 'b> {
    type Target = [Value<'a>];
    fn deref(&self) -> &[Value<'a>] {
        &self.stack.values[self.frame.offset as usize..]
    }
}

impl <'a, 'b> DerefMut for StackFrame<'a, 'b> {
    fn deref_mut(&mut self) -> &mut [Value<'a>] {
        &mut self.stack.values[self.frame.offset as usize..]
    }
}

impl <'a, 'b> Index<VMIndex> for StackFrame<'a, 'b> {
    type Output = Value<'a>;
    fn index(&self, index: VMIndex) -> &Value<'a> {
        &self.stack.values[(self.frame.offset + index) as usize]
    }
}
impl <'a, 'b> IndexMut<VMIndex> for StackFrame<'a, 'b> {
    fn index_mut(&mut self, index: VMIndex) -> &mut Value<'a> {
        &mut self.stack.values[(self.frame.offset + index) as usize]
    }
}
impl <'a, 'b> Index<::std::ops::RangeFull> for StackFrame<'a, 'b> {
    type Output = [Value<'a>];
    fn index(&self, _: ::std::ops::RangeFull) -> &[Value<'a>] {
        &self.stack.values[self.frame.offset as usize..]
    }
}
impl <'a, 'b> IndexMut<::std::ops::RangeFull> for StackFrame<'a, 'b> {
    fn index_mut(&mut self, _: ::std::ops::RangeFull) -> &mut [Value<'a>] {
        &mut self.stack.values[self.frame.offset as usize..]
    }
}

struct Def<'a:'b, 'b> {
    tag: VMTag,
    elems: &'b mut [Value<'a>]
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
            unsafe {
                ::std::ptr::write(field.as_unsafe_cell().get(), value.clone());
            }
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
    interner: &'b mut Interner
}
impl <'a, 'b> Traverseable for Roots<'a, 'b> {
    fn traverse(&self, gc: &mut Gc) {
        for g in self.globals.borrow().iter() {
            g.traverse(gc);
        }
        self.stack.traverse(gc);
        //Also need to check the interned string table
        self.interner.traverse(gc);
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
            stack: RefCell::new(Stack::new())
        };
        {
            let a = Type::Generic(ast::Generic { kind: ast::Kind::Star, id: vm.intern("a") });
            let array_a = Type::Array(box a.clone());
            let io = |t| ast::type_con(vm.intern("IO"), vec![t]);
            let io_unit = io(UNIT_TYPE.clone());
            let _ = vm.extern_function("array_length", vec![array_a.clone()], INT_TYPE.clone(), box array_length);
            let _ = vm.extern_function("string_append", vec![STRING_TYPE.clone(), STRING_TYPE.clone()], STRING_TYPE.clone(), box string_append);
            let _ = vm.extern_function("print_int", vec![INT_TYPE.clone()], io_unit, box print_int);
            let _ = vm.extern_function("read_file", vec![STRING_TYPE.clone()], io(STRING_TYPE.clone()), box read_file);
            let _ = vm.extern_function("show_Int_prim", vec![INT_TYPE.clone()], STRING_TYPE.clone(), box show_prim);
            let _ = vm.extern_function("show_Float_prim", vec![FLOAT_TYPE.clone()], STRING_TYPE.clone(), box show_prim);
            let _ = vm.extern_function("#error", vec![STRING_TYPE.clone()], a.clone(), box error_prim);
        }
        vm
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

    pub fn get_type<T: Any>(&self) -> &TcType {
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

    pub fn extern_function(&self, name: &str, args: Vec<TcType>, return_type: TcType, f: Box<Fn(&VM<'a>) -> Status + 'static>) -> Result<(), ::std::string::String> {
        let id = self.intern(name);
        if self.names.borrow().contains_key(&id) {
            return Err(format!("{} is already defined", name))
        }
        let num_args = args.len() as VMIndex;
        let global = Global {
            id: id,
            typ: ast::fn_type(args, return_type),
            value: Cell::new(Function(self.gc.borrow_mut().alloc(Move(
                ExternFunction {
                    args: num_args,
                    function: f
                }))))
        };
        self.names.borrow_mut().insert(id, GlobalFn(self.globals.len()));
        self.globals.push(global);
        Ok(())
    }

    pub fn register_type<T: ?Sized + Any>(&mut self, name: &str) -> Result<&TcType, ()> {
        let n = self.intern(name);
        let mut type_infos = self.type_infos.borrow_mut();
        if type_infos.id_to_type.contains_key(&n) {
            Err(())
        }
        else {
            let id = TypeId::of::<T>();
            let typ = Type::Data(ast::TypeConstructor::Data(n), Vec::new());
            try!(self.typeids.try_insert(id, typ.clone()).map_err(|_| ()));
            let t = self.typeids.get(&id).unwrap();
            let ctor = Type::Variants(vec![(n, typ)]);
            type_infos.id_to_type.insert(n, ctor.clone());
            type_infos.type_to_id.insert(ctor, Type::Data(ast::TypeConstructor::Data(n), vec![]));
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
            names: self.names.borrow()
        }
    }

    pub fn collect(&self) {
        let mut stack = self.stack.borrow_mut();
        self.with_roots(&mut stack.values, |gc, mut roots| {
            unsafe { gc.collect(&mut roots); }
        })
    }

    #[allow(dead_code)]
    fn new_data(&self, tag: VMTag, fields: &mut [Value<'a>]) -> Value<'a> {
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
        let roots = Roots { globals: &self.globals, stack: stack, interner: &mut *interner };
        let mut gc = self.gc.borrow_mut();
        f(&mut gc, roots)
    }

    fn alloc<T: ?Sized, D>(&self, stack: &mut [Value<'a>], def: D) -> GcPtr<T>
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
            x => Err(format!("Tried to call a non function object: '{:?}'", x))
        }
    }

    pub fn call_bytecode(&self, args: VMIndex, closure: GcPtr<ClosureData<'a>>) -> VMResult<Value<'a>> {
        self.push(Closure(closure));
        let mut stack = StackFrame::frame(self.stack.borrow_mut(), args, Some(closure));
        stack = try!(self.execute(stack, &closure.function.instructions, &closure.function));
        let x = if stack.len() > 0 { stack.pop() } else { Int(0) };
        Ok(x)
    }

    fn execute_callable<'b>(&'b self, stack: StackFrame<'a, 'b>, function: &Callable<'a>)
            -> Result<(Option<GcPtr<ClosureData<'a>>>, StackFrame<'a, 'b>), ::std::string::String> {
        match *function {
            Callable::Closure(closure) => Ok((Some(closure), stack)),
            Callable::Extern(ref ext) => self.execute_function(stack, ext).map(|s| (None, s))
        }
    }

    fn execute_function<'b>(&'b self, stack: StackFrame<'a, 'b>, function: &ExternFunction<'a>) -> Result<StackFrame<'a, 'b>, ::std::string::String> {
        //Make sure that the stack is not borrowed during the external function call
        //Necessary since we do not know what will happen during the function call
        let StackFrame { stack, frame } = stack;
        drop(stack);
        let status = (function.function)(self);
        let mut stack = StackFrame { stack: self.stack.borrow_mut(), frame: frame };
        stack.frame = frame;
        match status {
            Status::Ok => Ok(stack),
            Status::Error => {
                match stack.pop() {
                    String(s) => Err(::std::string::String::from(&s[..])),
                    _ => Err(::std::string::String::from("Unexpected panic in VM"))
                }
            }
        }
    }

    fn call_function_with_upvars<'b>(&'b self
                                    , mut stack: StackFrame<'a, 'b>
                                    , args: VMIndex
                                    , required_args: VMIndex
                                    , callable: Callable<'a>
                                    ) -> Result<(Option<GcPtr<ClosureData<'a>>>, StackFrame<'a, 'b>), ::std::string::String> {
        debug!("cmp {} {}", args, required_args);
        match args.cmp(&required_args) {
            Ordering::Equal => self.execute_callable(stack, &callable),
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
                Ok((None, stack))
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
                debug!("xxxxxx {:?}", &(*stack)[..]);
                stack.frame.excess = true;
                self.execute_callable(stack, &callable)
            }
        }
    }

    fn do_call<'b>(&'b self, mut stack: StackFrame<'a, 'b>, args: VMIndex) -> Result<(Option<GcPtr<ClosureData<'a>>>, StackFrame<'a, 'b>), ::std::string::String> {
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
                let closure = app.function;
                let total_args = app.arguments.len() as VMIndex + args;
                let offset = stack.len() - args;
                stack.insert_slice(offset, &app.arguments);
                match closure.args().cmp(&total_args) {
                    Ordering::Equal => {
                        self.execute_callable(stack, &app.function)
                    }
                    Ordering::Greater => {
                        let app = {
                            let whole_stack = &mut stack.stack.values[..];
                            let arg_start = whole_stack.len() - total_args as usize;
                            let (pre_stack, fields) = whole_stack.split_at_mut(arg_start);
                            self.alloc(pre_stack, PartialApplicationDataDef(closure.clone(), &*fields))
                        };
                        for _ in 0..(total_args+1) {
                            stack.pop();
                        }
                        stack.push(PartialApplication(app));
                        Ok((None, stack))
                    }
                    Ordering::Less => {
                        //Should never happen as creating a partial application with more arguments
                        //than a function needs should not happen
                        panic!("Unimplemented")
                    }
                }
            }
            x => return Err(format!("Cannot call {:?}", x))
        }
    }

    pub fn execute<'b>(&'b self, stack: StackFrame<'a, 'b>, instructions: &[Instruction], function: &BytecodeFunction) -> Result<StackFrame<'a, 'b>, ::std::string::String> {
        let (mut cont, mut stack) = try!(self.execute_(stack, 0, instructions, function));
        debug!("IS {:?}", stack.stack.frames);
        loop {
            let (closure, i) = match cont {
                Some(closure) => {
                    stack = stack.enter_scope(closure.function.args, Some(closure));
                    (closure, 0)
                }
                None => {
                    let result = stack.pop();
                    debug!("Return {:?}", result);
                    let len = stack.len();
                    stack = stack.exit_scope();
                    for _ in 0..(len + 1) {
                        stack.pop();
                    }
                    if stack.frame.excess {
                        //The stack will not have excess arguments after they are added
                        stack.frame.excess = false;
                        match stack.pop() {
                            Data(excess) => {
                                debug!("Push excess args {:?}", &excess.fields);
                                stack.push(result);
                                for value in &excess.fields {
                                    stack.push(value.get());
                                }
                                let (new_cont, new_stack) = try!(self.do_call(stack, excess.fields.len() as VMIndex));
                                stack = new_stack;
                                if let Some(_) = new_cont {
                                    cont = new_cont;
                                    continue
                                }
                            }
                            x => panic!("Expected excess arguments found {:?}", x)
                        }
                    }
                    else {
                        stack.push(result);
                    }
                    cont = stack.frame.upvars;
                    match cont {
                        Some(closure) => (closure, stack.frame.instruction_index),
                        None => break
                    }
                }
            };
            debug!("Continue with {:?}\nAt: {}", closure.function.name, i);
            let (new_cont, new_stack) = try!(self.execute_(stack, i, &closure.function.instructions, &closure.function));
            debug!("Result {:?} {:?}", new_cont, &new_stack[..]);
            stack = new_stack;
            cont = new_cont;
        }
        Ok(stack)
    }
    pub fn execute_<'b>(&'b self,
                        mut stack: StackFrame<'a, 'b>,
                        mut index: usize,
                        instructions: &[Instruction],
                        function: &BytecodeFunction
                       ) -> Result<(Option<GcPtr<ClosureData<'a>>>, StackFrame<'a, 'b>), ::std::string::String> {
        debug!("Enter frame with {:?}", stack.as_slice());
        while let Some(&instr) = instructions.get(index) {
            debug!("{:?}: {:?}", index, instr);
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
                    match self.do_call(stack, args) {
                        Ok((None, new_stack)) => stack = new_stack,
                        result => return result
                    }
                }
                TailCall(args) => {
                    stack.frame.instruction_index = index + 1;
                    match self.do_call(stack, args) {
                        Ok((None, new_stack)) => stack = new_stack,
                        result => return result
                    }
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
                        x => return Err(format!("GetField on {:?}", x))
                    }
                }
                SetField(i) => {
                    let value = stack.pop();
                    let data = stack.pop();
                    match data {
                        Data(data) => {
                            data.fields[i as usize].set(value);
                        }
                        _ => return Err("Op SetField called on non data type".to_string())
                    }
                }
                TestTag(tag) => {
                    let x = match *stack.top() {
                        Data(ref data) => if data.tag == tag { 1 } else { 0 },
                        _ => return Err("Op TestTag called on non data type".to_string())
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
                        _ => return Err("Op Split called on non data type".to_string())
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
                        (x, y) => return Err(format!("Op GetIndex called on invalid types {:?} {:?}", x, y))
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
                        (x, y) => return Err(format!("Op SetIndex called on invalid types {:?} {:?}", x, y))
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
        Ok((None, stack))
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

fn array_length(vm: &VM) -> Status {
    match vm.pop() {
        Data(values) => {
            let i = values.fields.len();
            vm.push(Int(i as VMInt));
        }
        x => panic!("{:?}", x)
    }
    Status::Ok
}
fn string_append(vm: &VM) -> Status {
    let mut stack = StackFrame::new(vm.stack.borrow_mut(), 2, None);
    match (&stack[0], &stack[1]) {
        (&String(l), &String(r)) => {
            let mut s = ::std::string::String::with_capacity(l.len() + r.len());
            s.push_str(&l);
            s.push_str(&r);
            stack.push(String(vm.gc.borrow_mut().alloc(&s[..])));
        }
        _ => panic!()
    }
    Status::Ok
}
fn print_int(vm: &VM) -> Status {
    let stack = StackFrame::new(vm.stack.borrow_mut(), 1, None);
    match stack[0] {
        Int(i) => {
            print!("{}", i);
        }
        x => panic!("print_int called on: {:?}", x)
    }
    Status::Ok
}

fn read_file(vm: &VM) -> Status {
    let mut stack = StackFrame::new(vm.stack.borrow_mut(), 1, None);
    match stack.pop() {
        String(s) => {
            let mut buffer = ::std::string::String::new();
            let status = match File::open(&s[..]).and_then(|mut file| file.read_to_string(&mut buffer)) {
                Ok(_) => Status::Ok,
                Err(err) => {
                    use std::fmt::Write;
                    buffer.clear();
                    let _ = write!(&mut buffer, "{}", err);
                    Status::Error
                }
            };
            let s = vm.alloc(&mut stack.stack.values, &buffer[..]);
            stack.push(String(s));
            status
        }
        x => panic!("print_int called on: {:?}", x)
    }
}

fn show_prim(vm: &VM) -> Status  {
    let mut stack = StackFrame::new(vm.stack.borrow_mut(), 1, None);
    let s = match stack[0] {
        Int(i) => format!("{}", i),
        Float(f) => format!("{}", f),
        x => panic!("print_int called on: {:?}", x)
    };
    stack.push(String(vm.gc.borrow_mut().alloc(&s[..])));
    Status::Ok
}

fn error_prim(_: &VM) -> Status {
    //We expect a string as an argument to this function but we only return Status::Error
    //and let the caller take care of printing the message
    Status::Error
}

macro_rules! tryf(
    ($e:expr) => (try!(($e).map_err(|e| format!("{}", e))))
);

pub fn load_script(vm: &VM, name: &str, input: &str) -> Result<(), ::std::string::String> {
    let mut expr = tryf!(parse_expr(input, vm));
    let (type_infos, function, typ) = {
        let env = vm.env();
        let (typ, type_infos) = {
            let mut interner = vm.interner.borrow_mut();
            let mut gc = vm.gc.borrow_mut();
            let mut tc = Typecheck::new(&mut interner, &mut gc);
            tc.add_environment(&env);
            let typ = tryf!(tc.typecheck_expr(&mut expr));
            (typ, tc.type_infos)
        };
        let function = {
            let env = (&env, &type_infos);
            let mut interner = vm.interner.borrow_mut();
            let mut gc = vm.gc.borrow_mut();
            let mut compiler = Compiler::new(&env, &mut interner, &mut gc);
            compiler.compile_expr(&expr)
        };
        (type_infos, function, typ)
    };
    let function = BytecodeFunction::new(&mut vm.gc.borrow_mut(), function);
    let closure = vm.new_closure(function, &[]);
    let value = try!(vm.call_bytecode(0, closure));
    let id = vm.intern(name);
    vm.names.borrow_mut().insert(id, GlobalFn(vm.globals.len()));
    vm.globals.push(Global { id: id, typ: typ, value: Cell::new(value) });
    vm.type_infos.borrow_mut().extend(type_infos);
    Ok(())
}

pub fn parse_expr(input: &str, vm: &VM) -> Result<::ast::LExpr<TcIdent>, ::std::string::String> {
    let mut interner = vm.interner.borrow_mut();
    let mut gc = vm.gc.borrow_mut();
    ::parser::parse_tc(&mut gc, &mut interner, input)
        .map_err(|err| format!("{}", err))
}
pub fn typecheck_expr<'a>(vm: &VM<'a>, expr_str: &str) -> Result<(ast::LExpr<TcIdent>, TypeInfos), ::std::string::String> {
    let mut expr = try!(parse_expr(&expr_str, vm));
    let env = vm.env();
    let mut interner = vm.interner.borrow_mut();
    let mut gc = vm.gc.borrow_mut();
    let mut tc = Typecheck::new(&mut interner, &mut gc);
    tc.add_environment(&env);
    tryf!(tc.typecheck_expr(&mut expr));
    Ok((expr, tc.type_infos))
}

pub fn run_expr<'a>(vm: &VM<'a>, expr_str: &str) -> Result<Value<'a>, ::std::string::String> {
    let function = {
        let (expr, type_infos) = try!(typecheck_expr(vm, expr_str));
        let env = (vm.env(), &type_infos);
        let mut interner = vm.interner.borrow_mut();
        let mut gc = vm.gc.borrow_mut();
        let mut compiler = Compiler::new(&env, &mut interner, &mut gc);
        compiler.compile_expr(&expr)
    };
    let function = vm.new_function(function);
    let closure = vm.new_closure(function, &[]);
    let value = try!(vm.call_bytecode(0, closure));
    Ok(value)
}

pub fn run_function<'a: 'b, 'b>(vm: &'b VM<'a>, name: &str) -> VMResult<Value<'a>> {
    let func = match vm.globals.find(|g| &*g.id == name) {
        Some((_, f)) => f,
        None => return Err(format!("Undefined function {}", name))
    };
    vm.run_function(func)
}

#[cfg(test)]
mod tests {
    use super::{VM, load_script, run_expr};
    use super::Value::{Float, Int};

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
        let value = run_expr(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
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
        let value = run_expr(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
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
        let value = run_expr(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
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
        let value = run_expr(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
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
        let value = run_expr(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
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

        let value = run_expr(&mut vm, "Vec.add { x = 10, y = 5 } { x = 1, y = 2 }")
            .unwrap_or_else(|err| panic!("{}", err));
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
        let value = run_expr(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
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
        let value = run_expr(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
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
        let value = run_expr(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
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
        let value = run_expr(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
        assert_eq!(value, Int(2));
    }
    #[test]
    fn insert_stack_slice() {
        use std::cell::Cell;
        let _ = ::env_logger::init();
        let vm = VM::new();
        let _: Result<_, ()> = super::StackFrame::new_scope(vm.stack.borrow_mut(), 0, None, |mut stack| {
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
        let value = run_expr(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
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
        let value = run_expr(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
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
        let value = run_expr(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
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
        let value = run_expr(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
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
        run_expr(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
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
        let result = run_expr(&mut vm, text);
        assert!(result.is_err());
    }

    #[test]
    fn test_prelude() {
        use std::fs::File;
        use std::io::Read;
        let _ = ::env_logger::init();
        let mut text = String::new();
        File::open("std/prelude.hs").unwrap().read_to_string(&mut text).unwrap();
        let mut vm = VM::new();
        run_expr(&mut vm, &text)
            .unwrap_or_else(|err| panic!("{}", err));
    }
    #[test]
    fn test_map() {
        use std::fs::File;
        use std::io::Read;
        let _ = ::env_logger::init();
        let mut vm = VM::new();
        let mut text = String::new();
        File::open("std/prelude.hs").unwrap().read_to_string(&mut text).unwrap();
        load_script(&mut vm, "prelude", &text).unwrap();
        text.clear();
        File::open("std/map.hs").unwrap().read_to_string(&mut text).unwrap();
        run_expr(&mut vm, &text)
            .unwrap_or_else(|err| panic!("{}", err));
    }
}

