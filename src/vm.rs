use std::cell::{Cell, RefCell, RefMut, Ref};
use std::fmt;
use std::intrinsics::type_name;
use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::ops::{Deref, DerefMut, Index, IndexMut};
use base::ast;
use base::ast::Type;
use typecheck::{Typecheck, TypeEnv, TypeInfos, Typed, STRING_TYPE, INT_TYPE, TcIdent, TcType};
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
    Closure,
    TraitObject,
    Userdata,
    Bottom
};

#[derive(Copy, Clone)]
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

pub struct BytecodeFunction {
    instructions: Vec<Instruction>,
    inner_functions: Vec<GcPtr<BytecodeFunction>>,
    strings: Vec<InternedStr>
}

impl BytecodeFunction {
    pub fn empty() -> BytecodeFunction {
        BytecodeFunction { instructions: Vec::new(), inner_functions: Vec::new(), strings: Vec::new() }
    }

    pub fn new(gc: &mut Gc, f: CompiledFunction) -> GcPtr<BytecodeFunction> {
        let CompiledFunction { instructions, inner_functions, strings, .. } = f;
        let fs = inner_functions.into_iter()
            .map(|inner| BytecodeFunction::new(gc, inner))
            .collect();
        gc.alloc(Move(BytecodeFunction { instructions: instructions, inner_functions: fs, strings: strings }))
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
    Function(GcPtr<Function_<'a>>),
    Closure(GcPtr<ClosureData<'a>>),
    TraitObject(GcPtr<DataStruct<'a>>),
    Userdata(Userdata_),
    Bottom//Special value used to mark that a global was used before it was initialized
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
            _ => ()
        }
    }
}

impl <'a> fmt::Debug for Value<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Int(i) => write!(f, "{:?}", i),
            Float(x) => write!(f, "{:?}f", x),
            String(x) => write!(f, "\"{:?}\"", &*x),
            Data(ref data) => {
                write!(f, "{{{:?} {:?}}}", data.tag, &data.fields)
            }
            Function(ref func) => write!(f, "{:?}", **func),
            Closure(ref closure) => write!(f, "<Closure {:?}>", &closure.upvars),
            TraitObject(ref object) => write!(f, "<{:?} {:?}>", object.tag, &object.fields),
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

pub type ExternFunction<'a> = Box<Fn(&VM<'a>) + 'static>;

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

pub enum Function_<'a> {
    Bytecode(BytecodeFunction),
    Extern(ExternFunction<'a>)
}
impl <'a> Typed for Global<'a> {
    type Id = InternedStr;
    fn type_of(&self) -> &TcType {
        &self.typ
    }
}
impl <'a> PartialEq for Function_<'a> {
    fn eq(&self, _other: &Function_<'a>) -> bool {
        false//TODO?
    }
}

impl <'a> Traverseable for Function_<'a> {
    fn traverse(&self, gc: &mut Gc) {
        match *self { 
            Function_::Bytecode(ref f) => f.traverse(gc),
            Function_::Extern(_) => ()
        }
    }
}
impl <'a> fmt::Debug for Function_<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self { 
            Function_::Bytecode(_) => write!(f, "<Bytecode>"),
            Function_::Extern(_) => write!(f, "<extern>")
        }
    }
}

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
        match self.type_infos.datas.get(data_name) {
            Some(ctors) => {
                ctors.iter()
                    .enumerate()
                    .find(|&(_, c)| c.name.id() == ctor_name)
                    .map(|(i, _)| i as VMIndex)
            }
            None => None
        }
    }
    fn next_global_index(&self) -> VMIndex {
        self.globals.len() as VMIndex
    }
}

impl <'a, 'b> TypeEnv for VMEnv<'a, 'b> {
    fn find_type(&self, id: &InternedStr) -> Option<(&[ast::Constraint], &TcType)> {
        match self.names.get(id) {
            Some(&GlobalFn(index)) if index < self.globals.len() => {
                let g = &self.globals[index];
                Some((&[], &g.typ))
            }
            _ => {
                self.type_infos.datas.values()
                    .flat_map(|ctors| ctors.iter())
                    .find(|ctor| ctor.name.id() == id)
                    .map(|ctor| (&[][..], &ctor.name.typ))
            }
        }
    }
    fn find_type_info(&self, id: &InternedStr) -> Option<&[ast::Constructor<TcIdent>]> {
        self.type_infos.find_type_info(id)
    }
    fn find_type_name(&self, typ: &TcType) -> Option<&TcType> {
        self.type_infos.find_id(typ)
    }
}

pub struct Stack<'a> {
    values: Vec<Value<'a>>,
    frames: Vec<(VMIndex, Option<GcPtr<ClosureData<'a>>>)>
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
    offset: VMIndex,
    upvars: Option<GcPtr<ClosureData<'a>>>
}
impl <'a: 'b, 'b> StackFrame<'a, 'b> {
    pub fn new(v: RefMut<'b, Stack<'a>>, args: VMIndex, upvars: Option<GcPtr<ClosureData<'a>>>) -> StackFrame<'a, 'b> {
        let offset = v.len() - args;
        StackFrame { stack: v, offset: offset, upvars: upvars }
    }

    pub fn new_empty(vm: &'b VM<'a>) -> StackFrame<'a, 'b> {
        let stack = vm.stack.borrow_mut();
        let offset = stack.len();
        StackFrame { stack: stack, offset: offset, upvars: None }
    }

    pub fn len(&self) -> VMIndex {
        self.stack.len() - self.offset
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

    fn set_upvar(&self, index: VMIndex, v: Value<'a>) {
        let upvars = self.upvars.as_ref().expect("Attempted to access upvar in non closure function");
        upvars.upvars[index as usize].set(v)
    }

    fn get_upvar(&self, index: VMIndex) -> Value<'a> {
        let upvars = self.upvars.as_ref().expect("Attempted to access upvar in non closure function");
        upvars.upvars[index as usize].get()
    }

    fn as_slice(&self) -> &[Value<'a>] {
        &self.stack.values[self.offset as usize..]
    }

    fn as_mut_slice(&mut self) -> &mut [Value<'a>] {
        &mut self.stack.values[self.offset as usize..]
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
    fn scope<E, F>(self
            , args: VMIndex
            , new_upvars: Option<GcPtr<ClosureData<'a>>>
            , f: F) -> Result<StackFrame<'a, 'b>, E>
        where F: FnOnce(StackFrame<'a, 'b>) -> Result<StackFrame<'a, 'b>, E> {
        let StackFrame { stack: s, offset, upvars } = self;
        let new_stack = StackFrame::frame(s, args, new_upvars);
        let mut new_stack = try!(f(new_stack));
        new_stack.stack.frames.pop();
        Ok(StackFrame { stack: new_stack.stack, offset: offset, upvars: upvars })
    }

    fn frame(mut stack: RefMut<'b, Stack<'a>>, args: VMIndex, upvars: Option<GcPtr<ClosureData<'a>>>) -> StackFrame<'a, 'b> {
        assert!(stack.len() >= args);
        let offset = stack.len() - args;
        stack.frames.push((offset, upvars));
        StackFrame { stack: stack, offset: offset, upvars: upvars }
    }
}

impl <'a, 'b> Deref for StackFrame<'a, 'b> {
    type Target = [Value<'a>];
    fn deref(&self) -> &[Value<'a>] {
        &self.stack.values[self.offset as usize..]
    }
}

impl <'a, 'b> DerefMut for StackFrame<'a, 'b> {
    fn deref_mut(&mut self) -> &mut [Value<'a>] {
        &mut self.stack.values[self.offset as usize..]
    }
}

impl <'a, 'b> Index<VMIndex> for StackFrame<'a, 'b> {
    type Output = Value<'a>;
    fn index(&self, index: VMIndex) -> &Value<'a> {
        &self.stack.values[(self.offset + index) as usize]
    }
}
impl <'a, 'b> IndexMut<VMIndex> for StackFrame<'a, 'b> {
    fn index_mut(&mut self, index: VMIndex) -> &mut Value<'a> {
        &mut self.stack.values[(self.offset + index) as usize]
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
        let a = Type::Generic(vm.intern("a"));
        let array_a = Type::Array(box a.clone());
        let _ = vm.extern_function("array_length", vec![array_a.clone()], INT_TYPE.clone(), box array_length);
        let _ = vm.extern_function("string_append", vec![STRING_TYPE.clone(), STRING_TYPE.clone()], STRING_TYPE.clone(), box string_append);
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

    pub fn extern_function(&self, name: &str, args: Vec<TcType>, return_type: TcType, f: ExternFunction<'a>) -> Result<(), ::std::string::String> {
        let id = self.intern(name);
        if self.names.borrow().contains_key(&id) {
            return Err(format!("{} is already defined", name))
        }
        let global = Global {
            id: id,
            typ: Type::Function(args, box return_type),
            value: Cell::new(Function(self.gc.borrow_mut().alloc(Move(Function_::Extern(f)))))
        };
        self.names.borrow_mut().insert(id, GlobalFn(self.globals.len()));
        self.globals.push(global);
        Ok(())
    }

    pub fn register_type<T: ?Sized + Any>(&mut self, name: &str) -> Result<&TcType, ()> {
        let n = self.intern(name);
        let mut type_infos = self.type_infos.borrow_mut();
        if type_infos.datas.contains_key(&n) {
            Err(())
        }
        else {
            let id = TypeId::of::<T>();
            let typ = Type::Data(ast::TypeConstructor::Data(n), Vec::new());
            try!(self.typeids.try_insert(id, typ.clone()).map_err(|_| ()));
            let t = self.typeids.get(&id).unwrap();
            let ctor = ast::Constructor {
                name: TcIdent { name: n, typ: typ },
                arguments: ast::ConstructorType::Record(Vec::new())
            };
            type_infos.datas.insert(n, vec![ctor]);
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

    fn new_data(&self, tag: VMTag, fields: &mut [Value<'a>]) -> Value<'a> {
        Data(self.gc.borrow_mut().alloc(Def { tag: tag, elems: fields }))
    }
    fn new_data_and_collect(&self, stack: &mut [Value<'a>], tag: VMTag, fields: &mut [Value<'a>]) -> GcPtr<DataStruct<'a>> {
       self.alloc(stack, Def { tag: tag, elems: fields })
    }
    fn new_closure_and_collect(&self, stack: &mut [Value<'a>], func: GcPtr<BytecodeFunction>, fields: &mut [Value<'a>]) -> GcPtr<ClosureData<'a>> {
        self.alloc(stack, ClosureDataDef(func, &*fields))
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
                let stack = StackFrame::new(self.stack.borrow_mut(), args, None);
                let stack = self.execute_function(stack, &ptr);
                stack.map(|mut stack| { if stack.len() > 0 { stack.pop() } else { Int(0) } })
            }
            Closure(closure) => self.call_bytecode(args, &closure.function, Some(closure)),
            x => Err(format!("Tried to call a non function object: '{:?}'", x))
        }
    }

    pub fn call_bytecode(&self, args: VMIndex, bytecode: &BytecodeFunction, closure: Option<GcPtr<ClosureData<'a>>>) -> VMResult<Value<'a>> {
        let stack = StackFrame::new(self.stack.borrow_mut(), args, closure);
        let stack = self.execute(stack, &bytecode.instructions, &bytecode);
        stack.map(|mut stack| { if stack.len() > 0 { stack.pop() } else { Int(0) } })
    }

    fn execute_function<'b>(&'b self, stack: StackFrame<'a, 'b>, function: &Function_<'a>) -> Result<StackFrame<'a, 'b>, ::std::string::String> {
        match *function {
            Function_::Extern(ref func) => {
                //Make sure that the stack is not borrowed during the external function call
                //Necessary since we do not know what will happen during the function call
                let StackFrame { stack, offset, upvars } = stack;
                drop(stack);
                func(self);
                Ok(StackFrame::new(self.stack.borrow_mut(), offset, upvars))
            }
            Function_::Bytecode(ref function) => {
                self.execute(stack, &function.instructions, &function)
            }
        }
    }

    pub fn execute<'b>(&'b self, mut stack: StackFrame<'a, 'b>, instructions: &[Instruction], function: &BytecodeFunction) -> Result<StackFrame<'a, 'b>, ::std::string::String> {
        debug!("Enter frame with {:?}", stack.as_slice());
        let mut index = 0;
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
                    let function_index = stack.len() - 1 - args;
                    {
                        let f = stack[function_index].clone();
                        match f {
                            Function(ref f) => {
                                stack = try!(stack.scope(args, None, |new_stack| {
                                    self.execute_function(new_stack, f)
                                }));
                            }
                            Closure(ref closure) => {
                                stack = try!(stack.scope(args, Some(*closure), |new_stack| {
                                    self.execute(new_stack, &closure.function.instructions, &closure.function)
                                }));
                            }
                            x => return Err(format!("Cannot call {:?}", x))
                        }
                    }
                    if stack.len() > function_index + args {
                        //Value was returned
                        let result = stack.pop();
                        debug!("Return {:?}", result);
                        while stack.len() > function_index {
                            stack.pop();
                        }
                        stack.push(result);
                    }
                    else {
                        while stack.len() > function_index {
                            stack.pop();
                        }
                    }
                }
                Construct(tag, args) => {
                    let arg_start = (stack.len() - args) as usize;
                    let d = self.new_data(tag, &mut stack.as_mut_slice()[arg_start..]);
                    for _ in 0..args {
                        stack.pop();
                    } 
                    stack.push(d);
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
                        args.reverse();
                        let func = function.inner_functions[fi as usize];
                        Closure(self.new_closure_and_collect(stack_after, func, args))
                    };
                    for _ in 0..n {
                        stack.pop();
                    }
                    stack.push(closure);
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
        Ok(stack)
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

fn array_length(vm: &VM) {
    match vm.pop() {
        Data(values) => {
            let i = values.fields.len();
            vm.push(Int(i as VMInt));
        }
        x => panic!("{:?}", x)
    }
}
fn string_append(vm: &VM) {
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
}

macro_rules! tryf(
    ($e:expr) => (try!(($e).map_err(|e| format!("{}", e))))
);

pub fn load_script(vm: &VM, name: &str, input: &str) -> Result<(), ::std::string::String> {
    let empty_string = vm.intern("");
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
            let mut compiler = Compiler::new(&env, empty_string);
            compiler.compile_expr(&expr)
        };
        (type_infos, function, typ)
    };
    let function = BytecodeFunction::new(&mut vm.gc.borrow_mut(), function);
    let value = try!(vm.call_bytecode(0, &function, None));
    let id = vm.intern(name);
    vm.names.borrow_mut().insert(id, GlobalFn(vm.globals.len()));
    vm.globals.push(Global { id: id, typ: typ, value: Cell::new(value) });
    vm.type_infos.borrow_mut().extend(type_infos);
    Ok(())
}

pub fn parse_expr(input: &str, vm: &VM) -> Result<::ast::LExpr<TcIdent>, ::std::string::String> {
    let mut interner = vm.interner.borrow_mut();
    let mut gc = vm.gc.borrow_mut();
    ::parser_new::parse_tc(&mut gc, &mut interner, input)
        .map_err(|err| format!("{}", err))
}

pub fn run_expr<'a>(vm: &VM<'a>, expr_str: &str) -> Result<Value<'a>, ::std::string::String> {
    let mut expr = try!(parse_expr(&expr_str, vm));
    let function = {
        let empty_string = vm.intern("");
        let env = vm.env();
        let (typ, type_infos) = {
            let mut interner = vm.interner.borrow_mut();
            let mut gc = vm.gc.borrow_mut();
            let mut tc = Typecheck::new(&mut interner, &mut gc);
            tc.add_environment(&env);
            let typ = tryf!(tc.typecheck_expr(&mut expr));
            (typ, tc.type_infos)
        };
        let env = (&env, &type_infos);
        let mut compiler = Compiler::new(&env, empty_string);
        vm.new_function(compiler.compile_expr(&expr))
    };
    vm.call_bytecode(0, &function, None)
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
    fn record() {
        let text = 
r"
{ x: 0, y: 1.0, z: {} }
";
        let mut vm = VM::new();
        let value = run_expr(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
        let unit = vm.new_data(0, &mut []);
        assert_eq!(value, vm.new_data(0, &mut [Int(0), Float(1.0), unit]));
    }

    #[test]
    fn record_add() {
        let _ = ::env_logger::init();
        let text = 
r"
type T = { x: Int, y: Int } in
let add = \l r -> { x: l.x #Int+ r.x, y: l.y #Int+ r.y } in
add { x: 0, y: 1 } { x: 1, y: 1 }
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
let add = \l r -> { x: l.x #Int+ r.x, y: l.y #Int+ r.y } in
let sub = \l r -> { x: l.x #Int- r.x, y: l.y #Int- r.y } in
{ add: add, sub: sub }
";
        let mut vm = VM::new();
        load_script(&mut vm, "Vec", text)
            .unwrap_or_else(|err| panic!("{}", err));

        let value = run_expr(&mut vm, "Vec.add { x: 10, y: 5 } { x: 1, y: 2 }")
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
}

