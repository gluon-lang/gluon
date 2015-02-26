use std::cell::{Cell, RefCell, RefMut, Ref};
use std::fmt;
use std::intrinsics::get_tydesc;
use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::ops::{Deref, Index};
use ast;
use parser::Parser;
use typecheck::{Typecheck, TypeEnv, TypeInfos, Typed, STRING_TYPE, INT_TYPE, UNIT_TYPE, TcIdent, TcType, Constrained, match_types};
use ast::TypeEnum::*;
use compiler::*;
use compiler::Instruction::*;
use interner::{Interner, InternedStr};
use gc::{Gc, GcPtr, Traverseable, DataDef};
use fixed::*;

use self::Named::*;

pub use vm::Value::{
    Int,
    Float,
    String,
    Data,
    Function,
    Closure,
    TraitObject,
    Userdata};

#[derive(Copy, Clone)]
pub struct Userdata_ {
    pub data: GcPtr<RefCell<Box<Any>>>
}

impl Userdata_ {
    pub fn new<T: 'static>(vm: &VM, v: T) -> Userdata_ {
        Userdata_ { data: vm.gc.borrow_mut().alloc(UserDataDef(v)) }
    }
    fn ptr(&self) -> *const () {
        (&*self.data as *const RefCell<Box<Any>>) as *const ()
    }
}
impl PartialEq for Userdata_ {
    fn eq(&self, o: &Userdata_) -> bool {
        self.ptr() == o.ptr()
    }
}

struct UserDataDef<T>(T);

impl <T: 'static> DataDef for UserDataDef<T> {
    type Value = RefCell<Box<Any>>;
    fn size(&self) -> usize {
        use std::mem::size_of;
        size_of::< <Self as DataDef>::Value>()
    }
    fn initialize(self, result: *mut RefCell<Box<Any>>) {
        unsafe {
            ::std::ptr::write(result, RefCell::new(box self.0 as Box<Any>));
        }
    }
    fn make_ptr(&self, ptr: *mut ()) -> *mut RefCell<Box<Any>> {
        ptr as *mut _
    }
}

#[derive(Copy, Clone)]
pub struct DataStruct<'a> {
    value: GcPtr<Data_<'a>>
}

impl <'a> PartialEq for DataStruct<'a> {
    fn eq(&self, other: &DataStruct<'a>) -> bool {
        self.tag == other.tag && self.fields == other.fields
    }
}

impl <'a> Deref for DataStruct<'a> {
    type Target = Data_<'a>;
    fn deref(&self) -> &Data_<'a> {
        &*self.value
    }
}

pub struct Data_<'a> {
    tag: usize,
    fields: [Cell<Value<'a>>]
}

pub type VMInt = isize;

#[derive(Copy, Clone, PartialEq)]
pub enum Value<'a> {
    Int(VMInt),
    Float(f64),
    String(InternedStr),
    Data(DataStruct<'a>),
    Function(usize),
    Closure(DataStruct<'a>),
    TraitObject(DataStruct<'a>),
    Userdata(Userdata_)
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

impl <'a> Traverseable for Data_<'a> {
    fn traverse(&self, gc: &mut Gc) {
        self.fields.traverse(gc);
    }
}

impl <'a> Traverseable for Value<'a> {
    fn traverse(&self, gc: &mut Gc) {
        let ptr = match *self {
            Data(ref data) => data.value,
            Closure(ref data) => data.value,
            TraitObject(ref data) => data.value,
            _ => return
        };
        ptr.traverse(gc);
    }
}

impl <'a> fmt::Debug for Value<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Int(i) => write!(f, "{:?}", i),
            Float(x) => write!(f, "{:?}f", x),
            String(x) => write!(f, "\"{:?}\"", x),
            Data(ref data) => {
                write!(f, "{{{:?} {:?}}}", data.tag, &data.fields)
            }
            Function(i) => write!(f, "<function {:?}>", i),
            Closure(ref closure) => write!(f, "<Closure {:?} {:?}>", closure.tag, &closure.fields),
            TraitObject(ref object) => write!(f, "<{:?} {:?}>", object.tag, &object.fields),
            Userdata(ref data) => write!(f, "<Userdata {:?}>", data.ptr())
        }
    }
}

pub type ExternFunction<'a> = Box<Fn(&VM<'a>) + 'static>;

#[derive(Debug)]
pub struct Global<'a> {
    id: InternedStr,
    typ: Constrained<TcType>,
    value: Cell<Value<'a>>
}
enum Function_<'a> {
    Bytecode(Vec<Instruction>),
    Extern(ExternFunction<'a>)
}
impl <'a> Typed for Global<'a> {
    fn type_of(&self) -> &TcType {
        &self.typ.value
    }
}
impl <'a> fmt::Debug for Function_<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self { 
            Function_::Bytecode(ref is) => write!(f, "Bytecode {:?}", is),
            Function_::Extern(_) => write!(f, "<extern>")
        }
    }
}

enum Named {
    GlobalFn(usize),
    TraitFn(InternedStr, usize),
}

pub struct VM<'a> {
    functions: FixedVec<Function_<'a>>,
    globals: FixedVec<Global<'a>>,
    trait_indexes: FixedVec<TraitFunctions>,
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
    trait_indexes: &'b FixedVec<TraitFunctions>,
    globals: &'b FixedVec<Global<'a>>,
    functions: &'b FixedVec<Function_<'a>>,
    names: Ref<'b, HashMap<InternedStr, Named>>
}

impl <'a, 'b> CompilerEnv for VMEnv<'a, 'b> {
    fn find_var(&self, id: &InternedStr) -> Option<Variable> {
        match self.names.get(id) {
            Some(&GlobalFn(index)) if index < self.globals.len() => {
                let g = &self.globals[index];
                Some(Variable::Global(index, g.typ.constraints.as_slice(), &g.typ.value))
            }
            Some(&TraitFn(trait_index, function_index)) => {
                self.type_infos.traits
                    .get(&trait_index)
                    .and_then(|functions| {
                        if function_index < functions.len() {
                            Some(Variable::TraitFunction(&functions[function_index].1.value))
                        }
                        else {
                            None
                        }
                    })
            }
            _ => {
                self.type_infos.datas.values()
                    .flat_map(|ctors| ctors.iter().enumerate())
                    .find(|ctor| ctor.1.name.id() == id)
                    .map(|(i, ctor)| Variable::Constructor(i, ctor.arguments.len()))
            }
        }
    }
    fn find_field(&self, struct_: &InternedStr, field: &InternedStr) -> Option<usize> {
        panic!("find field {} {}", struct_, field)
    }

    fn find_tag(&self, data_name: &InternedStr, ctor_name: &InternedStr) -> Option<usize> {
        match self.type_infos.datas.get(data_name) {
            Some(ctors) => {
                ctors.iter()
                    .enumerate()
                    .find(|&(_, c)| c.name.id() == ctor_name)
                    .map(|(i, _)| i)
            }
            None => None
        }
    }
    fn find_trait_offset(&self, trait_name: &InternedStr, trait_type: &TcType) -> Option<usize> {
        self.trait_indexes
            .find(|func| func.trait_name == *trait_name && match_types(&func.impl_type, trait_type))
            .map(|(_, func)| func.index)
    }
    fn find_trait_function(&self, typ: &TcType, fn_name: &InternedStr) -> Option<TypeResult<usize>> {
        self.names.get(fn_name).and_then(|named| {
            match *named {
                TraitFn(ref trait_name, _) => {
                    match (self.find_object_function(trait_name, fn_name), self.find_trait_offset(trait_name, typ)) {
                        (Some(function_offset), Some(trait_offset)) => {
                            debug!("{} {} {}", function_offset, trait_offset, self.globals.len());
                            let global_index = function_offset + trait_offset;
                            let global = &self.globals[global_index];
                            Some(TypeResult {
                                constraints: global.typ.constraints.as_slice(),
                                typ: &global.typ.value,
                                value: global_index
                            })
                        }
                        _ => None
                    }
                }
                _ =>  None
            }
        })
    }
    fn find_object_function(&self, trait_name: &InternedStr, fn_name: &InternedStr) -> Option<usize> {
        self.type_infos.traits
            .get(trait_name)
            .and_then(|trait_info| 
                trait_info.iter()
                    .enumerate()
                    .find(|&(_, tup)| tup.0 == *fn_name)
                    .map(|(i, _)| i)
            )
    }
    fn next_function_index(&self) -> usize {
        self.functions.len()
    }
    fn next_global_index(&self) -> usize {
        self.globals.len()
    }
}

impl <'a, 'b> TypeEnv for VMEnv<'a, 'b> {
    fn find_type(&self, id: &InternedStr) -> Option<(&[ast::Constraint], &TcType)> {
        match self.names.get(id) {
            Some(&GlobalFn(index)) if index < self.globals.len() => {
                let g = &self.globals[index];
                Some((g.typ.constraints.as_slice(), &g.typ.value))
            }
            Some(&TraitFn(trait_index, function_index)) => {
                self.type_infos.traits
                    .get(&trait_index)
                    .and_then(|functions| {
                        if function_index < functions.len() {
                            let f = &functions[function_index].1;
                            Some((f.constraints.as_slice(), &f.value))
                        }
                        else {
                            None
                        }
                    })
            }
            _ => {
                self.type_infos.datas.values()
                    .flat_map(|ctors| ctors.iter())
                    .find(|ctor| ctor.name.id() == id)
                    .map(|ctor| ([].as_slice(), &ctor.name.typ))
            }
        }
    }
    fn find_type_info(&self, id: &InternedStr) -> Option<&[ast::Constructor<TcIdent>]> {
        self.type_infos.find_type_info(id)
    }
}

pub struct Stack<'a> {
    values: Vec<Value<'a>>,
    frames: Vec<(usize, Option<GcPtr<Data_<'a>>>)>
}

impl <'a, 'b, 'c> Stack<'a> {

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

    pub fn len(&self) -> usize {
        self.values.len()
    }

}

pub struct StackFrame<'a: 'b, 'b> {
    stack: RefMut<'b, Stack<'a>>,
    offset: usize,
    upvars: Option<GcPtr<Data_<'a>>>
}
impl <'a: 'b, 'b> StackFrame<'a, 'b> {
    pub fn new(v: RefMut<'b, Stack<'a>>, args: usize, upvars: Option<GcPtr<Data_<'a>>>) -> StackFrame<'a, 'b> {
        let offset = v.len() - args;
        StackFrame { stack: v, offset: offset, upvars: upvars }
    }

    pub fn new_empty(vm: &'b VM<'a>) -> StackFrame<'a, 'b> {
        let stack = vm.stack.borrow_mut();
        let offset = stack.len();
        StackFrame { stack: stack, offset: offset, upvars: None }
    }

    pub fn len(&self) -> usize {
        self.stack.len() - self.offset
    }

    pub fn get(&self, i: usize) -> &Value<'a> {
        &self.stack.values[self.offset + i]
    }

    pub fn get_mut(&mut self, i: usize) -> &mut Value<'a> {
        &mut self.stack.values[self.offset + i]
    }

    pub fn push(&mut self, v: Value<'a>) {
        self.stack.values.push(v);
    }

    pub fn top(&mut self) -> &Value<'a> {
        self.stack.values.last().unwrap()
    }

    pub fn pop(&mut self) -> Value<'a> {
        self.stack.pop()
    }

    fn get_upvar(&self, index: usize) -> Value<'a> {
        let upvars = self.upvars.as_ref().expect("Attempted to access upvar in non closure function");
        upvars.fields[index].get()
    }

    fn as_slice(&self) -> &[Value<'a>] {
        &self.stack.values[self.offset..]
    }

    fn as_mut_slice(&mut self) -> &mut [Value<'a>] {
        &mut self.stack.values[self.offset..]
    }

    fn new_scope<E, F>(stack: RefMut<'b, Stack<'a>>
            , args: usize
            , upvars: Option<GcPtr<Data_<'a>>>
            , f: F) -> Result<StackFrame<'a, 'b>, E> 
        where F: FnOnce(StackFrame<'a, 'b>) -> Result<StackFrame<'a, 'b>, E> {
        let stack = StackFrame::frame(stack, args, upvars);
        let mut stack = try!(f(stack));
        stack.stack.frames.pop();
        Ok(stack)
    }
    fn scope<E, F>(self
            , args: usize
            , new_upvars: Option<GcPtr<Data_<'a>>>
            , f: F) -> Result<StackFrame<'a, 'b>, E>
        where F: FnOnce(StackFrame<'a, 'b>) -> Result<StackFrame<'a, 'b>, E> {
        let StackFrame { stack: s, offset, upvars } = self;
        let new_stack = StackFrame::frame(s, args, new_upvars);
        let mut new_stack = try!(f(new_stack));
        new_stack.stack.frames.pop();
        Ok(StackFrame { stack: new_stack.stack, offset: offset, upvars: upvars })
    }

    fn frame(mut stack: RefMut<'b, Stack<'a>>, args: usize, upvars: Option<GcPtr<Data_<'a>>>) -> StackFrame<'a, 'b> {
        assert!(stack.len() >= args);
        let offset = stack.len() - args;
        stack.frames.push((offset, upvars));
        StackFrame { stack: stack, offset: offset, upvars: upvars }
    }
}

impl <'a, 'b, 'c> Index<usize> for StackFrame<'a, 'b> {
    type Output = Value<'a>;
    fn index(&self, index: &usize) -> &Value<'a> {
        &self.stack.values[self.offset + *index]
    }
}

struct Def<'a:'b, 'b> {
    tag: usize,
    elems: &'b mut [Value<'a>]
}
impl <'a, 'b> DataDef for Def<'a, 'b> {
    type Value = Data_<'a>;
    fn size(&self) -> usize {
        use std::mem::size_of;
        size_of::<usize>() + size_of::<Value<'a>>() * self.elems.len()
    }
    fn initialize(self, result: *mut Data_<'a>) {
        let result = unsafe { &mut *result };
        result.tag = self.tag;
        for (field, value) in result.fields.iter().zip(self.elems.iter()) {
            unsafe {
                ::std::ptr::write(field.as_unsafe_cell().get(), value.clone());
            }
        }
    }
    fn make_ptr(&self, ptr: *mut ()) -> *mut Data_<'a> {
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
    stack: &'b mut [Value<'a>],
    interner: &'b mut Interner
}
impl <'a, 'b> Traverseable for Roots<'a, 'b> {
    fn traverse(&self, gc: &mut Gc) {
        self.stack.traverse(gc);
        //Also need to check the interned string table
        self.interner.traverse(gc);
    }
}

impl <'a> VM<'a> {
    
    pub fn new() -> VM<'a> {
        let vm = VM {
            globals: FixedVec::new(),
            functions: FixedVec::new(),
            trait_indexes: FixedVec::new(),
            type_infos: RefCell::new(TypeInfos::new()),
            typeids: FixedMap::new(),
            interner: RefCell::new(Interner::new()),
            names: RefCell::new(HashMap::new()),
            gc: RefCell::new(Gc::new()),
            stack: RefCell::new(Stack::new())
        };
        let a = Generic(vm.intern("a"));
        let array_a = ArrayType(box a.clone());
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

    pub fn new_functions(&self, Assembly { initializer, anonymous_functions, trait_functions: indexes, globals }: Assembly) {
        let mut names = self.names.borrow_mut();
        for trait_index in indexes.into_iter() {
            //First index of this impl's functions
            let start_index = trait_index.index - self.functions.len();
            let id = match globals[start_index] {
                Binding::Function(ref id, _, _) => id,
                _ => panic!()
            };
            let is_registered = match names.get(id) {
                Some(&TraitFn(..)) => true,
                None => false,
                _ => panic!()
            };
            if !is_registered {
                match self.type_infos.borrow().traits.get(&trait_index.trait_name) {
                    Some(trait_fns) => {
                        for (i, &(trait_fn, _)) in trait_fns.iter().enumerate() {
                            debug!("Register trait fn '{}'", trait_fn);
                            names.insert(trait_fn, TraitFn(trait_index.trait_name, i));
                        }
                    }
                    None => panic!()
                }
            }
            self.trait_indexes.push(trait_index);
        }
        for global in globals {
            let g = match global {
                Binding::Function(id, typ, index) => {
                    match names.get(&id) {
                        Some(&GlobalFn(..)) => panic!("ICE: Global '{}' already exists", id),
                        Some(&TraitFn(..)) => (),
                        None => {
                            names.insert(id, GlobalFn(self.functions.len()));
                        }
                    }
                    Global { id: id, typ: typ, value: Cell::new(Function(index)) }
                }
                Binding::Other(id, typ) => {
                    Global { id: id, typ: typ, value: Cell::new(Int(0)) }
                }
            };
            self.globals.push(g);
        }
        for f in anonymous_functions {
            let CompiledFunction { instructions, id, .. } = f;
            debug!("Function {} at {}", id, self.functions.len());
            self.functions.push(Function_::Bytecode(instructions));
        }
        debug!("Run initializer");
        self.execute_instructions(&initializer).unwrap();
        debug!("Done initializer");
    }

    pub fn get_global(&self, name: &str) -> Option<(usize, &Global<'a>)> {
        let n = self.intern(name);
        self.globals.find(|g| n == g.id)
    }

    pub fn get_type<T: 'static>(&self) -> &TcType {
        let id = TypeId::of::<T>();
        self.typeids.get(&id)
            .unwrap_or_else(|| {
                let desc = unsafe { get_tydesc::<T>() };
                let name = if !desc.is_null() {
                    unsafe { &*desc }.name
                }
                else {
                    ""
                };
                panic!("Expected type {} to be inserted before get_type call", name)
            })
    }

    pub fn run_function(&self, cf: &Global<'a>) -> VMResult<Value<'a>> {
        self.call_function(0, None, cf)
    }

    pub fn execute_instructions(&self, instructions: &[Instruction]) -> VMResult<Value<'a>> {
        let stack = self.stack.borrow_mut();
        let frame = StackFrame::new_scope(stack, 0, None, |frame| {
            self.execute(frame, instructions)
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
            typ: Constrained { constraints: Vec::new(), value: FunctionType(args, box return_type) },
            value: Cell::new(Function(self.functions.borrow().len()))
        };
        self.names.borrow_mut().insert(id, GlobalFn(self.functions.len()));
        self.functions.push(Function_::Extern(f));
        self.globals.push(global);
        Ok(())
    }

    pub fn register_type<T: 'static>(&mut self, name: &str) -> Result<&TcType, ()> {
        let n = self.intern(name);
        let mut type_infos = self.type_infos.borrow_mut();
        if type_infos.datas.contains_key(&n) {
            Err(())
        }
        else {
            let id = TypeId::of::<T>();
            let typ = Type(n, Vec::new());
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
            trait_indexes: &self.trait_indexes,
            globals: &self.globals,
            functions: &self.functions,
            names: self.names.borrow()
        }
    }

    pub fn collect(&self) {
        let mut interner = self.interner.borrow_mut();
        let mut stack = self.stack.borrow_mut();
        let mut roots = Roots { stack: &mut *stack.values, interner: &mut *interner };
        self.gc.borrow_mut().collect(&mut roots);
    }

    fn new_data(&self, tag: usize, fields: &mut [Value<'a>]) -> Value<'a> {
        Data(DataStruct { value: self.gc.borrow_mut().alloc(Def { tag: tag, elems: fields })})
    }
    fn new_data_and_collect(&self, stack: &mut [Value<'a>], tag: usize, fields: &mut [Value<'a>]) -> DataStruct<'a> {
        let mut interner = self.interner.borrow_mut();
        let mut roots = Roots { stack: stack, interner: &mut *interner };
        let mut gc = self.gc.borrow_mut();
        DataStruct { value: gc.alloc_and_collect(&mut roots, Def { tag: tag, elems: fields }) }
    }

    pub fn call_function<'b, 'c>(&self, args: usize, upvars: Option<GcPtr<Data_<'a>>>, global: &Global<'a>) -> VMResult<Value<'a>>  {
        debug!("Call function {:?}", global);
        let i = match global.value.get() {
            Function(i) if i < self.functions.len() => i,
            Closure(d) if d.tag < self.functions.len() => d.tag,
            x => return Err(format!("Tried to call a non function object: '{:?}' / {}", x, self.functions.len()))
        };
        let function = &self.functions[i];
        let stack = StackFrame::new(self.stack.borrow_mut(), args, upvars);
        self.execute_function(stack, function)
            .map(|mut stack| { if stack.len() > 0 { stack.pop() } else { Int(0) } })
    }
    fn execute_function<'b, 'c>(&'b self, stack: StackFrame<'a, 'b>, function: &Function_<'a>) -> Result<StackFrame<'a, 'b>, ::std::string::String> {
        match *function {
            Function_::Extern(ref func) => {
                //Make sure that the stack is not borrowed during the external function call
                //Necessary since we do not know what will happen during the function call
                let StackFrame { stack, offset, upvars } = stack;
                drop(stack);
                func(self);
                Ok(StackFrame::new(self.stack.borrow_mut(), offset, upvars))
            }
            Function_::Bytecode(ref instructions) => {
                self.execute(stack, instructions.as_slice())
            }
        }
    }

    pub fn execute<'b>(&'b self, mut stack: StackFrame<'a, 'b>, instructions: &[Instruction]) -> Result<StackFrame<'a, 'b>, ::std::string::String> {
        debug!("Enter frame with {:?}", stack.as_slice());
        let mut index = 0;
        while index < instructions.len() {
            let instr = instructions[index];
            debug!("{:?}: {:?}", index, instr);
            match instr {
                Push(i) => {
                    let v = stack.get(i).clone();
                    stack.push(v);
                }
                PushInt(i) => {
                    stack.push(Int(i));
                }
                PushString(s) => {
                    stack.push(String(s));
                }
                PushGlobal(i) => {
                    stack.push(self.globals[i].value.get());
                }
                PushFloat(f) => stack.push(Float(f)),
                Store(i) => {
                    *stack.get_mut(i) = stack.pop();
                }
                StoreGlobal(i) => {
                    let v = stack.pop();
                    self.globals[i].value.set(v);
                }
                CallGlobal(args) => {
                    let function_index = stack.len() - 1 - args;
                    {
                        let f = stack.get(function_index).clone();
                        let (function, new_upvars) = match f {
                            Function(index) => {
                                (&self.functions[index], None)
                            }
                            Closure(ref closure) => {
                                (&self.functions[closure.tag], Some(closure.value))
                            }
                            x => return Err(format!("Cannot call {:?}", x))
                        };
                        stack = try!(stack.scope(args, new_upvars, |new_stack| {
                            self.execute_function(new_stack, function)
                        }));
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
                    let arg_start = stack.len() - args;
                    let d = self.new_data(tag, &mut stack.as_mut_slice()[arg_start..]);
                    for _ in range(0, args) {
                        stack.pop();
                    } 
                    stack.push(d);
                }
                GetField(i) => {
                    match stack.pop() {
                        Data(data) => {
                            let v = data.fields[i].get();
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
                            data.fields[i].set(value);
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
                    index = i;
                    continue
                }
                CJump(i) => {
                    match stack.pop() {
                        Int(0) => (),
                        _ => {
                            index = i;
                            continue
                        }
                    }
                }
                Pop(n) => {
                    for _ in range(0, n) {
                        stack.pop();
                    }
                }
                Slide(n) => {
                    let v = stack.pop();
                    for _ in range(0, n) {
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
                        let (stack_after, args) = stack.stack.values.split_at_mut(i);
                        args.reverse();
                        Closure(self.new_data_and_collect(stack_after, fi, args))
                    };
                    for _ in range(0, n) {
                        stack.pop();
                    }
                    stack.push(closure);
                }
                PushUpVar(i) => {
                    let v = stack.get_upvar(i).clone();
                    stack.push(v);
                }
                StoreUpVar(i) => {
                    let v = stack.pop();
                    stack.upvars.expect("Upvar").fields[i].set(v);
                }
                ConstructTraitObject(i) => {
                    let mut v = stack.pop();
                    let v = ::std::slice::mut_ref_slice(&mut v);
                    let object = TraitObject(self.new_data_and_collect(stack.stack.values.as_mut_slice(), i, v));
                    stack.push(object);
                }
                PushTraitFunction(i) => {
                    let func = match stack.top() {
                        &TraitObject(ref object) => {
                            Function(object.tag + i)
                        }
                        _ => return Err(format!("Op PushTraitFunction called on object other than a TraitObject"))
                    };
                    stack.push(func);
                }
                Unpack => {
                    match stack.pop() {
                        TraitObject(ref obj) => stack.push(obj.fields[0].get().clone()),
                        _ => return Err(format!("Op Unpack called on object other than a TraitObject"))
                    }
                }
                PushDictionaryMember(trait_index, function_offset) => {
                    let func = match stack.get_upvar(0).clone()  {
                        Data(dict) => {
                            match dict.fields[trait_index as usize].get() {
                                Closure(d) => self.globals[d.tag + function_offset as usize].value.get(),
                                x => panic!("PushDictionaryMember {:?}", x)
                            }
                        }
                        ref x => panic!("PushDictionaryMember {:?}", x)
                    };
                    stack.push(func);
                }
                PushDictionary(index) => {
                    let dict = stack.get_upvar(0).clone();
                    let dict = match dict {
                        Data(data) => data.fields[index].get(),
                        _ => panic!()
                    };
                    stack.push(dict);
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
            let l = l.as_slice();
            let r = r.as_slice();
            let mut s = ::std::string::String::with_capacity(l.len() + r.len());
            s.push_str(l);
            s.push_str(r);
            let result = vm.intern(s.as_slice());
            stack.push(String(result));
        }
        _ => panic!()
    }
}

macro_rules! tryf(
    ($e:expr) => (try!(($e).map_err(|e| format!("{:?}", e))))
);

pub fn parse_expr(buffer: &mut Buffer, vm: &VM) -> Result<::ast::LExpr<TcIdent>, ::std::string::String> {
    let mut interner = vm.interner.borrow_mut();
        let mut gc = vm.gc.borrow_mut();
    let mut parser = Parser::new(&mut *interner, &mut *gc, buffer, |s| TcIdent { name: s, typ: UNIT_TYPE.clone() });
    parser.expression().map_err(|err| format!("{:?}", err))
}

pub fn load_script(vm: &VM, buffer: &mut Buffer) -> Result<(), ::std::string::String> {
    use parser::Parser;

    let mut module = {
        let mut cell = vm.interner.borrow_mut();
        let mut gc = vm.gc.borrow_mut();
        let mut parser = Parser::new(&mut*cell, &mut *gc, buffer, |s| TcIdent { typ: UNIT_TYPE.clone(), name: s });
        tryf!(parser.module())
    };
    let (type_infos, functions) = {
        let env = vm.env();
        let mut tc = Typecheck::new();
        tc.add_environment(&env);
        tryf!(tc.typecheck_module(&mut module));
        let env = (vm.env(), &module);
        let mut compiler = Compiler::new(&env);
        (tc.type_infos, compiler.compile_module(&module))
    };
    vm.type_infos.borrow_mut().extend(type_infos);
    vm.new_functions(functions);
    Ok(())
}

pub fn run_main<'a>(vm: &VM<'a>, s: &str) -> VMResult<Value<'a>> {
    use std::old_io::BufReader;
    let mut buffer = BufReader::new(s.as_bytes());
    run_buffer_main(vm, &mut buffer)
}
pub fn run_buffer_main<'a>(vm: &VM<'a>, buffer: &mut Buffer) -> VMResult<Value<'a>> {
    try!(load_script(vm, buffer));
    let v = try!(run_function(vm, "main"));
    Ok(v)
}

pub fn run_function<'a: 'b, 'b>(vm: &'b VM<'a>, name: &str) -> VMResult<Value<'a>> {
    let func = match vm.globals.find(|g| g.id.as_slice() == name) {
        Some((_, f)) => f,
        None => return Err(format!("Undefined function {}", name))
    };
    vm.run_function(func)
}

#[cfg(test)]
mod tests {
    use super::{VM, Data, Int, String, run_main, run_function, load_script};
    use ast::INT_TYPE;
    use std::old_io::BufReader;
    ///Test that the stack is adjusted correctly after executing expressions as statements
    #[test]
    fn stack_for_block() {
        let text =
r"
main : () -> Int;
main = \ -> {
    10 + 2;
    let y = {
        let a = 1000;
        let b = 1000;
    };
    let x = {
        let z = 1;
        z + 2
    };
    x = x * 2 + 2;
    x
}
";
        let mut vm = VM::new();
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
        assert_eq!(value, Int(8));
    }

    #[test]
    fn unpack_enum() {
        let text =
r"
main : () -> Int;
main = \ -> {
    match A(8) {
        A(x) => { x }
        B(y) => { 0 }
    }
}
data AB = A(Int) | B(Float)
";
        let mut vm = VM::new();
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
        assert_eq!(value, Int(8));
    }
    #[test]
    fn call_trait_function() {
        let text =
r"
main : () -> Vec;
main = \ -> {
    let x = Vec(1, 2);
    x = add(x, Vec(10, 0));
    x.y = add(x.y, 3);
    x
}
data Vec = Vec {
    x: Int,
    y: Int
}

trait Add a {
    add : (a, a) -> a;
}

impl Add for Vec {
    add : (Vec, Vec) -> Vec;
    add = \l r -> {
        Vec(l.x + r.x, l.y + r.y)
    }
}
impl Add for Int {
    add : (Int, Int) -> Int;
    add = \l r -> {
        l + r
    }
}
";
        let mut vm = VM::new();
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
        match value {
            Data(ref data) => {
                assert_eq!(&data.fields, [Int(11), Int(5)].as_slice());
            }
            _ => panic!()
        }
    }
    #[test]
    fn pass_function_value() {
        let text = 
r"
main : () -> Int;
main = \ -> {
    test(lazy)
}
lazy : () -> Int;
lazy = \ -> {
    42
}

test : (() -> Int) -> Int;
test = \f -> {
    f() + 10
}
";
        let mut vm = VM::new();
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
        assert_eq!(value, Int(52));
    }
    #[test]
    fn arrays() {
        let text = 
r"
main : () -> [Int];
main = \ -> {
    let x = [10, 20, 30];
    [1,2, x[2] + 3]
}
";
        let mut vm = VM::new();
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
        match value {
            Data(ref data) => {
                assert_eq!(&data.fields, [Int(1), Int(2), Int(33)].as_slice());
            }
            _ => panic!()
        }
    }
    #[test]
    fn array_assign() {
        let text = 
r"
main : () -> Int;
main = \ -> {
    let x = [10, 20, 30];
    x[2] = x[2] + 10;
    x[2]
}
";
        let mut vm = VM::new();
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
        assert_eq!(value, Int(40));
    }
    #[test]
    fn lambda() {
        let text = 
r"
main : () -> Int;
main = \ -> {
    let y = 100;
    let f = \x -> {
        y = y + x;
        y + 1
    };
    f(22)
}
";
        let mut vm = VM::new();
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
        assert_eq!(value, Int(123));
    }

    #[test]
    fn trait_object() {
        let text = 
r"

trait Collection a {
    len : (a) -> Int;
}
impl Collection for [Int] {
    len : ([Int]) -> Int;
    len = \x -> {
        array_length(x)
    }
}

test : (Collection) -> Int;
test = \c -> {
    len(c)
}

main : () -> Int;
main = \ -> {
    test([0, 0, 0])
}
";
        let mut vm = VM::new();
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
        assert_eq!(value, Int(3));
    }

    #[test]
    fn upvar_index() {
        let text = 
r"
main : () -> Int;
main = \ -> {
    let x = 100;
    let f = \y -> x + y;
    f(10)
}
";
        let mut vm = VM::new();
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
        assert_eq!(value, Int(110));
    }

    #[test]
    fn call_generic_constrained_function() {
        let text = 
r"
trait Eq a {
    eq : (a, a) -> Bool;
}
data Option a = Some(a) | None()

impl Eq for Int {
    eq : (Int, Int) -> Bool;
    eq = \l r -> {
        l == r
    }
}
impl <Eq a> Eq for Option a {
    eq : (Option a, Option a) -> Bool;
    eq = \l r -> {
        match l {
            Some(l_val) => {
                match r {
                    Some(r_val) => { eq(l_val, r_val) }
                    None() => { false }
                }
            }
            None() => {
                match r {
                    Some(_) => { false }
                    None() => { true }
                }
            }
        }
    }
}
data Pair = Pair {
    x: Bool,
    y: Bool
}
main : () -> Pair;
main = \ -> {
    let x = eq(Some(2), None());
    let y = eq(Some(1), Some(1));
    Pair(x, y)
}
";
        let mut vm = VM::new();
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
        match value {
            Data(ref data) => {
                assert_eq!(&data.fields, [Int(0), Int(1)].as_slice());
            }
            _ => panic!()
        }
    }
    #[test]
    fn call_generic_constrained_multi_parameters_function() {
        let text = 
r"
trait Eq a {
    eq : (a, a) -> Bool;
}
data Option a = Some(a) | None()

impl Eq for Int {
    eq : (Int, Int) -> Bool;
    eq = \l r -> {
        l == r
    }
}
impl Eq for Float {
    eq : (Float, Float) -> Bool;
    eq = \l r -> {
        l == r
    }
}
impl <Eq a> Eq for Option a {
    eq : (Option a, Option a) -> Bool;
    eq = \l r -> {
        match l {
            Some(l_val) => {
                match r {
                    Some(r_val) => { eq(l_val, r_val) }
                    None() => { false }
                }
            }
            None() => {
                match r {
                    Some(_) => { false }
                    None() => { true }
                }
            }
        }
    }
}
test : <Eq a, Eq b> (Option a, b, b) -> Bool;
test = \opt x y -> {
    if eq(x, y) {
        eq(opt, None())
    }
    else {
        false
    }
}
data Pair = Pair {
    x: Bool,
    y: Bool
}
main : () -> Pair;
main = \ -> {
    let a = None();
    eq(a, Some(1));
    let x = test(a, 1.0, 1.0);
    let y = test(Some(2), 1.0, 1.0);
    Pair(x, y)
}
";
        let mut vm = VM::new();
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
        match value {
            Data(ref data) => {
                assert_eq!(&data.fields, [Int(1), Int(0)].as_slice());
            }
            _ => panic!()
        }
    }

    #[test]
    fn strings() {
        let text = 
r#"
main : () -> String;
main = \ -> {
    string_append("Hello", " World")
}"#;
        let mut vm = VM::new();
        let hello_world = vm.intern("Hello World");
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
        assert_eq!(value, String(hello_world));
    }
    #[test]
    fn call_trait_from_another_script() {
        let mut vm = VM::new();
        {
            let text = 
r"
trait Eq a {
    eq : (a, a) -> Bool;
}
impl Eq for Int {
    eq : (Int, Int) -> Bool;
    eq = \l r -> {
        l == r
    }
}
impl Eq for Float {
    eq : (Float, Float) -> Bool;
    eq = \l r -> {
        l == r
    }
}
";
            let mut buffer = BufReader::new(text.as_bytes());
            load_script(&mut vm, &mut buffer)
                .unwrap_or_else(|e| panic!("{}", e));
        }
        {
            let text = 
r"
test : <Eq a> (a, a) -> Bool;
test = \x y -> {
    eq(x, y)
}
main : () -> Bool;
main = \ -> {
    if eq(1.0, 1.0) {
        test(13, 13)
    }
    else {
        false
    }
}
";
            let mut buffer = BufReader::new(text.as_bytes());
            load_script(&mut vm, &mut buffer)
                .unwrap_or_else(|e| panic!("{}", e));
        }
        let value = run_function(&vm, "main")
            .unwrap_or_else(|err| panic!("{}", err));
        assert_eq!(value, Int(1));
    }

    #[test]
    fn use_type_from_another_script() {
        let mut vm = VM::new();
        {
            let text = 
r"
data IntOrFloat = I(Int) | F(Float)

";
            let mut buffer = BufReader::new(text.as_bytes());
            load_script(&mut vm, &mut buffer)
                .unwrap_or_else(|e| panic!("{}", e));
        }
        {
            let text = 
r"
main : () -> Int;
main = \ -> {
    match F(2.0) {
        I(x) => { x }
        F(x) => { 1 }
    }
}
";
            let mut buffer = BufReader::new(text.as_bytes());
            load_script(&mut vm, &mut buffer)
                .unwrap_or_else(|e| panic!("{}", e));
        }
        let value = run_function(&vm, "main")
            .unwrap_or_else(|err| panic!("{}", err));
        assert_eq!(value, Int(1));
    }

    #[test]
    fn and_operator() {
        let text = 
r#"
main : () -> Int;
main = \ -> {
    let x = 0;
    if false && { x = 100; true } {
    }
    else if 0 < x || false {
        x = 200;
    }
    x
}"#;
        let mut vm = VM::new();
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
        assert_eq!(value, Int(0));
    }
    #[test]
    fn recursive_mixed_calls() {
        let s =
r"
test : () -> Int;
test = \ -> {
    rust_fn(10)
}
mul : (Int, Int) -> Int;
mul = \x y -> {
    x * y
}
";
    
        fn rust_fn<'a, 'b, 'c>(vm: &VM<'a>) {
            match vm.pop() {
                Int(i) => {
                    vm.push(Int(i));
                    vm.push(Int(15));
                    let (_, function) = vm.get_global("mul")
                            .expect("Expected 'mul' function");
                    let result = vm.call_function(2, None, function)
                        .unwrap();
                    vm.push(result);
                }
                _ => panic!()
            }
        }
        let mut vm = VM::new();
        vm.extern_function("rust_fn", vec![INT_TYPE.clone()], INT_TYPE.clone(), box rust_fn)
            .unwrap_or_else(|e| panic!("{}", e));
        let mut buffer = BufReader::new(s.as_bytes());
        load_script(&mut vm, &mut buffer)
            .unwrap_or_else(|e| panic!("{}", e));
        let value = run_function(&vm, "test")
            .unwrap_or_else(|err| panic!("{}", err));
        assert_eq!(value, Int(150));
    }

    #[test]
    fn interned_strings_are_not_collected() {
        let mut vm = VM::new();
        {
            let text = 
r"
data IntOrFloat = I(Int) | F(Float)

";
            let mut buffer = BufReader::new(text.as_bytes());
            load_script(&mut vm, &mut buffer)
                .unwrap_or_else(|e| panic!("{}", e));
        }
        vm.collect();
        {
            let text = 
r"
main : () -> Int;
main = \ -> {
    match F(2.0) {
        I(x) => { x }
        F(x) => { 1 }
    }
}
";
            let mut buffer = BufReader::new(text.as_bytes());
            load_script(&mut vm, &mut buffer)
                .unwrap_or_else(|e| panic!("{}", e));
        }
        let value = run_function(&vm, "main")
            .unwrap_or_else(|err| panic!("{}", err));
        assert_eq!(value, Int(1));
    }

    #[test]
    fn field_access() {
        let text = 
r#"
data Test = Test { x: Int, y: Float }

main : () -> Int;
main = \ -> {
    let x = Test(123, 0.0);
    x.x
}"#;
        let mut vm = VM::new();
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
        assert_eq!(value, Int(123));
    }
    #[test]
    fn global_access() {
        let text = 
r#"

global : Int;
global = { 123 }

main : () -> Int;
main = \ -> { global }
"#;
        let mut vm = VM::new();
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| panic!("{}", err));
        assert_eq!(value, Int(123));
    }
}

