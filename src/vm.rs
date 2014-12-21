use std::rc::Rc;
use std::cell::{RefCell, RefMut, Ref};
use std::fmt;
use std::intrinsics::{TypeId, get_tydesc};
use std::any::Any;
use std::collections::HashMap;
use ast;
use parser::Parser;
use typecheck::{Typecheck, TypeEnv, TypeInfo, TypeInfos, Typed, STRING_TYPE, INT_TYPE, UNIT_TYPE, TcIdent, TcType, Constrained, match_types};
use ast::TypeEnum::*;
use compiler::*;
use compiler::Instruction::*;
use interner::{Interner, InternedStr};
use gc::{Gc, GcPtr, Traverseable, DataDef};
use fixed::*;

use self::Named::*;
use self::Global_::*;

pub use vm::Value::{
    Int,
    Float,
    String,
    Data,
    Function,
    Closure,
    TraitObject,
    Userdata};

pub struct Userdata_<T> {
    pub data: Rc<RefCell<T>>
}
impl <T> Userdata_<T> {
    pub fn new(v: T) -> Userdata_<T> {
        Userdata_ { data: Rc::new(RefCell::new(v)) }
    }
    fn ptr(&self) -> *const () {
        (&*self.data as *const RefCell<T>) as *const ()
    }
}
impl <T> PartialEq for Userdata_<T> {
    fn eq(&self, o: &Userdata_<T>) -> bool {
        self.ptr() == o.ptr()
    }
}
impl <T> Clone for Userdata_<T> {
    fn clone(&self) -> Userdata_<T> {
        Userdata_ { data: self.data.clone() }
    }
}

pub struct DataStruct<'a> {
    value: GcPtr<Data_<'a>>
}

impl <'a> DataStruct<'a> {

    fn borrow(&self) -> &Data_<'a> {
        & **self
    }
    fn borrow_mut(&self) -> &mut Data_<'a> {
        unsafe { ::std::mem::transmute(& **self) }
    }
}

impl <'a> PartialEq for DataStruct<'a> {
    fn eq(&self, other: &DataStruct<'a>) -> bool {
        self.tag == other.tag && self.fields == other.fields
    }
}

impl <'a> Clone for DataStruct<'a> {
    fn clone(&self) -> DataStruct<'a> {
        DataStruct { value: self.value }
    }
}

impl <'a> Deref<Data_<'a>> for DataStruct<'a> {
    fn deref(&self) -> &Data_<'a> {
        &*self.value
    }
}
impl <'a> DerefMut<Data_<'a>> for DataStruct<'a> {
    fn deref_mut(&mut self) -> &mut Data_<'a> {
        &mut *self.value
    }
}

pub struct Data_<'a> {
    tag: uint,
    fields: [Value<'a>]
}

#[deriving(Clone, PartialEq)]
pub enum Value<'a> {
    Int(int),
    Float(f64),
    String(InternedStr),
    Data(DataStruct<'a>),
    Function(uint),
    Closure(DataStruct<'a>),
    TraitObject(DataStruct<'a>),
    Userdata(Userdata_<Box<Any + 'static>>)
}

impl <'a> Traverseable for Data_<'a> {
    fn traverse(&mut self, gc: &mut Gc) {
        self.fields.traverse(gc);
    }
}

impl <'a> Traverseable for Value<'a> {
    fn traverse(&mut self, gc: &mut Gc) {
        let mut ptr = match *self {
            Data(ref mut data) => data.value,
            Closure(ref mut data) => data.value,
            TraitObject(ref mut data) => data.value,
            _ => return
        };
        ptr.traverse(gc);
    }
}

type Dict = Vec<uint>;

impl <'a> fmt::Show for Value<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Int(i) => write!(f, "{}", i),
            Float(x) => write!(f, "{}f", x),
            String(x) => write!(f, "\"{}\"", x),
            Data(ref data) => {
                let d = data.borrow();
                write!(f, "{{{} {}}}", d.tag, &d.fields)
            }
            Function(i) => write!(f, "<function {}>", i),
            Closure(ref closure) => write!(f, "<Closure {} {}>", closure.tag, &closure.fields),
            TraitObject(ref object) => write!(f, "<{} {}>", object.tag, &object.fields),
            Userdata(ref ptr) => write!(f, "<Userdata {}>", &*ptr.data.borrow() as *const Box<Any>)
        }
    }
}

pub type ExternFunction<'a> = for<'b, 'c> fn(&VM<'a>);

#[deriving(Show)]
pub struct Global<'a> {
    id: InternedStr,
    typ: Constrained<TcType>,
    value: Global_<'a>
}
enum Global_<'a> {
    Bytecode(Vec<Instruction>),
    Extern(ExternFunction<'a>)
}
impl <'a> Typed for Global<'a> {
    fn type_of(&self) -> &TcType {
        &self.typ.value
    }
}
impl <'a> fmt::Show for Global_<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self { 
            Bytecode(ref is) => write!(f, "Bytecode {}", is),
            Extern(_) => write!(f, "<extern>")
        }
    }
}

enum Named {
    GlobalFn(uint),
    TraitFn(InternedStr, uint),
}

pub struct VM<'a> {
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
                debug!("#### {} {}", id, self.type_infos.enums);
                self.type_infos.structs.get(id)
                    .map(|&(_, ref fields)| Variable::Constructor(0, fields.len()))
                    .or_else(|| {
                        self.type_infos.enums.values()
                            .flat_map(|ctors| ctors.iter().enumerate())
                            .find(|ctor| ctor.1.name.id() == id)
                            .map(|(i, ctor)| Variable::Constructor(i, ctor.arguments.len()))
                    })
            }
        }
    }
    fn find_field(&self, struct_: &InternedStr, field: &InternedStr) -> Option<uint> {
        (*self).find_field(struct_, field)
    }

    fn find_tag(&self, enum_: &InternedStr, ctor_name: &InternedStr) -> Option<uint> {
        match self.type_infos.enums.get(enum_) {
            Some(ctors) => {
                ctors.iter()
                    .enumerate()
                    .find(|&(_, c)| c.name.id() == ctor_name)
                    .map(|(i, _)| i)
            }
            None => None
        }
    }
    fn find_trait_offset(&self, trait_name: &InternedStr, trait_type: &TcType) -> Option<uint> {
        self.trait_indexes
            .find(|func| func.trait_name == *trait_name && match_types(&func.impl_type, trait_type))
            .map(|(_, func)| func.index)
    }
    fn find_trait_function(&self, typ: &TcType, fn_name: &InternedStr) -> Option<TypeResult<uint>> {
        self.names.get(fn_name).and_then(|named| {
            match *named {
                TraitFn(ref trait_name, _) => {
                    match (self.find_object_function(trait_name, fn_name), self.find_trait_offset(trait_name, typ)) {
                        (Some(function_offset), Some(trait_offset)) => {
                            debug!("{} {} {}", function_offset, trait_offset, self.globals.borrow().len());
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
    fn find_object_function(&self, trait_name: &InternedStr, fn_name: &InternedStr) -> Option<uint> {
        self.type_infos.traits
            .get(trait_name)
            .and_then(|trait_info| 
                trait_info.iter()
                    .enumerate()
                    .find(|&(_, tup)| tup.0 == *fn_name)
                    .map(|(i, _)| i)
            )
    }
    fn next_function_index(&self) -> uint {
        self.globals.borrow().len()
    }
}

impl <'a, 'b> TypeEnv for VMEnv<'a, 'b> {
    fn find_type(&self, id: &InternedStr) -> Option<(&[ast::Constraints], &TcType)> {
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
                self.type_infos.structs.get(id)
                    .map(|type_fields| ([].as_slice(), &type_fields.0))
                    .or_else(|| {
                        self.type_infos.enums.values()
                            .flat_map(|ctors| ctors.iter())
                            .find(|ctor| ctor.name.id() == id)
                            .map(|ctor| ([].as_slice(), &ctor.name.typ))
                    })
            }
        }
    }
    fn find_type_info(&self, id: &InternedStr) -> Option<TypeInfo> {
        self.type_infos.find_type_info(id)
    }
}

pub struct Stack<'a> {
    values: Vec<Value<'a>>,
    frames: Vec<(uint, Option<GcPtr<Data_<'a>>>)>
}

impl <'a, 'b, 'c> Stack<'a> {

    fn new() -> Stack<'a> {
        Stack { values: Vec::new(), frames: Vec::new() }
    }

    pub fn get(&self, index: uint) -> Value<'a> {
        self.values[index].clone()
    }

    pub fn pop(&mut self) -> Value<'a> {
        self.values
            .pop()
            .expect("pop on empty stack")
    }

    pub fn set(&mut self, index: uint, v: Value<'a>) {
        self.values[index] = v;
    }

    pub fn push(&mut self, v: Value<'a>) {
        self.values.push(v)
    }

    pub fn len(&self) -> uint {
        self.values.len()
    }

}

pub struct StackFrame<'a: 'b, 'b> {
    stack: RefMut<'b, Stack<'a>>,
    offset: uint,
    upvars: Option<GcPtr<Data_<'a>>>
}
impl <'a: 'b, 'b> StackFrame<'a, 'b> {
    pub fn new(v: RefMut<'b, Stack<'a>>, args: uint, upvars: Option<GcPtr<Data_<'a>>>) -> StackFrame<'a, 'b> {
        let offset = v.len() - args;
        StackFrame { stack: v, offset: offset, upvars: upvars }
    }

    pub fn new_empty(vm: &'b VM<'a>) -> StackFrame<'a, 'b> {
        let stack = vm.stack.borrow_mut();
        let offset = stack.len();
        StackFrame { stack: stack, offset: offset, upvars: None }
    }

    pub fn len(&self) -> uint {
        self.stack.len() - self.offset
    }

    pub fn get(&self, i: uint) -> &Value<'a> {
        &self.stack.values[self.offset + i]
    }

    pub fn get_mut(&mut self, i: uint) -> &mut Value<'a> {
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

    fn get_upvar(&self, index: uint) -> &Value<'a> {
        let upvars = self.upvars.as_ref().expect("Attempted to access upvar in non closure function");
        &upvars.fields[index]
    }

    fn as_slice(&self) -> &[Value<'a>] {
        self.stack.values.slice_from(self.offset)
    }

    fn as_mut_slice(&mut self) -> &mut [Value<'a>] {
        self.stack.values.slice_from_mut(self.offset)
    }

    fn new_scope<E, F>(stack: RefMut<'b, Stack<'a>>
            , args: uint
            , upvars: Option<GcPtr<Data_<'a>>>
            , f: F) -> Result<StackFrame<'a, 'b>, E> 
        where F: FnOnce(StackFrame<'a, 'b>) -> Result<StackFrame<'a, 'b>, E> {
        let stack = StackFrame::frame(stack, args, upvars);
        let mut stack = try!(f(stack));
        stack.stack.frames.pop();
        Ok(stack)
    }
    fn scope<E, F>(self
            , args: uint
            , new_upvars: Option<GcPtr<Data_<'a>>>
            , f: F) -> Result<StackFrame<'a, 'b>, E>
        where F: FnOnce(StackFrame<'a, 'b>) -> Result<StackFrame<'a, 'b>, E> {
        let StackFrame { stack: s, offset, upvars } = self;
        let new_stack = StackFrame::frame(s, args, new_upvars);
        let mut new_stack = try!(f(new_stack));
        new_stack.stack.frames.pop();
        Ok(StackFrame { stack: new_stack.stack, offset: offset, upvars: upvars })
    }

    fn frame(mut stack: RefMut<'b, Stack<'a>>, args: uint, upvars: Option<GcPtr<Data_<'a>>>) -> StackFrame<'a, 'b> {
        assert!(stack.len() >= args);
        let offset = stack.len() - args;
        stack.frames.push((offset, upvars));
        StackFrame { stack: stack, offset: offset, upvars: upvars }
    }
}

impl <'a, 'b, 'c> Index<uint, Value<'a>> for StackFrame<'a, 'b> {
    fn index(&self, index: &uint) -> &Value<'a> {
        &self.stack.values[self.offset + *index]
    }
}

struct Def<'a:'b, 'b> {
    tag: uint,
    elems: &'b mut [Value<'a>]
}
impl <'a, 'b> DataDef<Data_<'a>> for Def<'a, 'b> {
    fn size(&self) -> uint {
        use std::mem::size_of;
        size_of::<uint>() + size_of::<Value<'a>>() * self.elems.len()
    }
    fn initialize(&self, result: *mut Data_<'a>) {
        let result = unsafe { &mut *result };
        result.tag = self.tag;
        for (field, value) in result.fields.iter_mut().zip(self.elems.iter()) {
            unsafe {
                ::std::ptr::write(field, value.clone());
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
    fn traverse(&mut self, gc: &mut Gc) {
        self.elems.traverse(gc);
    }
}

struct Roots<'a: 'b, 'b> {
    stack: &'b mut [Value<'a>],
    interner: &'b mut Interner
}
impl <'a, 'b> Traverseable for Roots<'a, 'b> {
    fn traverse(&mut self, gc: &mut Gc) {
        self.stack.traverse(gc);
        //Also need to check the interned string table
        self.interner.traverse(gc);
    }
}

impl <'a> VM<'a> {
    
    pub fn new() -> VM<'a> {
        let vm = VM {
            globals: FixedVec::new(),
            trait_indexes: FixedVec::new(),
            type_infos: RefCell::new(TypeInfos::new()),
            typeids: FixedMap::new(),
            interner: RefCell::new(Interner::new()),
            names: RefCell::new(HashMap::new()),
            gc: RefCell::new(Gc::new()),
            stack: RefCell::new(Stack::new())
        };
        let a = Generic(0);
        let array_a = ArrayType(box a.clone());
        let _ = vm.extern_function("array_length", vec![array_a.clone()], INT_TYPE.clone(), array_length);
        let _ = vm.extern_function("string_append", vec![STRING_TYPE.clone(), STRING_TYPE.clone()], STRING_TYPE.clone(), string_append);
        vm
    }

    pub fn push(&self, v: Value<'a>) {
        self.stack.borrow_mut().push(v)
    }

    pub fn pop(&self) -> Value<'a> {
        self.stack.borrow_mut()
            .pop()
    }

    pub fn new_functions(&self, (fns, indexes): (Vec<CompiledFunction>, Vec<TraitFunctions>)) {
        let mut names = self.names.borrow_mut();
        for trait_index in indexes.into_iter() {
            //First index of this impl's functions
            let start_index = trait_index.index - self.globals.len();
            let func = &fns[start_index];
            let is_registered = match names.get(&func.id) {
                Some(&TraitFn(..)) => true,
                None => false,
                _ => panic!()
            };
            if !is_registered {
                match self.type_infos.borrow().traits.get(&trait_index.trait_name) {
                    Some(trait_fns) => {
                        for (i, &(trait_fn, _)) in trait_fns.iter().enumerate() {
                            debug!("Register trait fn {}", trait_fn);
                            names.insert(func.id, TraitFn(trait_index.trait_name, i));
                        }
                    }
                    None => panic!()
                }
            }
            self.trait_indexes.push(trait_index);
        }
        for f in fns.into_iter() {
            let CompiledFunction { id, typ, instructions } = f;
            match names.get(&id) {
                Some(&GlobalFn(..)) => {
                    if id != self.intern("") {//Lambdas have the empty string as name
                        panic!("ICE: Global {} already exists", id);
                    }
                }
                Some(&TraitFn(..)) => (),
                None => {
                    debug!("Register fn {}", id);
                    names.insert(id, GlobalFn(self.globals.len()));
                }
            }
            self.globals.push(Global { id: id, typ: typ, value: Bytecode(instructions) });
        }
    }

    pub fn get_global(&self, name: &str) -> Option<(uint, &Global<'a>)> {
        let n = self.intern(name);
        self.globals.find(|g| n == g.id)
    }

    pub fn get_type<T: 'static>(&self) -> &TcType {
        let id = TypeId::of::<T>();
        self.typeids.get(&id)
            .unwrap_or_else(|| {
                let desc = unsafe { get_tydesc::<T>() };
                let name = if desc.is_not_null() {
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
        frame.map(|mut frame| frame.pop())
    }

    pub fn extern_function(&self, name: &str, args: Vec<TcType>, return_type: TcType, f: ExternFunction<'a>) -> Result<(), ::std::string::String> {
        let id = self.intern(name);
        if self.names.borrow().contains_key(&id) {
            return Err(format!("{} is already defined", name))
        }
        let global = Global {
            id: id,
            typ: Constrained { constraints: Vec::new(), value: FunctionType(args, box return_type) },
            value: Extern(f)
        };
        self.names.borrow_mut().insert(id, GlobalFn(self.globals.len()));
        self.globals.push(global);
        Ok(())
    }

    pub fn register_type<T: 'static>(&mut self, name: &str) -> Result<&TcType, ()> {
        let n = self.intern(name);
        let mut type_infos = self.type_infos.borrow_mut();
        if type_infos.structs.contains_key(&n) {
            Err(())
        }
        else {
            let id = TypeId::of::<T>();
            let typ = Type(n, Vec::new());
            try!(self.typeids.try_insert(id, typ.clone()).map_err(|_| ()));
            let t = self.typeids.get(&id).unwrap();
            type_infos.structs.insert(n, (typ, Vec::new()));
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
            names: self.names.borrow()
        }
    }

    pub fn collect(&self) {
        let mut interner = self.interner.borrow_mut();
        let mut stack = self.stack.borrow_mut();
        let mut roots = Roots { stack: &mut *stack.values, interner: &mut *interner };
        self.gc.borrow_mut().collect(&mut roots);
    }

    fn new_data(&self, tag: uint, fields: &mut [Value<'a>]) -> Value<'a> {
        Data(DataStruct { value: self.gc.borrow_mut().alloc(Def { tag: tag, elems: fields })})
    }
    fn new_data_and_collect(&self, stack: &mut [Value<'a>], tag: uint, fields: &mut [Value<'a>]) -> DataStruct<'a> {
        let mut interner = self.interner.borrow_mut();
        let mut roots = Roots { stack: stack, interner: &mut *interner };
        let mut gc = self.gc.borrow_mut();
        DataStruct { value: gc.alloc_and_collect(&mut roots, Def { tag: tag, elems: fields }) }
    }

    pub fn call_function<'b, 'c>(&self, args: uint, upvars: Option<GcPtr<Data_<'a>>>, function: &Global<'a>) -> VMResult<Value<'a>>  {
        let stack = StackFrame::new(self.stack.borrow_mut(), args, upvars);
        self.execute_function(stack, function)
            .map(|mut stack| stack.pop())
    }
    fn execute_function<'b, 'c>(&'b self, stack: StackFrame<'a, 'b>, function: &Global<'a>) -> Result<StackFrame<'a, 'b>, ::std::string::String> {
        match function.value {
            Extern(func) => {
                //Make sure that the stack is not borrowed during the external function call
                //Necessary since we do not know what will happen during the function call
                let StackFrame { stack, offset, upvars } = stack;
                drop(stack);
                func(self);
                Ok(StackFrame::new(self.stack.borrow_mut(), offset, upvars))
            }
            Bytecode(ref instructions) => {
                self.execute(stack, instructions.as_slice())
            }
        }
    }

    pub fn execute<'b>(&'b self, mut stack: StackFrame<'a, 'b>, instructions: &[Instruction]) -> Result<StackFrame<'a, 'b>, ::std::string::String> {
        debug!("Enter frame with {}", stack.as_slice());
        let mut index = 0;
        while index < instructions.len() {
            let instr = instructions[index];
            debug!("{}: {}", index, instr);
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
                    stack.push(Function(i));
                }
                PushFloat(f) => stack.push(Float(f)),
                Store(i) => {
                    *stack.get_mut(i) = stack.pop();
                }
                CallGlobal(args) => {
                    let function_index = stack.len() - 1 - args;
                    {
                        let f = stack.get(function_index).clone();
                        let (function, new_upvars) = match f {
                            Function(index) => {
                                (&self.globals[index], None)
                            }
                            Closure(ref closure) => {
                                (&self.globals[closure.tag], Some(closure.value))
                            }
                            x => return Err(format!("Cannot call {}", x))
                        };
                        debug!("Call {} :: {}", function.id, function.typ);
                        stack = try!(stack.scope(args, new_upvars, |new_stack| {
                            self.execute_function(new_stack, function)
                        }));
                    }
                    if stack.len() > function_index + args {
                        //Value was returned
                        let result = stack.pop();
                        debug!("Return {}", result);
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
                    let d = self.new_data(tag, stack.as_mut_slice().slice_from_mut(arg_start));
                    for _ in range(0, args) {
                        stack.pop();
                    } 
                    stack.push(d);
                }
                GetField(i) => {
                    match stack.pop() {
                        Data(data) => {
                            let v = data.borrow().fields[i].clone();
                            stack.push(v);
                        }
                        x => return Err(format!("GetField on {}", x))
                    }
                }
                SetField(i) => {
                    let value = stack.pop();
                    let data = stack.pop();
                    match data {
                        Data(data) => {
                            data.borrow_mut().fields[i] = value;
                        }
                        _ => return Err("Op SetField called on non data type".to_string())
                    }
                }
                TestTag(tag) => {
                    let x = match *stack.top() {
                        Data(ref data) => if data.borrow().tag == tag { 1 } else { 0 },
                        _ => return Err("Op TestTag called on non data type".to_string())
                    };
                    stack.push(Int(x));
                }
                Split => {
                    match stack.pop() {
                        Data(data) => {
                            for field in data.fields.iter() {
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
                            let v = array.borrow_mut().fields[index as uint].clone();
                            stack.push(v);
                        }
                        (x, y) => return Err(format!("Op GetIndex called on invalid types {} {}", x, y))
                    }
                }
                SetIndex => {
                    let value = stack.pop();
                    let index = stack.pop();
                    let array = stack.pop();
                    match (array, index) {
                        (Data(array), Int(index)) => {
                            array.borrow_mut().fields[index as uint] = value;
                        }
                        (x, y) => return Err(format!("Op SetIndex called on invalid types {} {}", x, y))
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
                    stack.upvars.expect("Upvar").fields[i] = v;
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
                        TraitObject(ref obj) => stack.push(obj.fields[0].clone()),
                        _ => return Err(format!("Op Unpack called on object other than a TraitObject"))
                    }
                }
                PushDictionaryMember(trait_index, function_offset) => {
                    let func = match stack.get_upvar(0).clone()  {
                        Data(dict) => {
                            match dict.borrow().fields[trait_index] {
                                Function(i) => Function(i + function_offset),
                                _ => panic!()
                            }
                        }
                        ref x => panic!("PushDictionaryMember {}", x)
                    };
                    stack.push(func);
                }
                PushDictionary(index) => {
                    let dict = stack.get_upvar(0).clone();
                    let dict = match dict {
                        Data(data) => data.borrow().fields[index].clone(),
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
            debug!("--> {}", stack.top());
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
    where F: FnOnce(int, int) -> int {
    binop(stack, move |l, r| {
        match (l, r) {
            (Int(l), Int(r)) => Int(f(l, r)),
            (l, r) => panic!("{} `intOp` {}", l, r)
        }
    })
}
#[inline]
fn binop_float<F>(stack: &mut StackFrame, f: F)
    where F: FnOnce(f64, f64) -> f64 {
    binop(stack, move |l, r| {
        match (l, r) {
            (Float(l), Float(r)) => Float(f(l, r)),
            (l, r) => panic!("{} `floatOp` {}", l, r)
        }
    })
}

fn array_length(vm: &VM) {
    match vm.pop() {
        Data(values) => {
            let i = values.borrow().fields.len();
            vm.push(Int(i as int));
        }
        x => panic!("{}", x)
    }
}
fn string_append(vm: &VM) {
    let mut stack = StackFrame::new(vm.stack.borrow_mut(), 2, None);
    match (&stack[0], &stack[1]) {
        (&String(ref l), &String(ref r)) => {
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
    ($e:expr) => (try!(($e).map_err(|e| format!("{}", e))))
)

pub fn parse_expr(buffer: &mut Buffer, vm: &VM) -> Result<::ast::LExpr<TcIdent>, ::std::string::String> {
    let mut interner = vm.interner.borrow_mut();
        let mut gc = vm.gc.borrow_mut();
    let mut parser = Parser::new(&mut *interner, &mut *gc, buffer, |s| TcIdent { name: s, typ: UNIT_TYPE.clone() });
    parser.expression().map_err(|err| format!("{}", err))
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
        let mut tc = Typecheck::new();
        let env = vm.env();
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
    use std::io::BufReader;
    let mut buffer = BufReader::new(s.as_bytes());
    run_buffer_main(vm, &mut buffer)
}
pub fn run_buffer_main<'a>(vm: &VM<'a>, buffer: &mut Buffer) -> VMResult<Value<'a>> {
    try!(load_script(vm, buffer));
    let v = try!(run_function(vm, "main"));
    Ok(v)
}

pub fn run_function<'a: 'b, 'b>(vm: &'b VM<'a>, name: &str) -> VMResult<Value<'a>> {
    let globals = vm.globals.borrow();
    let func = match globals.iter().find(|g| g.id.as_slice() == name) {
        Some(f) => &**f,
        None => return Err(format!("Undefined function {}", name))
    };
    vm.run_function(func)
}

#[cfg(test)]
mod tests {
    use super::{VM, Data, Int, String, run_main, run_function, load_script};
    use ast::INT_TYPE;
    use std::io::BufReader;
    ///Test that the stack is adjusted correctly after executing expressions as statements
    #[test]
    fn stack_for_block() {
        let text =
r"
fn main() -> int {
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
fn main() -> int {
    match A(8) {
        A(x) => { x }
        B(y) => { 0 }
    }
}
enum AB {
    A(int),
    B(float)
}
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
fn main() -> Vec {
    let x = Vec(1, 2);
    x = add(x, Vec(10, 0));
    x.y = add(x.y, 3);
    x
}
struct Vec {
    x: int,
    y: int
}

trait Add {
    fn add(l: Self, r: Self) -> Self;
}

impl Add for Vec {
    fn add(l: Vec, r: Vec) -> Vec {
        Vec(l.x + r.x, l.y + r.y)
    }
}
impl Add for int {
    fn add(l: int, r: int) -> int {
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
fn main() -> int {
    test(lazy)
}
fn lazy() -> int {
    42
}

fn test(f: fn () -> int) -> int {
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
fn main() -> [int] {
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
fn main() -> int {
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
fn main() -> int {
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

trait Collection {
    fn len(x: Self) -> int;
}
impl Collection for [int] {
    fn len(x: [int]) -> int {
        array_length(x)
    }
}

fn test(c: Collection) -> int {
    len(c)
}

fn main() -> int {
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
fn main() -> int {
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
trait Eq {
    fn eq(l: Self, r: Self) -> bool;
}
enum Option<T> {
    Some(T),
    None()
}
impl Eq for int {
    fn eq(l: int, r: int) -> bool {
        l == r
    }
}
impl <T:Eq> Eq for Option<T> {
    fn eq(l: Option<T>, r: Option<T>) -> bool {
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
struct Pair {
    x: bool,
    y: bool
}
fn main() -> Pair {
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
trait Eq {
    fn eq(l: Self, r: Self) -> bool;
}
enum Option<T> {
    Some(T),
    None()
}
impl Eq for int {
    fn eq(l: int, r: int) -> bool {
        l == r
    }
}
impl Eq for float {
    fn eq(l: float, r: float) -> bool {
        l == r
    }
}
impl <T:Eq> Eq for Option<T> {
    fn eq(l: Option<T>, r: Option<T>) -> bool {
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
fn test<T: Eq, U: Eq>(opt: Option<T>, x: U, y: U) -> bool {
    if eq(x, y) {
        eq(opt, None())
    }
    else {
        false
    }
}
struct Pair {
    x: bool,
    y: bool
}
fn main() -> Pair {
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
r#"fn main() -> string {
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
trait Eq {
    fn eq(l: Self, r: Self) -> bool;
}
impl Eq for int {
    fn eq(l: int, r: int) -> bool {
        l == r
    }
}
impl Eq for float {
    fn eq(l: float, r: float) -> bool {
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
fn test<T: Eq>(x: T, y: T) -> bool {
    eq(x, y)
}
fn main() -> bool {
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
enum IntOrFloat {
    I(int),
    F(float)
}
";
            let mut buffer = BufReader::new(text.as_bytes());
            load_script(&mut vm, &mut buffer)
                .unwrap_or_else(|e| panic!("{}", e));
        }
        {
            let text = 
r"
fn main() -> int {
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
fn main() -> int {
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
fn test() -> int {
    rust_fn(10)
}
fn mul(x: int, y: int) -> int {
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
        vm.extern_function("rust_fn", vec![INT_TYPE.clone()], INT_TYPE.clone(), rust_fn)
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
enum IntOrFloat {
    I(int),
    F(float)
}
";
            let mut buffer = BufReader::new(text.as_bytes());
            load_script(&mut vm, &mut buffer)
                .unwrap_or_else(|e| panic!("{}", e));
        }
        vm.collect();
        {
            let text = 
r"
fn main() -> int {
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
}

