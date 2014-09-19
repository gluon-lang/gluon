use std::rc::Rc;
use std::cell::{RefCell, Ref};
use std::fmt;
use std::intrinsics::{TypeId, get_tydesc};
use std::any::Any;
use std::collections::HashMap;
use parser::Parser;
use typecheck::{Typecheck, TypeEnv, TypeInfo, TypeInfos, Typed, string_type_tc, int_type_tc, unit_type_tc, TcIdent, TcType, Type, FunctionType, Constrained, Generic, ArrayType, match_types};
use compiler::*;
use interner::{Interner, InternedStr};
use gc::{Gc, GcPtr, Traverseable};
use fixed::*;

pub struct Userdata<T> {
    pub data: Rc<RefCell<T>>
}
impl <T> Userdata<T> {
    pub fn new(v: T) -> Userdata<T> {
        Userdata { data: Rc::new(RefCell::new(v)) }
    }
    fn ptr(&self) -> *const () {
        (&*self.data as *const RefCell<T>) as *const ()
    }
}
impl <T> PartialEq for Userdata<T> {
    fn eq(&self, o: &Userdata<T>) -> bool {
        self.ptr() == o.ptr()
    }
}
impl <T> Clone for Userdata<T> {
    fn clone(&self) -> Userdata<T> {
        Userdata { data: self.data.clone() }
    }
}

pub struct Data<'a> {
    value: GcPtr<'a, Data_<'a>>
}

impl <'a> Data<'a> {

    fn borrow(&self) -> &Data_<'a> {
        & **self
    }
    fn borrow_mut(&self) -> &mut Data_<'a> {
        unsafe { ::std::mem::transmute(& **self) }
    }
}

impl <'a> PartialEq for Data<'a> {
    fn eq(&self, other: &Data<'a>) -> bool {
        self.tag == other.tag && self.fields == other.fields
    }
}

impl <'a> Clone for Data<'a> {
    fn clone(&self) -> Data<'a> {
        Data { value: self.value }
    }
}

impl <'a> Deref<Data_<'a>> for Data<'a> {
    fn deref(&self) -> &Data_<'a> {
        &*self.value
    }
}
impl <'a> DerefMut<Data_<'a>> for Data<'a> {
    fn deref_mut(&mut self) -> &mut Data_<'a> {
        &mut *self.value
    }
}

#[deriving(Clone, PartialEq)]
pub struct Data_<'a> {
    tag: uint,
    fields: Vec<Value<'a>>
}

#[deriving(Clone, PartialEq)]
pub enum Value<'a> {
    Int(int),
    Float(f64),
    String(InternedStr),
    Data(Data<'a>),
    Function(uint),
    Closure(Data<'a>),
    TraitObject(Data<'a>),
    Userdata(Userdata<Box<Any + 'static>>)
}

impl <'a> Traverseable<Data_<'a>> for Data_<'a> {
    fn traverse(&mut self, func: |&mut Data_<'a>|) {
        self.fields.traverse(func);
    }
}

impl <'a> Traverseable<Data_<'a>> for Vec<Value<'a>> {
    fn traverse(&mut self, func: |&mut Data_<'a>|) {
        for value in self.mut_iter() {
            match *value {
                Data(ref mut data) => func(&mut **data),
                Closure(ref mut data) => func(&mut **data),
                TraitObject(ref mut data) => func(&mut **data),
                _ => ()
            }
        }
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
                write!(f, "{{{} {}}}", d.tag, d.fields)
            }
            Function(i) => write!(f, "<function {}>", i),
            Closure(ref closure) => write!(f, "<Closure {} {}>", closure.tag, closure.fields),
            TraitObject(ref object) => write!(f, "<{} {}>", object.tag, object.fields),
            Userdata(ref ptr) => write!(f, "<Userdata {}>", &*ptr.data.borrow() as *const Box<Any>)
        }
    }
}

pub type ExternFunction = fn (&VM, StackFrame);

#[deriving(Show)]
pub struct Global {
    id: InternedStr,
    typ: Constrained<TcType>,
    value: Global_
}
enum Global_ {
    Bytecode(Vec<Instruction>),
    Extern(ExternFunction)
}
impl Typed for Global {
    fn type_of(&self) -> &TcType {
        &self.typ.value
    }
}
impl fmt::Show for Global_ {
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
    globals: FixedVec<Global>,
    trait_indexes: FixedVec<TraitFunctions>,
    type_infos: RefCell<TypeInfos>,
    typeids: FixedMap<TypeId, TcType>,
    interner: RefCell<Interner>,
    names: RefCell<HashMap<InternedStr, Named>>,
    gc: Gc<Data_<'a>>
}

pub struct VMEnv<'a> {
    type_infos: Ref<'a, TypeInfos>,
    trait_indexes: &'a FixedVec<TraitFunctions>,
    globals: &'a FixedVec<Global>,
    names: Ref<'a, HashMap<InternedStr, Named>>
}

impl <'a> CompilerEnv for VMEnv<'a> {
    fn find_var(&self, id: &InternedStr) -> Option<Variable> {
        self.names.find(id).and_then(|named| {
            match *named {
                GlobalFn(index) if index < self.globals.len() => {
                    let g = &self.globals[index];
                    Some(Global(index, g.typ.constraints.as_slice(), &g.typ.value))
                }
                TraitFn(trait_index, function_index) => {
                    self.type_infos.traits
                        .find(&trait_index)
                        .and_then(|functions| {
                            if function_index < functions.len() {
                                Some(TraitFunction(&functions[function_index].ref1().value))
                            }
                            else {
                                None
                            }
                        })
                }
                _ => None
            }
        })
    }
    fn find_field(&self, struct_: &InternedStr, field: &InternedStr) -> Option<uint> {
        (*self).find_field(struct_, field)
    }

    fn find_tag(&self, enum_: &InternedStr, ctor_name: &InternedStr) -> Option<uint> {
        match self.type_infos.enums.find(enum_) {
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
        self.names.find(fn_name).and_then(|named| {
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
            .find(trait_name)
            .and_then(|trait_info| 
                trait_info.iter()
                    .enumerate()
                    .find(|&(_, tup)| tup.ref0() == fn_name)
                    .map(|(i, _)| i)
            )
    }
    fn next_function_index(&self) -> uint {
        self.globals.borrow().len()
    }
}

impl <'a> TypeEnv for VMEnv<'a> {
    fn find_type(&self, id: &InternedStr) -> Option<&Constrained<TcType>> {
        self.names.find(id).and_then(|named| {
            match *named {
                GlobalFn(index) if index < self.globals.len() => {
                    Some(&self.globals[index].typ)
                }
                TraitFn(trait_index, function_index) => {
                    self.type_infos.traits
                        .find(&trait_index)
                        .and_then(|functions| {
                            if function_index < functions.len() {
                                Some(functions[function_index].ref1())
                            }
                            else {
                                None
                            }
                        })
                }
                _ => None
            }
        })
    }
    fn find_type_info(&self, id: &InternedStr) -> Option<TypeInfo> {
        self.type_infos.find_type_info(id)
    }
}

pub struct StackFrame<'a, 'b: 'a> {
    stack: &'a mut Vec<Value<'b>>,
    offset: uint,
    upvars: &'a mut [Value<'b>]
}
impl <'a, 'b> StackFrame<'a, 'b> {
    pub fn new(v: &'a mut Vec<Value<'b>>, args: uint, upvars: &'a mut [Value<'b>]) -> StackFrame<'a, 'b> {
        let offset = v.len() - args;
        StackFrame { stack: v, offset: offset, upvars: upvars }
    }

    pub fn len(&self) -> uint {
        self.stack.len() - self.offset
    }

    pub fn get<'a>(&'a self, i: uint) -> &'a Value<'b> {
        &(*self.stack)[self.offset + i]
    }
    pub fn get_mut<'a>(&'a mut self, i: uint) -> &'a mut Value<'b> {
        self.stack.get_mut(self.offset + i)
    }

    pub fn push(&mut self, v: Value<'b>) {
        self.stack.push(v);
    }
    pub fn top(&mut self) -> &Value<'b> {
        self.stack.last().unwrap()
    }

    pub fn pop(&mut self) -> Value<'b> {
        match self.stack.pop() {
            Some(x) => x,
            None => fail!()
        }
    }
    fn as_slice(&self) -> &[Value<'b>] {
        self.stack.slice_from(self.offset)
    }
}

impl <'a, 'b> Index<uint, Value<'b>> for StackFrame<'a, 'b> {
    fn index(&self, index: &uint) -> &Value<'b> {
        &(*self.stack)[self.offset + *index]
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
            gc: Gc::new()
        };
        let a = Generic(0);
        let array_a = ArrayType(box a.clone());
        let _ = vm.extern_function("array_length", vec![array_a.clone()], int_type_tc.clone(), array_length);
        let _ = vm.extern_function("array_push", vec![array_a.clone(), a.clone()], unit_type_tc.clone(), array_push);
        let _ = vm.extern_function("string_append", vec![string_type_tc.clone(), string_type_tc.clone()], string_type_tc.clone(), string_append);
        vm
    }

    pub fn new_functions(&self, (fns, indexes): (Vec<CompiledFunction>, Vec<TraitFunctions>)) {
        let mut names = self.names.borrow_mut();
        for trait_index in indexes.move_iter() {
            //First index of this impl's functions
            let start_index = trait_index.index - self.globals.len();
            let func = &fns[start_index];
            let is_registered = match names.find(&func.id) {
                Some(&TraitFn(..)) => true,
                None => false,
                _ => fail!()
            };
            if !is_registered {
                match self.type_infos.borrow().traits.find(&trait_index.trait_name) {
                    Some(trait_fns) => {
                        for (i, &(trait_fn, _)) in trait_fns.iter().enumerate() {
                            debug!("Register trait fn {}", trait_fn);
                            names.insert(func.id, TraitFn(trait_index.trait_name, i));
                        }
                    }
                    None => fail!()
                }
            }
            self.trait_indexes.push(trait_index);
        }
        for f in fns.move_iter() {
            let CompiledFunction { id: id, typ: typ, instructions: instructions } = f;
            match names.find(&id) {
                Some(&GlobalFn(..)) => {
                    if id != self.interner.borrow_mut().intern("") {//Lambdas have the empty string as name
                        fail!("ICE: Global {} already exists", id);
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

    pub fn get_global(&self, name: &str) -> Option<(uint, &Global)> {
        let n = self.intern(name);
        self.globals.find(|g| n == g.id)
    }

    pub fn get_type<T: 'static>(&self) -> &TcType {
        let id = TypeId::of::<T>();
        self.typeids.find(&id)
            .unwrap_or_else(|| {
                let desc = unsafe { get_tydesc::<T>() };
                let name = if desc.is_not_null() {
                    unsafe { &*desc }.name
                }
                else {
                    ""
                };
                fail!("Expected type {} to be inserted before get_type call", name)
            })
    }

    pub fn run_function(&'a self, cf: &Global) -> Option<Value<'a>> {
        let mut stack = Vec::new();
        {
            let frame = StackFrame::new(&mut stack, 0, [].as_mut_slice());
            self.execute_function(frame, cf);
        }
        stack.pop()
    }

    pub fn execute_instructions(&'a self, instructions: &[Instruction]) -> Option<Value<'a>> {
        let mut stack = Vec::new();
        {
            let frame = StackFrame::new(&mut stack, 0, [].as_mut_slice());
            self.execute(frame, instructions);
        }
        stack.pop()
    }

    pub fn extern_function(&self, name: &str, args: Vec<TcType>, return_type: TcType, f: ExternFunction) -> Result<(), String> {
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
            try!(self.typeids.try_insert(id, Type(n, Vec::new())).map_err(|_| ()));
            let t = self.typeids.find(&id).unwrap();
            type_infos.structs.insert(n, Vec::new());
            Ok(t)
        }
    }

    pub fn intern(&self, s: &str) -> InternedStr {
        self.interner.borrow_mut().intern(s)
    }

    pub fn env(&self) -> VMEnv {
        VMEnv {
            type_infos: self.type_infos.borrow(),
            trait_indexes: &self.trait_indexes,
            globals: &self.globals,
            names: self.names.borrow()
        }
    }

    fn new_data(&'a self, tag: uint, fields: Vec<Value<'a>>) -> Value<'a> {
        Data(Data { value: self.gc.alloc(Data_ { tag: tag, fields: fields })})
    }
    fn new_data_and_collect(&'a self, roots: &mut Vec<Value<'a>>, tag: uint, fields: Vec<Value<'a>>) -> Data<'a> {
        Data { value: self.gc.alloc_and_collect(roots, Data_ { tag: tag, fields: fields })}
    }

    fn execute_function<'b>(&'a self, stack: StackFrame<'b, 'a>, function: &Global) {
        match function.value {
            Extern(func) => {
                func(self, stack);
            }
            Bytecode(ref instructions) => {
                self.execute(stack, instructions.as_slice());
            }
        }
    }

    pub fn execute<'b>(&'a self, mut stack: StackFrame<'b, 'a>, instructions: &[Instruction]) {
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
                        let mut f = stack.get(function_index).clone();
                        let (function, upvars) = match f {
                            Function(index) => {
                                (&self.globals[index], [].as_mut_slice())
                            }
                            Closure(ref mut closure) => {
                                (&self.globals[closure.tag], closure.fields.as_mut_slice())
                            }
                            x => fail!("Cannot call {}", x)
                        };
                        debug!("Call {} :: {}", function.id, function.typ);
                        let new_stack = StackFrame::new(stack.stack, args, upvars);
                        self.execute_function(new_stack, function);
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
                    let mut fields = Vec::new();
                    for _ in range(0, args) {
                        fields.push(stack.pop());
                    }
                    fields.reverse();
                    let d = self.new_data(tag, fields);
                    stack.push(d);
                }
                GetField(i) => {
                    match stack.pop() {
                        Data(data) => {
                            let v = data.borrow().fields[i].clone();
                            stack.push(v);
                        }
                        x => fail!("GetField on {}", x)
                    }
                }
                SetField(i) => {
                    let value = stack.pop();
                    let data = stack.pop();
                    match data {
                        Data(data) => {
                            *data.borrow_mut().fields.get_mut(i) = value;
                        }
                        _ => fail!()
                    }
                }
                TestTag(tag) => {
                    let x = match *stack.top() {
                        Data(ref data) => if data.borrow().tag == tag { 1 } else { 0 },
                        _ => fail!()
                    };
                    stack.push(Int(x));
                }
                Split => {
                    match stack.pop() {
                        Data(mut data) => {
                            for field in data.fields.iter() {
                                stack.push(field.clone());
                            }
                        }
                        _ => fail!()
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
                    for i in range(0, n) {
                        stack.pop();
                    }
                }
                Slide(n) => {
                    let v = stack.pop();
                    for i in range(0, n) {
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
                        (x, y) => fail!("{} {}", x, y)
                    }
                }
                SetIndex => {
                    let value = stack.pop();
                    let index = stack.pop();
                    let array = stack.pop();
                    match (array, index) {
                        (Data(array), Int(index)) => {
                            *array.borrow_mut().fields.get_mut(index as uint) = value;
                        }
                        _ => fail!()
                    }
                }
                MakeClosure(fi, n) => {
                    let mut upvars = Vec::with_capacity(n);
                    for _ in range(0, n) {
                        let v = stack.pop();
                        upvars.push(v);
                    }
                    let closure = Closure(self.new_data_and_collect(stack.stack, fi, upvars));
                    stack.push(closure);
                }
                PushUpVar(i) => {
                    let v = stack.upvars[i].clone();
                    stack.push(v);
                }
                StoreUpVar(i) => {
                    let v = stack.pop();
                    stack.upvars[i] = v;
                }
                ConstructTraitObject(i) => {
                    let v = stack.pop();
                    let object = TraitObject(self.new_data_and_collect(stack.stack, i, vec![v]));
                    stack.push(object);
                }
                PushTraitFunction(i) => {
                    let func = match stack.top() {
                        &TraitObject(ref object) => {
                            Function(object.tag + i)
                        }
                        _ => fail!()
                    };
                    stack.push(func);
                }
                Unpack => {
                    match stack.pop() {
                        TraitObject(ref obj) => stack.push(obj.fields[0].clone()),
                        _ => fail!()
                    }
                }
                PushDictionaryMember(trait_index, function_offset) => {
                    let func = match stack.upvars[0].clone()  {
                        Data(dict) => {
                            match dict.borrow().fields[trait_index] {
                                Function(i) => Function(i + function_offset),
                                _ => fail!()
                            }
                        }
                        ref x => fail!("PushDictionaryMember {}", x)
                    };
                    stack.push(func);
                }
                PushDictionary(index) => {
                    let dict = stack.upvars[0].clone();
                    let dict = match dict {
                        Data(data) => data.borrow().fields[index].clone(),
                        _ => fail!()
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
                        _ => fail!()
                    }
                }),
                FloatEQ => binop(&mut stack, |l, r| {
                    match (l, r) {
                        (Float(l), Float(r)) => Int(if l == r { 1 } else { 0 }),
                        _ => fail!()
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
    }
}

#[inline]
fn binop(stack: &mut StackFrame, f: |Value, Value| -> Value) {
    let r = stack.pop();
    let l = stack.pop();
    stack.push(f(l, r));
}
#[inline]
fn binop_int(stack: &mut StackFrame, f: |int, int| -> int) {
    binop(stack, |l, r| {
        match (l, r) {
            (Int(l), Int(r)) => Int(f(l, r)),
            (l, r) => fail!("{} `intOp` {}", l, r)
        }
    })
}
#[inline]
fn binop_float(stack: &mut StackFrame, f: |f64, f64| -> f64) {
    binop(stack, |l, r| {
        match (l, r) {
            (Float(l), Float(r)) => Float(f(l, r)),
            (l, r) => fail!("{} `floatOp` {}", l, r)
        }
    })
}

fn array_length(_: &VM, mut stack: StackFrame) {
    match stack.pop() {
        Data(values) => {
            let i = values.borrow().fields.len();
            stack.push(Int(i as int));
        }
        x => fail!("{}", x)
    }
}
fn array_push(_: &VM, mut stack: StackFrame) {
    let value = stack.pop();
    let data = stack.pop();
    match data {
        Data(values) => {
            values.borrow_mut().fields.push(value);
        }
        _ => fail!()
    }
}
fn string_append(vm: &VM, mut stack: StackFrame) {
    match (&stack[0], &stack[1]) {
        (&String(l), &String(r)) => {
            let l = l.as_slice();
            let r = r.as_slice();
            let mut s = String::with_capacity(l.len() + r.len());
            s = s.append(l).append(r);
            let result = vm.interner.borrow_mut().intern(s.as_slice());
            stack.push(String(result));
        }
        _ => fail!()
    }
}

macro_rules! tryf(
    ($e:expr) => (try!(($e).map_err(|e| format!("{}", e))))
)

pub fn parse_expr(buffer: &mut Buffer, vm: &VM) -> Result<::ast::LExpr<TcIdent>, String> {
    let mut interner = vm.interner.borrow_mut();
    let mut parser = Parser::new(&mut *interner, buffer, |s| TcIdent { name: s, typ: unit_type_tc.clone() });
    parser.expression().map_err(|err| format!("{}", err))
}

pub fn load_script(vm: &VM, buffer: &mut Buffer) -> Result<(), String> {
    use parser::Parser;

    let mut module = {
        let mut cell = vm.interner.borrow_mut();
        let mut parser = Parser::new(&mut*cell, buffer, |s| TcIdent { typ: unit_type_tc.clone(), name: s });
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

pub fn run_main<'a>(vm: &'a VM<'a>, s: &str) -> Result<Option<Value<'a>>, String> {
    use std::io::BufReader;
    let mut buffer = BufReader::new(s.as_bytes());
    run_buffer_main(vm, &mut buffer)
}
pub fn run_buffer_main<'a>(vm: &'a VM<'a>, buffer: &mut Buffer) -> Result<Option<Value<'a>>, String> {
    try!(load_script(vm, buffer));
    let v = try!(run_function(vm, "main"));
    Ok(v)
}

pub fn run_function<'a>(vm: &'a VM<'a>, name: &str) -> Result<Option<Value<'a>>, String> {
    let globals = vm.globals.borrow();
    let func = match globals.iter().find(|g| g.id.as_slice() == name) {
        Some(f) => &**f,
        None => return Err(format!("Undefined function {}", name))
    };
    Ok(vm.run_function(func))
}

#[cfg(test)]
mod tests {
    use super::{VM, Data, Int, String, run_main, run_function, load_script};
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
            .unwrap_or_else(|err| fail!("{}", err));
        assert_eq!(value, Some(Int(8)));
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
            .unwrap_or_else(|err| fail!("{}", err));
        assert_eq!(value, Some(Int(8)));
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
            .unwrap_or_else(|err| fail!("{}", err));
        match value {
            Some(Data(ref data)) => {
                assert_eq!(data.fields, vec![Int(11), Int(5)]);
            }
            _ => fail!()
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
            .unwrap_or_else(|err| fail!("{}", err));
        assert_eq!(value, Some(Int(52)));
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
            .unwrap_or_else(|err| fail!("{}", err));
        match value {
            Some(Data(ref data)) => {
                assert_eq!(data.fields, vec![Int(1), Int(2), Int(33)]);
            }
            _ => fail!()
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
            .unwrap_or_else(|err| fail!("{}", err));
        assert_eq!(value, Some(Int(40)));
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
            .unwrap_or_else(|err| fail!("{}", err));
        assert_eq!(value, Some(Int(123)));
    }
    #[test]
    fn array_map() {
        let text = 
r"
fn map_int_array(xs: [int], f: fn (int) -> int) -> [int] {
    let i = 0;
    let result = [];
    while i < array_length(xs) {
        array_push(result, f(xs[i]));
        i = i + 1;
    }
    result
}
fn main() -> [int] {
    let xs = [1,2,3];
    map_int_array(xs, \x -> x * 2)
}
";
        let mut vm = VM::new();
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| fail!("{}", err));
        match value {
            Some(Data(ref data)) => {
                assert_eq!(data.fields, vec![Int(2), Int(4), Int(6)]);
            }
            _ => fail!()
        }
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
            .unwrap_or_else(|err| fail!("{}", err));
        assert_eq!(value, Some(Int(3)));
    }

    #[test]
    fn upvar_index() {
        let text = 
r"
fn main() -> int {
    let xs = map([1,2,3], \x -> x * 2);
    xs[2]
}
fn map<A, B>(as: [A], f: fn (A) -> B) -> [B] {
    foldl(as, [], \a bs -> { array_push(bs, f(a)); bs })
}

fn foldl<A, B>(as: [A], b: B, f: fn (A, B) -> B) -> B {
    let i = 0;
    while i < array_length(as) {
        b = f(as[i], b);
        i = i + 1;
    }
    b
}

";
        let mut vm = VM::new();
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| fail!("{}", err));
        assert_eq!(value, Some(Int(6)));
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
            .unwrap_or_else(|err| fail!("{}", err));
        match value {
            Some(Data(ref data)) => {
                assert_eq!(data.fields, vec![Int(0), Int(1)]);
            }
            _ => fail!()
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
            .unwrap_or_else(|err| fail!("{}", err));
        match value {
            Some(Data(ref data)) => {
                assert_eq!(data.fields, vec![Int(1), Int(0)]);
            }
            _ => fail!()
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
            .unwrap_or_else(|err| fail!("{}", err));
        assert_eq!(value, Some(String(hello_world)));
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
                .unwrap_or_else(|e| fail!("{}", e));
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
                .unwrap_or_else(|e| fail!("{}", e));
        }
        let value = run_function(&vm, "main")
            .unwrap_or_else(|err| fail!("{}", err));
        assert_eq!(value, Some(Int(1)));
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
    else {
    }
    x
}"#;
        let mut vm = VM::new();
        let value = run_main(&mut vm, text)
            .unwrap_or_else(|err| fail!("{}", err));
        assert_eq!(value, Some(Int(0)));
    }
}

