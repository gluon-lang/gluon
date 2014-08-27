use std::rc::Rc;
use std::cell::RefCell;
use std::fmt;
use std::intrinsics::TypeId;
use std::collections::HashMap;
use std::any::Any;
use parser::Parser;
use typecheck::{Typecheck, TypeEnv, TypeInfo, TypeInfos, Typed, int_type_tc, unit_type_tc, TcIdent, TcType, Type, FunctionType, Constrained, Generic, ArrayType};
use compiler::*;
use interner::{Interner, InternedStr};

pub struct Data<T> {
    pub data: Rc<RefCell<T>>
}
impl <T> Data<T> {
    pub fn new(v: T) -> Data<T> {
        Data { data: Rc::new(RefCell::new(v)) }
    }
    fn ptr(&self) -> *const () {
        (&*self.data as *const RefCell<T>) as *const ()
    }
}
impl <T> PartialEq for Data<T> {
    fn eq(&self, o: &Data<T>) -> bool {
        self.ptr() == o.ptr()
    }
}
impl <T> Clone for Data<T> {
    fn clone(&self) -> Data<T> {
        Data { data: self.data.clone() }
    }
}

#[deriving(Clone, PartialEq)]
pub enum Value {
    Int(int),
    Float(f64),
    Data(uint, Rc<RefCell<Vec<Value>>>),
    Function(uint),
    Closure(uint, Rc<RefCell<Vec<Value>>>),
    TraitObject(uint, Rc<Value>),
    Userdata(Data<Box<Any>>)
}

type Dict = Vec<uint>;

impl fmt::Show for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Int(i) => write!(f, "{}", i),
            Float(x) => write!(f, "{}f", x),
            Data(tag, ref ptr) => write!(f, "{{{} {}}}", tag, ptr.borrow()),
            Function(i) => write!(f, "<function {}>", i),
            Closure(fi, ref upvars) => write!(f, "<Closure {} {}>", fi, upvars.borrow()),
            TraitObject(fns, ref o) => write!(f, "<{} {}>", fns, o),
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

pub struct VM {
    globals: Vec<Global>,
    trait_indexes: Vec<TraitFunctions>,
    type_infos: TypeInfos,
    typeids: HashMap<TypeId, TcType>,
    interner: RefCell<Interner>
}

impl CompilerEnv for VM {
    fn find_var(&self, id: &InternedStr) -> Option<Variable> {
        self.globals.iter()
            .enumerate()
            .find(|&(_, f)| f.id == *id)
            .map(|(i, f)| Global(i, f.typ.constraints.as_slice(), &f.typ.value))
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
        fail!("{} {}", trait_name, trait_type)
    }
    fn find_trait_function(&self, typ: &TcType, id: &InternedStr) -> Option<TypeResult<uint>> {
        self.globals.iter()
            .enumerate()
            .find(|&(_, f)| f.id == *id && f.typ.value == *typ)
            .map(|(i, f)| TypeResult { constraints: f.typ.constraints.as_slice(), typ: &f.typ.value, value: i })
    }
    fn find_object_function(&self, trait_type: &InternedStr, name: &InternedStr) -> Option<uint> {
        fail!()
    }
    fn next_function_index(&self) -> uint {
        self.globals.len()
    }
}

impl TypeEnv for VM {
    fn find_type(&self, id: &InternedStr) -> Option<&Constrained<TcType>> {
        self.globals.iter()
            .find(|f| f.id == *id)
            .map(|f| &f.typ)
    }
    fn find_type_info(&self, id: &InternedStr) -> Option<TypeInfo> {
        self.type_infos.find_type_info(id)
    }
}

pub struct StackFrame<'a, 'b> {
    stack: &'a mut Vec<Value>,
    offset: uint,
    upvars: Option<&'b RefCell<Vec<Value>>>
}
impl <'a, 'b> StackFrame<'a, 'b> {
    pub fn new(v: &'a mut Vec<Value>, args: uint, upvars: Option<&'b RefCell<Vec<Value>>>) -> StackFrame<'a, 'b> {
        let offset = v.len() - args;
        StackFrame { stack: v, offset: offset, upvars: upvars }
    }

    pub fn len(&self) -> uint {
        self.stack.len() - self.offset
    }

    pub fn get<'a>(&'a self, i: uint) -> &'a Value {
        &(*self.stack)[self.offset + i]
    }
    pub fn get_mut<'a>(&'a mut self, i: uint) -> &'a mut Value {
        self.stack.get_mut(self.offset + i)
    }

    pub fn push(&mut self, v: Value) {
        self.stack.push(v);
    }
    pub fn top(&mut self) -> &Value {
        self.stack.last().unwrap()
    }

    pub fn pop(&mut self) -> Value {
        match self.stack.pop() {
            Some(x) => x,
            None => fail!()
        }
    }
    fn as_slice(&self) -> &[Value] {
        self.stack.slice_from(self.offset)
    }
}

impl VM {
    
    pub fn new() -> VM {
        let mut vm = VM {
            globals: Vec::new(),
            trait_indexes: Vec::new(),
            type_infos: TypeInfos::new(),
            typeids: HashMap::new(),
            interner: RefCell::new(Interner::new())
        };
        let a = Generic(0);
        let array_a = ArrayType(box a.clone());
        vm.extern_function("array_length", vec![array_a.clone()], int_type_tc.clone(), array_length);
        vm.extern_function("array_push", vec![array_a.clone(), a.clone()], unit_type_tc.clone(), array_push);
        vm
    }

    pub fn new_functions(&mut self, fns: Vec<CompiledFunction>) {
        self.globals.extend(fns.move_iter()
            .map(|CompiledFunction { id: id, typ: typ, instructions: instructions }|
                Global { id: id, typ: typ, value: Bytecode(instructions) }
            )
        )
    }

    fn add_trait_indexes(&mut self, indexes: Vec<TraitFunctions>) {
        self.trait_indexes.extend(indexes.move_iter())
    }

    pub fn get_global(&self, name: &str) -> Option<(uint, &Global)> {
        let n = self.intern(name);
        self.globals.iter().enumerate()
            .find(|g| n == g.ref1().id)
    }

    pub fn get_type<T: 'static>(&self) -> &TcType {
        let id = TypeId::of::<T>();
        self.typeids.find(&id)
            .expect("Expected type to be inserted before get_type call")
    }
    pub fn find_type_info(&self, s: &str) -> Option<TypeInfo> {
        let n = self.intern(s);
        (self as &TypeEnv).find_type_info(&n)
    }

    pub fn run_function(&self, cf: &Global) -> Option<Value> {
        let mut stack = Vec::new();
        {
            let frame = StackFrame::new(&mut stack, 0, None);
            self.execute_function(frame, cf);
        }
        stack.pop()
    }

    pub fn execute_instructions(&self, instructions: &[Instruction]) -> Option<Value> {
        let mut stack = Vec::new();
        {
            let frame = StackFrame::new(&mut stack, 0, None);
            self.execute(frame, instructions);
        }
        stack.pop()
    }

    pub fn extern_function(&mut self, name: &str, args: Vec<TcType>, return_type: TcType, f: ExternFunction) {
        let global = Global {
            id: self.intern(name),
            typ: Constrained { constraints: Vec::new(), value: FunctionType(args, box return_type) },
            value: Extern(f)
        };
        self.globals.push(global);
    }

    pub fn register_type<T: 'static>(&mut self, name: &str) -> Result<&TcType, ()> {
        let n = self.intern(name);
        if self.type_infos.structs.contains_key(&n) {
            Err(())
        }
        else {
            let id = TypeId::of::<T>();
            let t = &*self.typeids.find_or_insert(id, Type(n, Vec::new()));
            self.type_infos.structs.insert(n, Vec::new());
            Ok(t)
        }
    }
    fn intern(&self, s: &str) -> InternedStr {
        self.interner.borrow_mut().intern(s)
    }

    fn execute_function(&self, stack: StackFrame, function: &Global) {
        match function.value {
            Extern(func) => {
                func(self, stack);
            }
            Bytecode(ref instructions) => {
                self.execute(stack, instructions.as_slice());
            }
        }
    }

    pub fn execute(&self, mut stack: StackFrame, instructions: &[Instruction]) {
        debug!("Enter frame with {}", stack.as_slice());
        let mut index = 0;
        while index < instructions.len() {
            let instr = instructions[index];
            debug!("{}", instr);
            match instr {
                Push(i) => {
                    let v = stack.get(i).clone();
                    stack.push(v);
                }
                PushInt(i) => {
                    stack.push(Int(i));
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
                    let (function, upvars) = match stack.get(function_index) {
                        &Function(index) => {
                            (&self.globals[index], None)
                        }
                        &Closure(index, ref upvars) => {
                            (&self.globals[index], Some(upvars.clone()))
                        }
                        x => fail!("Cannot call {}", x)
                    };
                    {
                        debug!("Call {} :: {}", function.id, function.typ);
                        match upvars {
                            Some(upvars) => {
                                let ref u = *upvars;
                                let new_stack = StackFrame::new(stack.stack, args, Some(u));
                                self.execute_function(new_stack, function);
                            }
                            None => {
                                let new_stack = StackFrame::new(stack.stack, args, None);
                                self.execute_function(new_stack, function);
                            }
                        }
                    }
                    if stack.len() > function_index + args {
                        //Value was returned
                        let result = stack.pop();
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
                    let d = Data(tag, Rc::new(RefCell::new(fields)));
                    stack.push(d);
                }
                GetField(i) => {
                    match stack.pop() {
                        Data(_, fields) => {
                            let v = (*fields.borrow())[i].clone();
                            stack.push(v);
                        }
                        x => fail!("GetField on {}", x)
                    }
                }
                SetField(i) => {
                    let value = stack.pop();
                    let data = stack.pop();
                    match data {
                        Data(_, fields) => {
                            *(*fields.borrow_mut()).get_mut(i) = value;
                        }
                        _ => fail!()
                    }
                }
                TestTag(tag) => {
                    let x = match *stack.top() {
                        Data(t, _) => if t == tag { 1 } else { 0 },
                        _ => fail!()
                    };
                    stack.push(Int(x));
                }
                Split => {
                    match stack.pop() {
                        Data(_, fields) => {
                            for field in (*fields.borrow()).iter() {
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
                        (Data(_, array), Int(index)) => {
                            let v = (*array.borrow_mut())[index as uint].clone();
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
                        (Data(_, array), Int(index)) => {
                            *(*array.borrow_mut()).get_mut(index as uint) = value;
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
                    stack.push(Closure(fi, Rc::new(RefCell::new(upvars))));
                }
                PushUpVar(i) => {
                    let v = (*stack.upvars.unwrap().borrow())[i].clone();
                    stack.push(v);
                }
                StoreUpVar(i) => {
                    let v = stack.pop();
                    *(*stack.upvars.unwrap().borrow_mut()).get_mut(i) = v;
                }
                ConstructTraitObject(i) => {
                    let v = stack.pop();
                    stack.push(TraitObject(i, Rc::new(v)));
                }
                PushTraitFunction(i) => {
                    let func = match stack.top() {
                        &TraitObject(fi, _) => {
                            Function(fi + i)
                        }
                        _ => fail!()
                    };
                    stack.push(func);
                }
                Unpack => {
                    match stack.pop() {
                        TraitObject(_, obj) => stack.push((*obj).clone()),
                        _ => fail!()
                    }
                }
                PushDictionaryMember(trait_index, function_offset) => {
                    let func = match stack.upvars.map(|upvars| (*upvars.borrow())[0].clone())  {
                        Some(Data(_, dict)) => {
                            match (*dict.borrow())[trait_index] {
                                Function(i) => Function(i + function_offset),
                                _ => fail!()
                            }
                        }
                        ref x => fail!("PushDictionaryMember {}", x)
                    };
                    stack.push(func);
                }
                PushDictionary(index) => {
                    let dict = stack.upvars.map(|upvars| (*upvars.borrow())[0].clone())
                        .expect("Expected dictionary in upvalues");
                    let dict = match dict {
                        Data(_, fields) => (*fields.borrow())[index].clone(),
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
        Data(_, values) => {
            let i = values.borrow().len();
            stack.push(Int(i as int));
        }
        x => fail!("{}", x)
    }
}
fn array_push(_: &VM, mut stack: StackFrame) {
    let value = stack.pop();
    let data = stack.pop();
    match data {
        Data(_, values) => {
            values.borrow_mut().push(value);
        }
        _ => fail!()
    }
}

macro_rules! tryf(
    ($e:expr) => (try!(($e).map_err(|e| format!("{}", e))))
)

pub fn parse_expr(buffer: &mut Buffer, vm: &mut VM) -> Result<::ast::LExpr<TcIdent>, String> {
    let mut interner = vm.interner.borrow_mut();
    let mut parser = Parser::new(&mut *interner, buffer, |s| TcIdent { name: s, typ: unit_type_tc.clone() });
    parser.expression().map_err(|err| format!("{}", err))
}

pub fn load_script(vm: &mut VM, buffer: &mut Buffer) -> Result<(), String> {
    use parser::Parser;

    let mut module = {
        let mut cell = vm.interner.borrow_mut();
        let mut parser = Parser::new(&mut*cell, buffer, |s| TcIdent { typ: unit_type_tc.clone(), name: s });
        tryf!(parser.module())
    };
    let (type_infos, (functions, trait_indexes)) = {
        let vm: &VM = vm;
        let mut tc = Typecheck::new();
        tc.add_environment(vm);
        tryf!(tc.typecheck_module(&mut module));
        let env = (vm, &module);
        let mut compiler = Compiler::new(&env);
        (tc.type_infos, compiler.compile_module(&module))
    };
    vm.new_functions(functions);
    vm.add_trait_indexes(trait_indexes);
    vm.type_infos = type_infos;
    Ok(())
}

pub fn run_main(s: &str) -> Result<Option<Value>, String> {
    use std::io::BufReader;
    let mut buffer = BufReader::new(s.as_bytes());
    run_buffer_main(&mut buffer)
}
pub fn run_buffer_main(buffer: &mut Buffer) -> Result<Option<Value>, String> {
    let mut vm = VM::new();
    try!(load_script(&mut vm, buffer));
    let func = match vm.globals.iter().find(|g| g.id.as_slice() == "main") {
        Some(f) => f,
        None => return Err("Undefined main function".to_string())
    };
    let v = vm.run_function(func);
    Ok(v)
}

#[cfg(test)]
mod tests {
    use super::{Data, Int, run_main};
    use std::rc::Rc;
    use std::cell::RefCell;
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
        let value = run_main(text)
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
        let value = run_main(text)
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
        let value = run_main(text)
            .unwrap_or_else(|err| fail!("{}", err));
        assert_eq!(value, Some(Data(0, Rc::new(RefCell::new(vec![Int(11), Int(5)])))));
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
        let value = run_main(text)
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
        let value = run_main(text)
            .unwrap_or_else(|err| fail!("{}", err));
        assert_eq!(value, Some(Data(0, Rc::new(RefCell::new(vec![Int(1), Int(2), Int(33)])))));
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
        let value = run_main(text)
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
        let value = run_main(text)
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
        let value = run_main(text)
            .unwrap_or_else(|err| fail!("{}", err));
        assert_eq!(value, Some(Data(0, Rc::new(RefCell::new(vec![Int(2), Int(4), Int(6)])))));
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
        let value = run_main(text)
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
        let value = run_main(text)
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
        let value = run_main(text)
            .unwrap_or_else(|err| fail!("{}", err));
        assert_eq!(value, Some(Data(0, Rc::new(RefCell::new(vec![Int(0), Int(1)])))));//false
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
        let value = run_main(text)
            .unwrap_or_else(|err| fail!("{}", err));
        assert_eq!(value, Some(Data(0, Rc::new(RefCell::new(vec![Int(1), Int(0)])))));
    }
}

