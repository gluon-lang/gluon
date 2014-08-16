use std::rc::Rc;
use std::cell::RefCell;
use std::fmt;
use typecheck::*;
use compiler::*;
use interner::{InternedStr, intern};


#[deriving(PartialEq, Clone)]
pub enum Value {
    Int(int),
    Float(f64),
    Data(uint, Rc<RefCell<Vec<Value>>>),
    Function(uint),
    Closure(uint, Rc<RefCell<Vec<Value>>>),
    TraitObject(uint, Rc<Value>)
}

impl fmt::Show for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Int(i) => write!(f, "{}", i),
            Float(x) => write!(f, "{}f", x),
            Data(tag, ref ptr) => write!(f, "{{{} {}}}", tag, ptr.borrow()),
            Function(i) => write!(f, "<function {}>", i),
            Closure(fi, ref upvars) => write!(f, "{} {}", fi, upvars.borrow()),
            TraitObject(fns, ref o) => write!(f, "<{} {}>", fns, o)
        }
    }
}

pub type ExternFunction = fn (&VM, StackFrame);

#[deriving(Show)]
struct Global {
    id: InternedStr,
    typ: TcType,
    value: Global_
}
enum Global_ {
    Bytecode(Vec<Instruction>),
    Extern(ExternFunction)
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
}

impl CompilerEnv for VM {
    fn find_var(&self, id: &InternedStr) -> Option<Variable> {
        self.globals.iter()
            .enumerate()
            .find(|&(_, f)| f.id == *id)
            .map(|(i, _)| Global(i))
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
    fn find_trait_function(&self, typ: &TcType, id: &InternedStr) -> Option<uint> {
        self.globals.iter()
            .enumerate()
            .find(|&(_, f)| f.id == *id && f.typ == *typ)
            .map(|(i, _)| i)
    }
    fn find_object_function(&self, trait_type: &InternedStr, name: &InternedStr) -> Option<uint> {
        fail!()
    }
    fn next_function_index(&self) -> uint {
        self.globals.len()
    }
}

impl TypeEnv for VM {
    fn find_type(&self, id: &InternedStr) -> Option<&TcType> {
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
    fn new(v: &'a mut Vec<Value>, args: uint, upvars: Option<&'b RefCell<Vec<Value>>>) -> StackFrame<'a, 'b> {
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
        let mut vm = VM { globals: Vec::new(), trait_indexes: Vec::new(), type_infos: TypeInfos::new() };
        vm.extern_function("array_length", vec![ArrayType(box int_type_tc.clone())], int_type_tc.clone(), array_length);
        vm.extern_function("array_push", vec![ArrayType(box int_type_tc.clone()), int_type_tc.clone()], unit_type_tc.clone(), array_push);
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
            id: intern(name),
            typ: FunctionType(args, box return_type),
            value: Extern(f)
        };
        self.globals.push(global);
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

    fn execute(&self, mut stack: StackFrame, instructions: &[Instruction]) {
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
                        debug!("Call {}", function.id);
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
                        _ => fail!()
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
                AddInt => binop_int(&mut stack, |l, r| l + r),
                SubtractInt => binop_int(&mut stack, |l, r| l - r),
                MultiplyInt => binop_int(&mut stack, |l, r| l * r),
                IntLT => binop_int(&mut stack, |l, r| if l < r { 1 } else { 0 }),

                AddFloat => binop_float(&mut stack, |l, r| l + r),
                SubtractFloat => binop_float(&mut stack, |l, r| l - r),
                MultiplyFloat => binop_float(&mut stack, |l, r| l * r),
                FloatLT => binop(&mut stack, |l, r| {
                    match (l, r) {
                        (Float(l), Float(r)) => Int(if l < r { 1 } else { 0 }),
                        _ => fail!()
                    }
                })
            }
            index += 1;
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
        _ => fail!()
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

pub fn load_script(vm: &mut VM, buffer: &mut Buffer) -> Result<(), String> {
    use parser::Parser;

    let mut parser = Parser::new(buffer, |s| TcIdent { typ: unit_type_tc.clone(), name: s });
    let mut module = tryf!(parser.module());
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

    let mut vm = VM::new();
    let mut buffer = BufReader::new(s.as_bytes());
    try!(load_script(&mut vm, &mut buffer));
    let func = match vm.globals.iter().find(|g| g.id.as_slice() == "main") {
        Some(f) => f,
        None => return Err("Undefined main function".to_string())
    };
    let v = vm.run_function(func);
    Ok(v)
}

#[cfg(test)]
mod tests {
    use super::*;
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
}

