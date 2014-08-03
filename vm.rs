use std::rc::Rc;
use std::cell::RefCell;
use std::fmt;
use compiler::*;
use interner::InternedStr;


#[deriving(PartialEq, Clone)]
pub enum Value {
    Int(int),
    Data(Rc<RefCell<Vec<Value>>>),
    Function(uint)
}

impl fmt::Show for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Int(i) => write!(f, "{}", i),
            Data(ref ptr) => write!(f, "{}", ptr.borrow()),
            Function(i) => write!(f, "<function {}>", i),
        }
    }
}

pub struct VM {
    globals: Vec<CompiledFunction>
}

impl CompilerEnv for VM {
    fn find_var(&self, id: &InternedStr) -> Option<Variable> {
        self.globals.iter()
            .enumerate()
            .find(|&(_, f)| f.id == *id)
            .map(|(i, _)| Global(i))
    }
}

struct StackFrame<'a> {
    stack: &'a mut Vec<Value>,
    offset: uint
}
impl <'a> StackFrame<'a> {
    fn new(v: &'a mut Vec<Value>, args: uint) -> StackFrame<'a> {
        let offset = v.len() - args;
        StackFrame { stack: v, offset: offset }
    }

    fn len(&self) -> uint {
        self.stack.len() - self.offset
    }

    fn get<'a>(&'a self, i: uint) -> &'a Value {
        self.stack.get(self.offset + i)
    }
    fn get_mut<'a>(&'a mut self, i: uint) -> &'a mut Value {
        self.stack.get_mut(self.offset + i)
    }

    fn push(&mut self, v: Value) {
        self.stack.push(v);
    }

    fn pop(&mut self) -> Value {
        match self.stack.pop() {
            Some(x) => x,
            None => fail!()
        }
    }
}

impl VM {
    
    pub fn new() -> VM {
        VM { globals: Vec::new() }
    }

    pub fn new_functions(&mut self, fns: Vec<CompiledFunction>) {
        self.globals.extend(fns.move_iter())
    }

    pub fn get_function(&self, index: uint) -> &CompiledFunction {
        &self.globals[index]
    }

    pub fn run_function(&self, cf: &CompiledFunction) -> Value {
        let mut stack = Vec::new();
        {
            let frame = StackFrame::new(&mut stack, 0);
            self.execute(frame, cf.instructions.as_slice());
        }
        stack.pop().expect("Expected return value")
    }

    fn execute<'a>(&self, mut stack: StackFrame<'a>, instructions: &[Instruction]) {
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
                PushFloat(_) => fail!(),
                Store(i) => {
                    *stack.get_mut(i) = stack.pop();
                }
                CallGlobal(args) => {
                    let function = match stack.get(stack.len() - 1 - args) {
                        &Function(index) => {
                            &self.globals[index]
                        }
                        _ => fail!()
                    };
                    {
                        let new_stack = StackFrame::new(stack.stack, args);
                        self.execute(new_stack, function.instructions.as_slice());
                    }
                    let result = stack.pop();
                    for _ in range(0, args + 1) {
                        stack.pop();
                    }
                    stack.push(result);
                }
                Construct(args) => {
                    let mut fields = Vec::new();
                    for _ in range(0, args) {
                        fields.push(stack.pop());
                    }
                    fields.reverse();
                    let d = Data(Rc::new(RefCell::new(fields)));
                    stack.push(d);
                }
                GetField(i) => {
                    match stack.pop() {
                        Data(fields) => {
                            let v = (*fields.borrow())[i].clone();
                            stack.push(v);
                        }
                        x => fail!("GetField on {}", x)
                    }
                }
                SetField(i) => {
                    let data = stack.pop();
                    let value = stack.pop();
                    match data {
                        Data(fields) => {
                            *(*fields.borrow_mut()).get_mut(i) = value;
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
                AddInt => binop_int(&mut stack, |l, r| l + r),
                SubtractInt => binop_int(&mut stack, |l, r| l - r),
                MultiplyInt => binop_int(&mut stack, |l, r| l * r),
                IntLT => binop_int(&mut stack, |l, r| if l < r { 1 } else { 0 })
            }
            index += 1;
        }
    }
}

#[inline]
fn binop_int<'a>(stack: &mut StackFrame<'a>, f: |int, int| -> int) {
    let r = stack.pop();
    let l = stack.pop();
    match (l, r) {
        (Int(l), Int(r)) => stack.push(Int(f(l, r))),
        (l, r) => fail!("{} `op` {}", l, r)
    }
}

