use std::rc::Rc;
use std::cell::RefCell;
use std::fmt;
use std::collections::HashMap;
use typecheck::{TypeEnv, Typecheck, TcIdent, TcType, TypeInfo, Struct, Enum};
use compiler::*;
use interner::InternedStr;


#[deriving(PartialEq, Clone)]
pub enum Value {
    Int(int),
    Float(f64),
    Data(uint, Rc<RefCell<Vec<Value>>>),
    Function(uint)
}

impl fmt::Show for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Int(i) => write!(f, "{}", i),
            Float(x) => write!(f, "{}f", x),
            Data(tag, ref ptr) => write!(f, "{{{} {}}}", tag, ptr.borrow()),
            Function(i) => write!(f, "<function {}>", i),
        }
    }
}

pub struct VM {
    globals: Vec<CompiledFunction>,
    type_infos: HashMap<InternedStr, TypeInfo>
}

impl CompilerEnv for VM {
    fn find_var(&self, id: &InternedStr) -> Option<Variable> {
        self.globals.iter()
            .enumerate()
            .find(|&(_, f)| f.id == *id)
            .map(|(i, _)| Global(i))
    }
}

impl TypeEnv for VM {
    fn find_type(&self, id: &InternedStr) -> Option<&TcType> {
        self.globals.iter()
            .find(|f| f.id == *id)
            .map(|f| &f.typ)
    }
    fn find_type_info(&self, id: &InternedStr) -> Option<&TypeInfo> {
        self.type_infos.find(id)
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
    fn top(&mut self) -> &Value {
        self.stack.last().unwrap()
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
        VM { globals: Vec::new(), type_infos: HashMap::new() }
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
                PushFloat(f) => stack.push(Float(f)),
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
                    let data = stack.pop();
                    let value = stack.pop();
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
fn binop<'a>(stack: &mut StackFrame<'a>, f: |Value, Value| -> Value) {
    let r = stack.pop();
    let l = stack.pop();
    stack.push(f(l, r));
}
#[inline]
fn binop_int<'a>(stack: &mut StackFrame<'a>, f: |int, int| -> int) {
    binop(stack, |l, r| {
        match (l, r) {
            (Int(l), Int(r)) => Int(f(l, r)),
            (l, r) => fail!("{} `intOp` {}", l, r)
        }
    })
}
#[inline]
fn binop_float<'a>(stack: &mut StackFrame<'a>, f: |f64, f64| -> f64) {
    binop(stack, |l, r| {
        match (l, r) {
            (Float(l), Float(r)) => Float(f(l, r)),
            (l, r) => fail!("{} `floatOp` {}", l, r)
        }
    })
}

pub fn run_main(s: &str) -> Result<Value, String> {
    use std::io::BufReader;
    use ast::*;
    use parser::Parser;

    let mut buffer = BufReader::new(s.as_bytes());
    let mut parser = Parser::new(&mut buffer, |s| TcIdent { typ: unit_type.clone(), name: s });
    let mut module = match parser.module() {
        Ok(f) => f,
        Err(x) => return Err(format!("{}", x))
    };
    let mut tc = Typecheck::new();
    try!(tc.typecheck_module(&mut module)
        .map_err(|e| format!("{}", e)));
    let mut compiler = Compiler::new(&module);
    let functions = compiler.compile_module(&module);
    let mut vm = VM::new();
    vm.new_functions(functions);
    let v = vm.run_function(vm.get_function(0));
    Ok(v)
}

#[cfg(test)]
mod tests {
    use super::*;
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
        assert_eq!(value, Int(8));
    }
}

