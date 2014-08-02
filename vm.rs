use compiler::*;
use interner::InternedStr;


pub enum Value {
    Int(int)
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
    fn execute<'a>(&self, mut stack: StackFrame<'a>, instructions: &[Instruction]) {
        let mut index = 0;
        while index < instructions.len() {
            match instructions[index] {
                Push(i) => {
                    let v = *stack.get(i);
                    stack.push(v);
                }
                PushInt(i) => {
                    stack.push(Int(i));
                }
                PushFloat(_) => fail!(),
                Store(i) => {
                    *stack.get_mut(i) = stack.pop();
                }
                Call(..) => fail!(),
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
        (Int(l), Int(r)) => stack.push(Int(f(l, r)))
    }
}

