use std::collections::HashMap;
use interner::*;
use ast::*;

pub enum Instruction {
    PushInt(int),
    PushFloat(f64),
    Push(uint),
    Store(uint),
    Call(int, int),
    Jump(uint),
    CJump(uint),

    AddInt,
    SubtractInt,
    MultiplyInt
}

type CExpr = Expr<InternedStr>;

pub enum Variable {
    Stack(uint),
    Global(uint)
}

pub struct CompiledFunction {
    pub id: InternedStr,
    pub instructions: Vec<Instruction>
}

pub trait CompilerEnv {
    fn find_var(&self, id: &InternedStr) -> Option<Variable>;
}

impl CompilerEnv for () {
    fn find_var(&self, id: &InternedStr) -> Option<Variable> {
        None
    }
}

impl CompilerEnv for HashMap<InternedStr, Variable> {
    fn find_var(&self, s: &InternedStr) -> Option<Variable> {
        self.find(s).map(|x| *x)
    }
}

impl <T: CompilerEnv, U: CompilerEnv> CompilerEnv for (T, U) {
    fn find_var(&self, s: &InternedStr) -> Option<Variable> {
        let &(ref outer, ref inner) = self;
        inner.find_var(s)
            .or_else(|| outer.find_var(s))
    }
}

impl <'a, T: CompilerEnv> CompilerEnv for &'a T {
    fn find_var(&self, s: &InternedStr) -> Option<Variable> {
        self.find_var(s)
    }
}

pub struct Compiler<'a> {
    globals: &'a CompilerEnv,
    stack: HashMap<InternedStr, Variable>,
}

impl <'a> Compiler<'a> {

    pub fn new(globals: &'a CompilerEnv) -> Compiler<'a> {
        Compiler { globals: globals, stack: HashMap::new() }
    }

    fn find(&self, s: &InternedStr) -> Option<Variable> {
        self.stack.find_var(s)
            .or_else(||  self.globals.find_var(s))
    }

    fn new_stack_var(&mut self, s: InternedStr) {
        let v = Stack(self.stack.len());
        if self.stack.find(&s).is_some() {
            fail!("Variable shadowing is not allowed")
        }
        self.stack.insert(s, v);
    }

    fn stack_size(&self) -> uint {
        self.stack.len()
    }

    fn compile_function(&mut self, function: &Function<InternedStr>) -> CompiledFunction {
        for arg in function.arguments.iter() {
            self.new_stack_var(arg.name);
        }
        let mut instructions = Vec::new();
        self.compile(&function.expression, &mut instructions);
        for arg in function.arguments.iter() {
            self.stack.remove(&arg.name);
        }
        CompiledFunction { id: function.name, instructions: instructions }
    }


    fn compile(&mut self, expr: &CExpr, instructions: &mut Vec<Instruction>) {
        match *expr {
            Literal(ref lit) => {
                match *lit {
                    Integer(i) => instructions.push(PushInt(i)),
                    Float(f) => instructions.push(PushFloat(f)),
                    String(s) => fail!("String is not implemented")
                }
            }
            Identifier(ref id) => {
                match self.find(id).unwrap_or_else(|| fail!("Undefined variable {}", id)) {
                    Stack(index) => instructions.push(Push(index)),
                    _ => fail!()
                }
            }
            IfElse(ref pred, ref if_true, ref if_false) => {
                self.compile(&**pred, instructions);
                let jump_index = instructions.len();
                instructions.push(CJump(0));
                self.compile(&**if_false, instructions);
                let false_jump_index = instructions.len();
                instructions.push(Jump(0));
                *instructions.get_mut(jump_index) = CJump(instructions.len());
                self.compile(&**if_true, instructions);
                *instructions.get_mut(false_jump_index) = Jump(instructions.len());
            }
            Block(ref exprs) => {
                for expr in exprs.iter() {
                    self.compile(expr, instructions);
                }
                for expr in exprs.iter() {
                    match expr {
                        &Let(ref id, _) => {
                            self.stack.remove(id);
                        }
                        _ => ()
                    }
                }
            }
            BinOp(ref lhs, ref op, ref rhs) => {
                self.compile(&**lhs, instructions);
                self.compile(&**rhs, instructions);
                match op.as_slice() {
                    "+" => instructions.push(AddInt),
                    "-" => instructions.push(SubtractInt),
                    "*" => instructions.push(MultiplyInt),
                    _ => fail!()
                }
            }
            Let(ref id, ref expr) => {
                self.new_stack_var(*id);
                self.compile(&**expr, instructions);
            }
            _ => fail!()
        }
    }
}
