use std::collections::HashMap;
use interner::*;
use ast::*;
use typecheck::{Typed, TcIdent};

#[deriving(Show)]
pub enum Instruction {
    PushInt(int),
    PushFloat(f64),
    Push(uint),
    PushGlobal(uint),
    Store(uint),
    CallGlobal(uint),
    Construct(uint),
    GetField(uint),
    SetField(uint),
    Jump(uint),
    CJump(uint),

    AddInt,
    SubtractInt,
    MultiplyInt,
    IntLT,

    AddFloat,
    SubtractFloat,
    MultiplyFloat,
    FloatLT
}

type CExpr = Expr<TcIdent>;

pub enum Variable {
    Stack(uint),
    Global(uint),
    Constructor(uint)
}

pub struct CompiledFunction {
    pub id: InternedStr,
    pub instructions: Vec<Instruction>
}

pub trait CompilerEnv {
    fn find_var(&self, id: &InternedStr) -> Option<Variable>;
    fn find_field(&self, _struct: &InternedStr, _field: &InternedStr) -> Option<uint> {
        None
    }
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
    fn find_field(&self, struct_: &InternedStr, field: &InternedStr) -> Option<uint> {
        let &(ref outer, ref inner) = self;
        inner.find_field(struct_, field)
            .or_else(|| outer.find_field(struct_, field))
    }
}

impl CompilerEnv for Module<TcIdent> {
    fn find_var(&self, id: &InternedStr) -> Option<Variable> {
        self.functions.iter()
            .enumerate()
            .find(|&(_, f)| f.name.id() == id)
            .map(|(i, _)| Global(i))
            .or_else(|| self.structs.iter()
                .find(|s| s.name.id() == id)
                .map(|s| Constructor(s.fields.len()))
            )
    }
    fn find_field(&self, struct_: &InternedStr, field: &InternedStr) -> Option<uint> {
        self.structs.iter()
            .find(|s| s.name.id() == struct_)
            .map(|s| s.fields.iter()
                .enumerate()
                .find(|&(_, f)| f.name == *field)
                .map(|(i, _)| i).unwrap())
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

    fn find_field(&self, struct_: &InternedStr, field: &InternedStr) -> Option<uint> {
        self.stack.find_field(struct_, field)
            .or_else(||  self.globals.find_field(struct_, field))
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

    pub fn compile_module(&mut self, module: &Module<TcIdent>) -> Vec<CompiledFunction> {
        module.functions.iter()
            .map(|f| self.compile_function(f))
            .collect()
    }

    pub fn compile_function(&mut self, function: &Function<TcIdent>) -> CompiledFunction {
        for arg in function.arguments.iter() {
            self.new_stack_var(arg.name);
        }
        let mut instructions = Vec::new();
        self.compile(&function.expression, &mut instructions);
        for arg in function.arguments.iter() {
            self.stack.remove(&arg.name);
        }
        CompiledFunction { id: function.name.id().clone(), instructions: instructions }
    }


    fn compile(&mut self, expr: &CExpr, instructions: &mut Vec<Instruction>) {
        match *expr {
            Literal(ref lit) => {
                match *lit {
                    Integer(i) => instructions.push(PushInt(i)),
                    Float(f) => instructions.push(PushFloat(f)),
                    Bool(b) => instructions.push(PushInt(if b { 1 } else { 0 })),
                    String(s) => fail!("String is not implemented")
                }
            }
            Identifier(ref id) => {
                match self.find(id.id()).unwrap_or_else(|| fail!("Undefined variable {}", id.id())) {
                    Stack(index) => instructions.push(Push(index)),
                    Global(index) => instructions.push(PushGlobal(index)),
                    Constructor(num_args) => instructions.push(Construct(num_args))
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
                            self.stack.remove(id.id());
                        }
                        _ => ()
                    }
                }
            }
            BinOp(ref lhs, ref op, ref rhs) => {
                self.compile(&**lhs, instructions);
                self.compile(&**rhs, instructions);
                let typ = lhs.type_of();
                let instr = if *typ == int_type {
                    match op.as_slice() {
                        "+" => AddInt,
                        "-" => SubtractInt,
                        "*" => MultiplyInt,
                        "<" => IntLT,
                        _ => fail!()
                    }
                }
                else if *typ == float_type {
                    match op.as_slice() {
                        "+" => AddFloat,
                        "-" => SubtractFloat,
                        "*" => MultiplyFloat,
                        "<" => FloatLT,
                        _ => fail!()
                    }
                }
                else {
                    fail!()
                };
                instructions.push(instr);
            }
            Let(ref id, ref expr) => {
                self.new_stack_var(*id.id());
                self.compile(&**expr, instructions);
            }
            Call(ref func, ref args) => {
                match **func {
                    Identifier(ref id) => {
                        match self.find(id.id()).unwrap_or_else(|| fail!("Undefined variable {}", id.id())) {
                            Constructor(num_args) => {
                                for arg in args.iter() {
                                    self.compile(arg, instructions);
                                }
                                instructions.push(Construct(num_args));
                                return
                            }
                            _ => ()
                        }
                    }
                    _ => ()
                }
                self.compile(&**func, instructions);
                for arg in args.iter() {
                    self.compile(arg, instructions);
                }
                instructions.push(CallGlobal(args.len()));
            }
            While(ref pred, ref expr) => {
                //jump #test
                //#start:
                //[compile(expr)]
                //#test:
                //[compile(pred)]
                //cjump #start
                let mut pre_jump_index = instructions.len();
                instructions.push(Jump(0));
                self.compile(&**expr, instructions);
                *instructions.get_mut(pre_jump_index) = Jump(instructions.len());
                self.compile(&**pred, instructions);
                instructions.push(CJump(pre_jump_index + 1));
            }
            Assign(ref lhs, ref rhs) => {
                self.compile(&**rhs, instructions);
                match **lhs {
                    Identifier(ref id) => {
                        let var = self.find(id.id())
                            .unwrap_or_else(|| fail!("Undefined variable {}", id));
                        match var {
                            Stack(i) => instructions.push(Store(i)),
                            Global(_) => fail!("Assignment to global {}", id),
                            Constructor(_) => fail!("Assignment to constructor {}", id)
                        }
                    }
                    FieldAccess(ref expr, ref field) => {
                        self.compile(&**expr, instructions);
                        let field_index = match *expr.type_of() {
                            Type(ref id) => {
                                self.find_field(id, field.id())
                                    .unwrap()
                            }
                            _ => fail!()
                        };
                        instructions.push(SetField(field_index));
                    }
                    _ => fail!("Assignment to {}", lhs)
                }
            }
            FieldAccess(ref expr, ref field) => {
                self.compile(&**expr, instructions);
                let field_index = match *expr.type_of() {
                    Type(ref id) => {
                        self.find_field(id, field.id())
                            .unwrap()
                    }
                    _ => fail!()
                };
                instructions.push(GetField(field_index));
            }
            ref e => fail!("Cannot compile {}", e)
        }
    }

}
