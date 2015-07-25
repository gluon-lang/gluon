use base::interner::*;
use base::gc::Gc;
use base::ast;
use base::ast::{LExpr, Expr, Integer, Float, String, Bool};
use typecheck::{TcIdent, TcType, Type, Typed, TypeInfos, UNIT_TYPE};
use self::Instruction::*;
use self::Variable::*;

pub type VMIndex = u32;
pub type VMTag = u32;

#[derive(Copy, Clone, Debug)]
pub enum Instruction {
    PushInt(isize),
    PushFloat(f64),
    PushString(VMIndex),
    Push(VMIndex),
    PushGlobal(VMIndex),
    Store(VMIndex),
    StoreGlobal(VMIndex),
    Call(VMIndex),
    TailCall(VMIndex),
    Construct(VMIndex, VMIndex),
    GetField(VMIndex),
    SetField(VMIndex),
    Split,
    TestTag(VMTag),
    Jump(VMIndex),
    CJump(VMIndex),
    Pop(VMIndex),
    Slide(VMIndex),

    //Creates a closure with 'n' upvariables
    //Pops the 'n' values on top of the stack and creates a closure
    MakeClosure(VMIndex, VMIndex),
    //Creates a closure but does not fill its environment
    NewClosure(VMIndex, VMIndex),
    //Fills the previously allocated closure with `n` upvariables
    CloseClosure(VMIndex),
    InstantiateConstrained(VMIndex),
    PushUpVar(VMIndex),
    StoreUpVar(VMIndex),

    GetIndex,
    SetIndex,

    AddInt,
    SubtractInt,
    MultiplyInt,
    IntLT,
    IntEQ,

    AddFloat,
    SubtractFloat,
    MultiplyFloat,
    FloatLT,
    FloatEQ,
}

pub type CExpr = LExpr<TcIdent>;

pub enum Variable<'a> {
    Stack(VMIndex),
    Global(VMIndex, &'a TcType),
    Constructor(VMTag, VMIndex),
    UpVar(VMIndex)
}

#[derive(Debug)]
pub struct CompiledFunction {
    pub args: VMIndex,
    pub id: InternedStr,
    pub typ: TcType,
    pub instructions: Vec<Instruction>,
    pub inner_functions: Vec<CompiledFunction>,
    pub strings: Vec<InternedStr>
}

pub struct FunctionEnv {
    pub instructions: Vec<Instruction>,
    pub free_vars: Vec<InternedStr>,
    pub inner_functions: Vec<CompiledFunction>,
    pub strings: Vec<InternedStr>
}

impl FunctionEnv {
    pub fn new() -> FunctionEnv {
        FunctionEnv {
            instructions: Vec::new(),
            free_vars: Vec::new(),
            inner_functions: Vec::new(),
            strings: Vec::new()
        }
    }

    fn emit_call(&mut self, args: VMIndex, tail_position: bool) {
        let i = if tail_position {
            TailCall(args)
        }
        else {
            Call(args)
        };
        self.instructions.push(i);
    }

    fn emit_string(&mut self, s: InternedStr) {
        let index = match self.strings.iter().position(|t| *t == s) {
            Some(i) => i,
            None => {
                self.strings.push(s);
                self.strings.len() - 1 
            }
        };
        self.instructions.push(PushString(index as VMIndex));
    }

    fn upvar(&mut self, s: InternedStr) -> VMIndex {
        match (0..).zip(self.free_vars.iter()).find(|t| *t.1 == s).map(|t| t.0) {
            Some(index) => index,
            None => {
                self.free_vars.push(s);
                (self.free_vars.len() - 1) as VMIndex
            }
        }
    }
}

pub trait CompilerEnv {
    fn find_var(&self, id: &InternedStr) -> Option<Variable>;
    fn find_field(&self, _struct: &InternedStr, _field: &InternedStr) -> Option<VMIndex>;
    fn find_tag(&self, _: &InternedStr, _: &InternedStr) -> Option<VMTag>;
    fn next_global_index(&self) -> VMIndex;
}

impl <T: CompilerEnv, U: CompilerEnv> CompilerEnv for (T, U) {
    fn find_var(&self, s: &InternedStr) -> Option<Variable> {
        let &(ref outer, ref inner) = self;
        inner.find_var(s)
            .map(|var| match var {
                Global(i, y) => Global(i + outer.next_global_index(), y),
                var => var
            })
            .or_else(|| outer.find_var(s))
    }
    fn find_field(&self, struct_: &InternedStr, field: &InternedStr) -> Option<VMIndex> {
        let &(ref outer, ref inner) = self;
        inner.find_field(struct_, field)
            .or_else(|| outer.find_field(struct_, field))
    }

    fn find_tag(&self, struct_: &InternedStr, field: &InternedStr) -> Option<VMTag> {
        let &(ref outer, ref inner) = self;
        inner.find_tag(struct_, field)
            .or_else(|| outer.find_tag(struct_, field))
    }
    fn next_global_index(&self) -> VMIndex {
        let &(ref outer, ref inner) = self;
        outer.next_global_index() + inner.next_global_index()
    }
}

impl <'a, T: CompilerEnv> CompilerEnv for &'a T {
    fn find_var(&self, s: &InternedStr) -> Option<Variable> {
        (*self).find_var(s)
    }
    fn find_field(&self, struct_: &InternedStr, field: &InternedStr) -> Option<VMIndex> {
        (*self).find_field(struct_, field)
    }

    fn find_tag(&self, enum_: &InternedStr, ctor_name: &InternedStr) -> Option<VMTag> {
        (*self).find_tag(enum_, ctor_name)
    }
    fn next_global_index(&self) -> VMIndex {
        (*self).next_global_index()
    }
}
impl CompilerEnv for TypeInfos {
    fn find_var(&self, id: &InternedStr) -> Option<Variable> {
        fn count_function_args(typ: &TcType) -> VMIndex {
            match *typ {
                Type::Function(_, ref rest) => 1 + count_function_args(rest),
                _ => 0
            }
        }

        self.id_to_type.iter()
            .filter_map(|(_, typ)| {
                match *typ {
                    Type::Variants(ref variants) => variants.iter()
                                                        .enumerate()
                                                        .find(|&(_, v)| v.0 == *id),
                    _ => None
                }
            })
            .next()
            .map(|(tag, &(_, ref typ))| {
                Variable::Constructor(tag as VMTag, count_function_args(&typ))
            })
    }
    fn find_field(&self, struct_: &InternedStr, field: &InternedStr) -> Option<VMIndex> {
        self.id_to_type.get(struct_)
            .and_then(|typ| {
                match *typ {
                    Type::Record(ref fields) => fields.iter()
                        .position(|f| f.name == *field)
                        .map(|i| i as VMIndex),
                    _ => None
                }
            })
    }

    fn find_tag(&self, type_id: &InternedStr, ctor_name: &InternedStr) -> Option<VMTag> {
        self.id_to_type.get(type_id)
            .and_then(|typ| {
                match *typ {
                    Type::Variants(ref variants) => variants.iter()
                                                        .enumerate()
                                                        .find(|&(_, v)| v.0 == *ctor_name)
                                                        .map(|t| t.0 as VMTag),
                    _ => None
                }
            })
    }
    fn next_global_index(&self) -> VMIndex {
        0
    }
}

pub struct Compiler<'a> {
    globals: &'a (CompilerEnv + 'a),
    stack: Vec<InternedStr>,
    //Stack which holds indexes for where each closure starts its stack variables
    closure_limits: Vec<VMIndex>,
    interner: &'a mut Interner,
    gc: &'a mut Gc
}

impl <'a> Compiler<'a> {

    pub fn new(globals: &'a CompilerEnv, interner: &'a mut Interner, gc: &'a mut Gc) -> Compiler<'a> {
        Compiler {
            globals: globals,
            stack: Vec::new(),
            closure_limits: Vec::new(),
            interner: interner,
            gc: gc
        }
    }

    fn intern(&mut self, s: &str) -> InternedStr {
        self.interner.intern(self.gc, s)
    }

    fn find(&self, id: &InternedStr, env: &mut FunctionEnv) -> Option<Variable> {
        (0..self.stack.len() as VMIndex).zip(self.stack.iter()).rev()
            .find(|&(_, var)| var == id)
            .map(|(index, _)| {
                if self.closure_limits.len() != 0 {
                    let closure_stack_start = *self.closure_limits.last()
                            .expect("find: closure_limits");
                    if index < closure_stack_start {
                        let i = env.upvar(*id);
                        UpVar(i)
                    }
                    else {
                        Stack(index - closure_stack_start)
                    }
                }
                else {
                    Stack(index)
                }
            })
            .or_else(||  self.globals.find_var(id))
    }

    fn find_field(&self, struct_: &ast::TypeConstructor<InternedStr>, field: &InternedStr) -> Option<VMIndex> {
        match *struct_ {
            ast::TypeConstructor::Data(ref struct_) => self.globals.find_field(struct_, field),
            _ => None
        }
    }

    fn find_tag(&self, enum_: &ast::TypeConstructor<InternedStr>, constructor: &InternedStr) -> Option<VMTag> {
        match *enum_ {
            ast::TypeConstructor::Data(ref enum_) => self.globals.find_tag(enum_, constructor),
            _ => None
        }
    }

    fn new_stack_var(&mut self, s: InternedStr) {
        self.stack.push(s);
    }

    fn stack_size(&self) -> VMIndex {
        self.stack.len() as VMIndex - self.closure_limits.last().map(|&x| x).unwrap_or(0)
    }

    ///Compiles an expression to a zero argument function which can be directly fed to the
    ///interpreter
    pub fn compile_expr(&mut self, expr: &CExpr) -> CompiledFunction {
        let mut env = FunctionEnv::new();
        self.compile(expr, &mut env, true);
        let FunctionEnv { instructions, inner_functions, strings, .. } = env;
        CompiledFunction {
            args: 0,
            id: self.intern(""),
            typ: Type::Function(vec![], Box::new(expr.type_of().clone())),
            instructions: instructions,
            inner_functions: inner_functions,
            strings: strings
        }
    }

    fn load_identifier(&self, id: InternedStr, function: &mut FunctionEnv) {
        match self.find(&id, function).unwrap_or_else(|| panic!("Undefined variable {}", id)) {
            Stack(index) => function.instructions.push(Push(index)),
            UpVar(index) => function.instructions.push(PushUpVar(index)),
            Global(index, _) => function.instructions.push(PushGlobal(index)),
            Constructor(tag, 0) => function.instructions.push(Construct(tag, 0)),
            Constructor(..) => panic!("Constructor {:?} is not fully applied", id)
        }
    }

    fn compile(&mut self, expr: &CExpr, function: &mut FunctionEnv, tail_position: bool) {
        match expr.value {
            Expr::Literal(ref lit) => {
                match *lit {
                    Integer(i) => function.instructions.push(PushInt(i as isize)),
                    Float(f) => function.instructions.push(PushFloat(f)),
                    Bool(b) => function.instructions.push(PushInt(if b { 1 } else { 0 })),
                    String(s) => function.emit_string(s)
                }
            }
            Expr::Identifier(ref id) => self.load_identifier(*id.id(), function),
            Expr::IfElse(ref pred, ref if_true, ref if_false) => {
                self.compile(&**pred, function, false);
                let jump_index = function.instructions.len();
                function.instructions.push(CJump(0));
                if let Some(ref if_false) = *if_false {
                    self.compile(&**if_false, function, tail_position);
                }
                let false_jump_index = function.instructions.len();
                function.instructions.push(Jump(0));
                function.instructions[jump_index] = CJump(function.instructions.len() as VMIndex);
                self.compile(&**if_true, function, tail_position);
                function.instructions[false_jump_index] = Jump(function.instructions.len() as VMIndex);
            }
            Expr::BinOp(ref lhs, ref op, ref rhs) => {
                if op.name == "&&" {
                    self.compile(&**lhs, function, false);
                    let lhs_end = function.instructions.len();
                    function.instructions.push(CJump(lhs_end as VMIndex + 3));//Jump to rhs evaluation
                    function.instructions.push(PushInt(0));
                    function.instructions.push(Jump(0));//lhs false, jump to after rhs
                    self.compile(&**rhs, function, tail_position);
                    function.instructions[lhs_end + 2] = Jump(function.instructions.len() as VMIndex);//replace jump instruction
                }
                else if op.name == "||" {
                    self.compile(&**lhs, function, false);
                    let lhs_end = function.instructions.len();
                    function.instructions.push(CJump(0));
                    self.compile(&**rhs, function, tail_position);
                    function.instructions.push(Jump(0));
                    function.instructions[lhs_end] = CJump(function.instructions.len() as VMIndex);
                    function.instructions.push(PushInt(1));
                    let end = function.instructions.len();
                    function.instructions[end - 2] = Jump(end as VMIndex);
                }
                else {
                    let instr = match &op.name[..] {
                        "#Int+" => AddInt,
                        "#Int-" => SubtractInt,
                        "#Int*" => MultiplyInt,
                        "#Int<" => IntLT,
                        "#Int==" => IntEQ,
                        "#Float+" => AddFloat,
                        "#Float-" => SubtractFloat,
                        "#Float*" => MultiplyFloat,
                        "#Float<" => FloatLT,
                        "#Float==" => FloatEQ,
                        _ => {
                            self.load_identifier(*op.id(), function);
                            Call(2)
                        }
                    };
                    self.compile(&**lhs, function, false);
                    self.compile(&**rhs, function, false);
                    function.instructions.push(instr);
                }
            }
            Expr::Let(ref bindings, ref body) => {
                let stack_start = self.stack_size();
                //Index where the instruction to create the first closure should be at
                let first_index = function.instructions.len();
                let is_recursive = bindings.iter().all(|bind| bind.arguments.len() > 0);
                if is_recursive {
                    for bind in bindings.iter() {
                        match bind.name {
                            ast::Pattern::Identifier(ref name) => {
                                self.new_stack_var(*name.id());
                            }
                            _ => panic!("ICE: Unexpected non identifer pattern")
                        }
                        //Add the NewClosure instruction before hand
                        //it will be fixed later
                        function.instructions.push(NewClosure(0, 0));
                    }
                }
                for (i, bind) in bindings.iter().enumerate() {

                    if is_recursive {
                        function.instructions.push(Push(stack_start + i as VMIndex));
                        let name = match bind.name {
                            ast::Pattern::Identifier(ref name) => name,
                            _ => panic!("Lambda binds to non identifer pattern")
                        };
                        let (function_index, vars, cf) = self.compile_lambda(&name, &bind.arguments, &bind.expression, function);
                        let offset = first_index + i;
                        function.instructions[offset] = NewClosure(function_index, vars);
                        function.instructions.push(CloseClosure(vars));
                        function.inner_functions.push(cf);
                    }
                    else {
                        self.compile(&bind.expression, function, false);
                        match bind.name {
                            ast::Pattern::Identifier(ref name) => {
                                self.new_stack_var(*name.id());
                            }
                            ast::Pattern::Record(ref record) => {
                                function.instructions.push(Split);
                                for &(mut name, bind) in record {
                                    name = bind.unwrap_or(name);
                                    self.new_stack_var(name);
                                }
                            }
                            ast::Pattern::Constructor(..) => {
                                panic!("constructor pattern in let")
                            }
                        }
                    }
                    //unit expressions do not return a value so we need to add a dummy value
                    //To make the stack correct
                    if *bind.expression.type_of() == UNIT_TYPE {
                        function.instructions.push(PushInt(0));
                    }
                }
                self.compile(&body, function, tail_position);
                for _ in 0..bindings.len() {
                    self.stack.pop();
                }
                function.instructions.push(Slide(bindings.len() as VMIndex));
            }
            Expr::Call(ref func, ref args) => {
                if let Expr::Identifier(ref id) = func.value {
                    if let Some(Constructor(tag, num_args)) = self.find(id.id(), function) {
                        for arg in args.iter() {
                            self.compile(arg, function, false);
                        }
                        function.instructions.push(Construct(tag, num_args));
                        return
                    }
                }
                self.compile(&**func, function, false);
                for arg in args.iter() {
                    self.compile(arg, function, false);
                }
                function.emit_call(args.len() as VMIndex, tail_position);
            }
            Expr::FieldAccess(ref expr, ref field) => {
                self.compile(&**expr, function, tail_position);
                debug!("{:?} {:?}", expr, field);
                let typ = expr.type_of().inner_app();
                debug!("FieldAccess {}", typ);
                let field_index = match *typ {
                    Type::Data(ref id, _) => {
                        self.find_field(id, field.id())
                    }
                    Type::Record(ref fields) => {
                        fields.iter()
                            .position(|f| f.name == field.name)
                            .map(|i| i as VMIndex)
                    }
                    ref typ => panic!("ICE: FieldAccess on {}", typ)
                }.expect("ICE: Undefined field in field access");
                function.instructions.push(GetField(field_index));
            }
            Expr::Match(ref expr, ref alts) => {
                self.compile(&**expr, function, false);
                let mut start_jumps = Vec::new();
                let mut end_jumps = Vec::new();
                let typename = match expr.type_of() {
                    &Type::Data(ref id, _) => Some(id),
                    _ => None
                };
                let mut catch_all = false;
                for alt in alts.iter() {
                    match alt.pattern {
                        ast::Pattern::Constructor(ref id, _) => {
                            let typename = typename.expect("typename");
                            let tag = self.find_tag(typename, id.id())
                                .unwrap_or_else(|| panic!("Could not find tag for {}::{}", typename, id.id()));
                            function.instructions.push(TestTag(tag));
                            start_jumps.push(function.instructions.len());
                            function.instructions.push(CJump(0));
                        }
                        ast::Pattern::Record(_) => {
                            catch_all = true;
                            start_jumps.push(function.instructions.len());
                        }
                        _ => {
                            catch_all = true;
                            start_jumps.push(function.instructions.len());
                            function.instructions.push(Jump(0));
                        }
                    }
                }
                //Create a catch all to prevent us from running into undefined behaviour
                if !catch_all {
                    let error_fn = self.intern("#error");
                    self.load_identifier(error_fn, function);
                    function.emit_string(self.intern("Non-exhaustive pattern"));
                    function.instructions.push(Call(1));
                }
                for (alt, &start_index) in alts.iter().zip(start_jumps.iter()) {
                    match alt.pattern {
                        ast::Pattern::Constructor(_, ref args) => {
                            function.instructions[start_index] = CJump(function.instructions.len() as VMIndex);
                            function.instructions.push(Split);
                            for arg in args.iter() {
                                self.new_stack_var(arg.id().clone());
                            }
                        }
                        ast::Pattern::Record(ref record) => {
                            function.instructions.push(Split);
                            for &(mut name, bind) in record {
                                name = bind.unwrap_or(name);
                                self.new_stack_var(name);
                            }
                        }
                        ast::Pattern::Identifier(ref id) => {
                            function.instructions[start_index] = Jump(function.instructions.len() as VMIndex);
                            self.new_stack_var(id.id().clone());
                        }
                    }
                    self.compile(&alt.expression, function, tail_position);
                    end_jumps.push(function.instructions.len());
                    function.instructions.push(Jump(0));

                    match alt.pattern {
                        ast::Pattern::Constructor(_, ref args) => {
                            for _ in 0..args.len() {
                                self.stack.pop();
                            }
                        }
                        ast::Pattern::Record(ref record) => {
                            for _ in record {
                                self.stack.pop();
                            }
                        }
                        ast::Pattern::Identifier(_) => { self.stack.pop(); }
                    }
                }
                for &index in end_jumps.iter() {
                    function.instructions[index] = Jump(function.instructions.len() as VMIndex);
                }
            }
            Expr::Array(ref a) => {
                for expr in a.expressions.iter() {
                    self.compile(expr, function, false);
                }
                function.instructions.push(Construct(0, a.expressions.len() as VMIndex));
            }
            Expr::ArrayAccess(ref array, ref index) => {
                self.compile(&**array, function, false);
                self.compile(&**index, function, tail_position);
                function.instructions.push(GetIndex);
            }
            Expr::Lambda(ref lambda) => {
                let (function_index, vars, cf) = self.compile_lambda(&lambda.id, &lambda.arguments, &lambda.body, function);
                function.instructions.push(MakeClosure(function_index, vars));
                function.inner_functions.push(cf);
            }
            Expr::Type(_, _, ref expr) => self.compile(&**expr, function, tail_position),
            Expr::Record(_, ref fields) => {
                for field in fields {
                    match field.1 {
                        Some(ref field_expr) => self.compile(field_expr, function, false),
                        None => self.load_identifier(field.0, function)
                    }
                }
                function.instructions.push(Construct(0, fields.len() as u32));
            }
            Expr::Tuple(ref exprs) => {
                for expr in exprs {
                    self.compile(expr, function, false);
                }
                function.instructions.push(Construct(0, exprs.len() as u32));
            }
        }
    }

    fn compile_lambda(&mut self,
                      id: &TcIdent,
                      arguments: &[TcIdent],
                      body: &LExpr<TcIdent>, parent: &mut FunctionEnv
                     ) -> (VMIndex, VMIndex, CompiledFunction) {
        self.closure_limits.push(self.stack.len() as VMIndex);
        for arg in arguments {
            self.new_stack_var(*arg.id());
        }
        let mut f = FunctionEnv::new();
        self.compile(body, &mut f, true);

        self.closure_limits.pop().expect("closure_limits: pop");
        for _ in 0..arguments.len() {
            self.stack.pop();
        }
        //Insert all free variables into the above globals free variables
        //if they arent in that lambdas scope
        for var in f.free_vars.iter() {
            match self.find(var, parent).expect("free_vars: find") {
                Stack(index) => parent.instructions.push(Push(index)),
                UpVar(index) => parent.instructions.push(PushUpVar(index)),
                _ => panic!("Free variables can only be on the stack or another upvar")
            }
        }
        let function_index = parent.inner_functions.len() as VMIndex;
        let free_vars = f.free_vars.len() as VMIndex;
        let FunctionEnv { instructions, inner_functions, strings, .. } = f;
        (function_index, free_vars, CompiledFunction {
            args: arguments.len() as VMIndex,
            id: id.id().clone(),
            typ: id.typ.clone(),
            instructions: instructions,
            inner_functions: inner_functions,
            strings: strings
        })
    }
}

