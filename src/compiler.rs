use base::interner::*;
use base::ast;
use base::ast::{LExpr, Expr, LambdaStruct, Integer, Float, String, Bool, ConstructorPattern, IdentifierPattern, Constraint, Constrained};
use typecheck::*;
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

pub struct Assembly {
    pub initializer: Vec<Instruction>,
    pub globals: Vec<Binding>,
    pub anonymous_functions: Vec<CompiledFunction>,
}

#[derive(Debug)]
pub struct Binding {
    pub name: InternedStr,
    pub typ: Constrained<TcType>,
}

#[derive(Debug)]
pub struct CompiledFunction {
    pub id: InternedStr,
    pub typ: Constrained<TcType>,
    pub instructions: Vec<Instruction>,
    pub inner_functions: Vec<CompiledFunction>,
    pub strings: Vec<InternedStr>
}

pub struct FunctionEnv<'a> {
    pub instructions: Vec<Instruction>,
    pub free_vars: Vec<InternedStr>,
    pub dictionary: &'a [Constraint],//Typevariable -> Trait
    pub inner_functions: Vec<CompiledFunction>,
    pub strings: Vec<InternedStr>
}

impl <'a> FunctionEnv<'a> {
    pub fn new() -> FunctionEnv<'a> {
        FunctionEnv {
            instructions: Vec::new(),
            free_vars: Vec::new(),
            dictionary: &[],
            inner_functions: Vec::new(),
            strings: Vec::new()
        }
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

#[derive(Debug)]
pub struct TypeResult<'a, T> {
    pub constraints: &'a [Constraint],
    pub typ: &'a TcType,
    pub value: T
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
    empty_string: InternedStr
}

impl <'a> Compiler<'a> {

    pub fn new(globals: &'a CompilerEnv, empty_string: InternedStr) -> Compiler<'a> {
        Compiler {
            globals: globals,
            stack: Vec::new(),
            closure_limits: Vec::new(),
            empty_string: empty_string
        }
    }

    fn find(&self, id: &InternedStr, env: &mut FunctionEnv) -> Option<Variable> {
        (0..).zip(self.stack.iter())
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
        if self.stack.iter().find(|i| **i == s).is_some() {
            panic!("Variable shadowing is not allowed")
        }
        self.stack.push(s);
    }

    fn stack_size(&self) -> VMIndex {
        self.stack.len() as VMIndex
    }

    ///Compiles an expression to a zero argument function which can be directly fed to the
    ///interpreter
    pub fn compile_expr(&mut self, expr: &CExpr) -> CompiledFunction {
        let mut env = FunctionEnv::new();
        self.compile(expr, &mut env);
        let FunctionEnv { instructions, inner_functions, strings, .. } = env;
        CompiledFunction {
            id: self.empty_string,
            typ: Constrained {
                constraints: Vec::new(),
                value: Type::Function(vec![], Box::new(expr.type_of().clone()))
            },
            instructions: instructions,
            inner_functions: inner_functions,
            strings: strings
        }
    }

    fn load_identifier(&self, id: &InternedStr, function: &mut FunctionEnv) {
        match self.find(id, function).unwrap_or_else(|| panic!("Undefined variable {}", id)) {
            Stack(index) => function.instructions.push(Push(index)),
            UpVar(index) => function.instructions.push(PushUpVar(index)),
            Global(index, _) => function.instructions.push(PushGlobal(index)),
            Constructor(tag, 0) => function.instructions.push(Construct(tag, 0)),
            Constructor(..) => panic!("Constructor {:?} is not fully applied", id)
        }
    }

    fn compile(&mut self, expr: &CExpr, function: &mut FunctionEnv) {
        match expr.value {
            Expr::Literal(ref lit) => {
                match *lit {
                    Integer(i) => function.instructions.push(PushInt(i as isize)),
                    Float(f) => function.instructions.push(PushFloat(f)),
                    Bool(b) => function.instructions.push(PushInt(if b { 1 } else { 0 })),
                    String(s) => {
                        function.instructions.push(PushString(function.strings.len() as VMIndex));
                        function.strings.push(s);
                    }
                }
            }
            Expr::Identifier(ref id) => self.load_identifier(id.id(), function),
            Expr::IfElse(ref pred, ref if_true, ref if_false) => {
                self.compile(&**pred, function);
                let jump_index = function.instructions.len();
                function.instructions.push(CJump(0));
                if let Some(ref if_false) = *if_false {
                    self.compile(&**if_false, function);
                }
                let false_jump_index = function.instructions.len();
                function.instructions.push(Jump(0));
                function.instructions[jump_index] = CJump(function.instructions.len() as VMIndex);
                self.compile(&**if_true, function);
                function.instructions[false_jump_index] = Jump(function.instructions.len() as VMIndex);
            }
            Expr::Block(ref exprs) => {
                let begin_stack_size = self.stack_size();
                if exprs.len() != 0 {
                    for expr in exprs[..exprs.len() - 1].iter() {
                        self.compile(expr, function);
                        //Since this line is executed as a statement we need to remove
                        //the value from the stack if it exists
                        if *expr.type_of() != UNIT_TYPE {
                            function.instructions.push(Pop(1));
                        }
                    }
                    let last = exprs.last().unwrap();
                    self.compile(last, function);
                }
                //If the stack has changed size during the block we need to adjust
                //it back to its initial size
                let diff_size = self.stack_size() - begin_stack_size;
                for _ in 0..diff_size {
                    self.stack.pop();
                }
                if diff_size != 0 {
                    if *expr.type_of() == UNIT_TYPE {
                        function.instructions.push(Pop(diff_size));
                    }
                    else {
                        function.instructions.push(Slide(diff_size));
                    }
                }
                
            }
            Expr::BinOp(ref lhs, ref op, ref rhs) => {
                if op.name == "&&" {
                    self.compile(&**lhs, function);
                    let lhs_end = function.instructions.len();
                    function.instructions.push(CJump(lhs_end as VMIndex + 3));//Jump to rhs evaluation
                    function.instructions.push(PushInt(0));
                    function.instructions.push(Jump(0));//lhs false, jump to after rhs
                    self.compile(&**rhs, function);
                    function.instructions[lhs_end + 2] = Jump(function.instructions.len() as VMIndex);//replace jump instruction
                }
                else if op.name == "||" {
                    self.compile(&**lhs, function);
                    let lhs_end = function.instructions.len();
                    function.instructions.push(CJump(0));
                    self.compile(&**rhs, function);
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
                            self.load_identifier(op.id(), function);
                            Call(2)
                        }
                    };
                    self.compile(&**lhs, function);
                    self.compile(&**rhs, function);
                    function.instructions.push(instr);
                }
            }
            Expr::Let(ref id, ref expr, ref body) => {
                self.compile(&**expr, function);
                self.new_stack_var(*id.id());
                //unit expressions do not return a value so we need to add a dummy value
                //To make the stack correct
                if *expr.type_of() == UNIT_TYPE {
                    function.instructions.push(PushInt(0));
                }
                if let Some(ref body) = *body {
                    self.compile(&body, function);
                }
            }
            Expr::Call(ref func, ref args) => {
                if let Expr::Identifier(ref id) = func.value {
                    if let Some(Constructor(tag, num_args)) = self.find(id.id(), function) {
                        for arg in args.iter() {
                            self.compile(arg, function);
                        }
                        function.instructions.push(Construct(tag, num_args));
                        return
                    }
                }
                self.compile(&**func, function);
                for arg in args.iter() {
                    self.compile(arg, function);
                }
                function.instructions.push(Call(args.len() as VMIndex));
            }
            Expr::While(ref pred, ref expr) => {
                //jump #test
                //#start:
                //[compile(expr)]
                //#test:
                //[compile(pred)]
                //cjump #start
                let pre_jump_index = function.instructions.len();
                function.instructions.push(Jump(0));
                self.compile(&**expr, function);
                function.instructions[pre_jump_index] = Jump(function.instructions.len() as VMIndex);
                self.compile(&**pred, function);
                function.instructions.push(CJump(pre_jump_index as VMIndex + 1));
            }
            Expr::Assign(ref lhs, ref rhs) => {
                match ***lhs {
                    Expr::Identifier(ref id) => {
                        self.compile(&**rhs, function);
                        let var = self.find(id.id(), function)
                            .unwrap_or_else(|| panic!("Undefined variable {:?}", id));
                        match var {
                            Stack(i) => function.instructions.push(Store(i)),
                            UpVar(i) => function.instructions.push(StoreUpVar(i)),
                            Global(..) => panic!("Assignment to global {:?}", id),
                            Constructor(..) => panic!("Assignment to constructor {:?}", id),
                        }
                    }
                    Expr::FieldAccess(ref expr, ref field) => {
                        self.compile(&**expr, function);
                        self.compile(&**rhs, function);
                        let field_index = match *expr.type_of() {
                            Type::Data(ref id, _) => {
                                self.find_field(id, field.id())
                                    .expect("ICE: Undefined field in field assign")
                            }
                            _ => panic!()
                        };
                        function.instructions.push(SetField(field_index));
                    }
                    Expr::ArrayAccess(ref expr, ref index) => {
                        self.compile(&**expr, function);
                        self.compile(&**index, function);
                        self.compile(&**rhs, function);
                        function.instructions.push(SetIndex);
                    }
                    _ => panic!("Assignment to {:?}", lhs)
                }
            }
            Expr::FieldAccess(ref expr, ref field) => {
                self.compile(&**expr, function);
                debug!("{:?} {:?}", expr, field);
                let field_index = match *expr.type_of() {
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
                self.compile(&**expr, function);
                let mut start_jumps = Vec::new();
                let mut end_jumps = Vec::new();
                let typename = match expr.type_of() {
                    &Type::Data(ref id, _) => id,
                    _ => panic!()
                };
                for alt in alts.iter() {
                    match alt.pattern {
                        ConstructorPattern(ref id, _) => {
                            let tag = self.find_tag(typename, id.id())
                                .unwrap_or_else(|| panic!("Could not find tag for {}::{}", typename, id.id()));
                            function.instructions.push(TestTag(tag));
                            start_jumps.push(function.instructions.len());
                            function.instructions.push(CJump(0));
                        }
                        _ => {
                            start_jumps.push(function.instructions.len());
                            function.instructions.push(Jump(0));
                        }
                    }
                }
                for (alt, &start_index) in alts.iter().zip(start_jumps.iter()) {
                    match alt.pattern {
                        ConstructorPattern(_, ref args) => {
                            function.instructions[start_index] = CJump(function.instructions.len() as VMIndex);
                            function.instructions.push(Split);
                            for arg in args.iter() {
                                self.new_stack_var(arg.id().clone());
                            }
                        }
                        IdentifierPattern(ref id) => {
                            function.instructions[start_index] = Jump(function.instructions.len() as VMIndex);
                            self.new_stack_var(id.id().clone());
                        }
                    }
                    self.compile(&alt.expression, function);
                    end_jumps.push(function.instructions.len());
                    function.instructions.push(Jump(0));

                    match alt.pattern {
                        ConstructorPattern(_, ref args) => {
                            for _ in 0..args.len() {
                                self.stack.pop();
                            }
                        }
                        IdentifierPattern(_) => { self.stack.pop(); }
                    }
                }
                for &index in end_jumps.iter() {
                    function.instructions[index] = Jump(function.instructions.len() as VMIndex);
                }
            }
            Expr::Array(ref a) => {
                for expr in a.expressions.iter() {
                    self.compile(expr, function);
                }
                function.instructions.push(Construct(0, a.expressions.len() as VMIndex));
            }
            Expr::ArrayAccess(ref array, ref index) => {
                self.compile(&**array, function);
                self.compile(&**index, function);
                function.instructions.push(GetIndex);
            }
            Expr::Lambda(ref lambda) => {
                let cf = self.compile_lambda(lambda, function);
                function.inner_functions.push(cf);
            }
            Expr::Type(_, _, ref expr) => self.compile(&**expr, function),
            Expr::Record(_, ref fields) => {
                for field in fields {
                    self.compile(&field.1, function);
                }
                function.instructions.push(Construct(0, fields.len() as u32));
            }
        }
    }

    fn compile_lambda(&mut self, lambda: &LambdaStruct<TcIdent>, parent: &mut FunctionEnv) -> CompiledFunction {
        self.closure_limits.push(self.stack.len() as VMIndex);
        for arg in lambda.arguments.iter() {
            self.new_stack_var(*arg.id());
        }
        let mut f = FunctionEnv::new();
        f.dictionary = parent.dictionary.clone();
        self.compile(&*lambda.body, &mut f);

        let previous_len = self.closure_limits.pop().expect("closure_limits: pop");
        while previous_len < self.stack_size() {
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
        parent.instructions.push(MakeClosure(function_index, f.free_vars.len() as VMIndex));
        let FunctionEnv { instructions, inner_functions, strings, .. } = f;
        CompiledFunction {
            id: lambda.id.id().clone(),
            typ: Constrained { constraints: Vec::new(), value: lambda.id.typ.clone() },
            instructions: instructions,
            inner_functions: inner_functions,
            strings: strings
        }
    }
}

