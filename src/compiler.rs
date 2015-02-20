use std::collections::HashMap;
use interner::*;
use ast;
use ast::{Module, LExpr, Identifier, Literal, While, IfElse, Block, FieldAccess, Match, Assign, Call, Let, BinOp, Array, ArrayAccess, Lambda, LambdaStruct, Integer, Float, String, Bool, ConstructorPattern, IdentifierPattern, Constraint};
use typecheck::*;
use self::Instruction::*;
use self::Variable::*;

#[derive(Debug)]
pub enum Instruction {
    PushInt(isize),
    PushFloat(f64),
    PushString(InternedStr),
    Push(usize),
    PushGlobal(usize),
    Store(usize),
    StoreGlobal(usize),
    CallGlobal(usize),
    Construct(usize, usize),
    GetField(usize),
    SetField(usize),
    Split,
    TestTag(usize),
    Jump(usize),
    CJump(usize),
    Pop(usize),
    Slide(usize),

    //Creates a closure with 'n' upvariables
    //Pops the 'n' values on top of the stack and creates a closure
    MakeClosure(usize, usize),
    PushUpVar(usize),
    StoreUpVar(usize),

    ConstructTraitObject(usize),
    PushTraitFunction(usize),
    Unpack,

    PushDictionaryMember(u32, u32),
    PushDictionary(usize),

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

impl Copy for Instruction { }

pub type CExpr = LExpr<TcIdent>;

pub enum Variable<'a> {
    Stack(usize),
    Global(usize, &'a [Constraint], &'a TcType),
    Constructor(usize, usize),
    TraitFunction(&'a TcType),
    UpVar(usize)
}

pub struct Assembly {
    pub initializer: Vec<Instruction>,
    pub globals: Vec<Binding>,
    pub anonymous_functions: Vec<CompiledFunction>,
    pub trait_functions: Vec<TraitFunctions>
}

#[derive(Debug)]
pub enum Binding {
    Function(InternedStr, Constrained<TcType>, usize),
    Other(InternedStr, Constrained<TcType>)
}

#[derive(Debug)]
pub struct CompiledFunction {
    pub id: InternedStr,
    pub typ: Constrained<TcType>,
    pub instructions: Vec<Instruction>
}

#[derive(PartialEq, Clone)]
pub struct TraitFunctions {
    //The where the first function of the implemented trait is at
    pub index: usize,
    pub trait_name: InternedStr,
    pub impl_type: TcType
}

pub struct FunctionEnv<'a> {
    pub instructions: Vec<Instruction>,
    pub free_vars: Vec<InternedStr>,
    pub dictionary: &'a [Constraint]//Typevariable -> Trait
}

impl <'a> FunctionEnv<'a> {
    pub fn new() -> FunctionEnv<'a> {
        FunctionEnv { instructions: Vec::new(), free_vars: Vec::new(), dictionary: &[] }
    }
    fn upvar(&mut self, s: InternedStr) -> usize {
        match self.free_vars.iter().enumerate().find(|t| *t.1 == s).map(|t| t.0) {
            Some(index) => index,
            None => {
                self.free_vars.push(s);
                self.free_vars.len() - 1
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
    fn find_field(&self, _struct: &InternedStr, _field: &InternedStr) -> Option<usize>;
    fn find_tag(&self, _: &InternedStr, _: &InternedStr) -> Option<usize>;
    fn find_trait_offset(&self, trait_name: &InternedStr, trait_type: &TcType) -> Option<usize>;
    fn find_trait_function(&self, typ: &TcType, id: &InternedStr) -> Option<TypeResult<usize>>;
    fn find_object_function(&self, trait_type: &InternedStr, name: &InternedStr) -> Option<usize>;
    fn next_function_index(&self) -> usize;
}

impl <T: CompilerEnv, U: CompilerEnv> CompilerEnv for (T, U) {
    fn find_var(&self, s: &InternedStr) -> Option<Variable> {
        let &(ref outer, ref inner) = self;
        inner.find_var(s)
            .map(|var| match var {
                Global(i, x, y) => Global(i + outer.next_function_index(), x, y),
                var => var
            })
            .or_else(|| outer.find_var(s))
    }
    fn find_field(&self, struct_: &InternedStr, field: &InternedStr) -> Option<usize> {
        let &(ref outer, ref inner) = self;
        inner.find_field(struct_, field)
            .or_else(|| outer.find_field(struct_, field))
    }

    fn find_tag(&self, struct_: &InternedStr, field: &InternedStr) -> Option<usize> {
        let &(ref outer, ref inner) = self;
        inner.find_tag(struct_, field)
            .or_else(|| outer.find_tag(struct_, field))
    }
    fn find_trait_offset(&self, trait_name: &InternedStr, trait_type: &TcType) -> Option<usize> {
        let &(ref outer, ref inner) = self;
        inner.find_trait_offset(trait_name, trait_type)
            .map(|index| index + outer.next_function_index())
            .or_else(|| outer.find_trait_offset(trait_name, trait_type))
    }
    fn find_trait_function(&self, typ: &TcType, id: &InternedStr) -> Option<TypeResult<usize>> {
        let &(ref outer, ref inner) = self;
        inner.find_trait_function(typ, id)
            .map(|mut result| {
                result.value += outer.next_function_index();
                result
            })
            .or_else(|| outer.find_trait_function(typ, id))
    }
    fn find_object_function(&self, trait_type: &InternedStr, name: &InternedStr) -> Option<usize> {
        let &(ref outer, ref inner) = self;
        inner.find_object_function(trait_type, name)
            .or_else(|| outer.find_object_function(trait_type, name))
    }
    fn next_function_index(&self) -> usize {
        let &(ref outer, ref inner) = self;
        outer.next_function_index() + inner.next_function_index()
    }
}

impl CompilerEnv for Module<TcIdent> {
    fn find_var(&self, id: &InternedStr) -> Option<Variable> {
        self.globals.iter()
            .enumerate()
            .find(|&(_, f)| f.declaration.name.id() == id)
            .map(|(i, f)| Global(i, f.declaration.constraints.as_slice(), &f.declaration.name.typ))
            .or_else(|| {
                for d in self.datas.iter() {
                    let x = d.constructors.iter().enumerate()
                        .find(|&(_, ctor)| ctor.name.id() == id)
                        .map(|(i, ctor)| Constructor(i, ctor.arguments.len()));
                    if x.is_some() {
                        return x
                    }
                }
                None
            })
            .or_else(|| {
                self.traits.iter()
                    .flat_map(|trait_| trait_.declarations.iter())
                    .find(|decl| decl.name.id() == id)
                    .map(|decl| TraitFunction(&decl.name.typ))
            })
    }
    fn find_field(&self, data_name: &InternedStr, field: &InternedStr) -> Option<usize> {
        self.datas.iter()
            .find(|d| d.name.id() == data_name)
            .and_then(|d| match &*d.constructors {
                [ast::Constructor { arguments: ast::ConstructorType::Record(ref fields), .. }] => {
                    fields.iter()
                        .enumerate()
                        .find(|&(_, f)| f.name == *field)
                        .map(|(i, _)| i)
                }
                _ => None
            })
    }
    fn find_tag(&self, enum_: &InternedStr, ctor_name: &InternedStr) -> Option<usize> {
        self.datas.iter()
            .find(|e| e.name.id() == enum_)
            .map(|e| e.constructors.iter()
                .enumerate()
                .find(|&(_, c)| c.name.id() == ctor_name)
                .map(|(i, _)| i).unwrap())
    }
    fn find_trait_offset(&self, trait_name: &InternedStr, trait_type: &TcType) -> Option<usize> {
        let mut offset = self.globals.len();
        self.impls.iter()
            .find(|imp| {
                offset += imp.globals.len();
                imp.trait_name.id() == trait_name && match_types(&imp.typ, trait_type)
            })
            .map(|imp| offset - imp.globals.len())
    }
    fn find_trait_function(&self, typ: &TcType, id: &InternedStr) -> Option<TypeResult<usize>> {
        let mut offset = self.globals.len();
        for imp in self.impls.iter() {
            if match_types(&imp.typ, typ) {
                for (i, func) in imp.globals.iter().enumerate() {
                    if func.declaration.name.id() == id {
                        return Some(TypeResult {
                            constraints: func.declaration.constraints.as_slice(),
                            typ: func.type_of(),
                            value: offset + i
                        });
                    }
                }
            }
            offset += imp.globals.len();
        }
        None
    }
    fn find_object_function(&self, trait_type: &InternedStr, name: &InternedStr) -> Option<usize> {
        self.traits.iter()
            .find(|trait_| trait_.name.id() == trait_type)
            .and_then(|trait_| trait_.declarations.iter().enumerate()
                .find(|&(_, func)| func.name.id() == name)
                .map(|(i, _)| i)
            )
    }
    fn next_function_index(&self) -> usize {
        self.globals.len() + self.impls.iter().fold(0, |y, i| i.globals.len() + y)
    }
}

impl <'a, T: CompilerEnv> CompilerEnv for &'a T {
    fn find_var(&self, s: &InternedStr) -> Option<Variable> {
        (*self).find_var(s)
    }
    fn find_field(&self, struct_: &InternedStr, field: &InternedStr) -> Option<usize> {
        (*self).find_field(struct_, field)
    }

    fn find_tag(&self, enum_: &InternedStr, ctor_name: &InternedStr) -> Option<usize> {
        (*self).find_tag(enum_, ctor_name)
    }
    fn find_trait_offset(&self, trait_name: &InternedStr, trait_type: &TcType) -> Option<usize> {
        (*self).find_trait_offset(trait_name, trait_type)
    }
    fn find_trait_function(&self, typ: &TcType, id: &InternedStr) -> Option<TypeResult<usize>> {
        (*self).find_trait_function(typ, id)
    }
    fn find_object_function(&self, trait_type: &InternedStr, name: &InternedStr) -> Option<usize> {
        (*self).find_object_function(trait_type, name)
    }
    fn next_function_index(&self) -> usize {
        (*self).next_function_index()
    }
}

pub struct Compiler<'a> {
    globals: &'a (CompilerEnv + 'a),
    stack: HashMap<InternedStr, usize>,
    //Stack which holds indexes for where each closure starts its stack variables
    closure_limits: Vec<usize>,
    compiled_lambdas: Vec<CompiledFunction>,
}

impl <'a> Compiler<'a> {

    pub fn new(globals: &'a CompilerEnv) -> Compiler<'a> {
        Compiler {
            globals: globals,
            stack: HashMap::new(),
            closure_limits: Vec::new(),
            compiled_lambdas: Vec::new(),
        }
    }

    fn find(&self, s: &InternedStr, env: &mut FunctionEnv) -> Option<Variable> {
        self.stack.get(s)
            .map(|x| {
                if self.closure_limits.len() != 0 {
                    let closure_stack_start = *self.closure_limits.last().unwrap();
                    if *x < closure_stack_start {
                        let i = env.upvar(*s);
                        UpVar(i)
                    }
                    else {
                        Stack(*x - closure_stack_start)
                    }
                }
                else {
                    Stack(*x)
                }
            })
            .or_else(||  self.globals.find_var(s))
    }

    fn find_field(&self, struct_: &InternedStr, field: &InternedStr) -> Option<usize> {
        self.globals.find_field(struct_, field)
    }

    fn find_tag(&self, enum_: &InternedStr, constructor: &InternedStr) -> Option<usize> {
        self.globals.find_tag(enum_, constructor)
    }

    fn find_trait_function(&self, typ: &TcType, id: &InternedStr) -> Option<TypeResult<usize>> {
        self.globals.find_trait_function(typ, id)
    }

    fn new_stack_var(&mut self, s: InternedStr) {
        let v = self.stack.len();
        if self.stack.get(&s).is_some() {
            panic!("Variable shadowing is not allowed")
        }
        self.stack.insert(s, v);
    }

    fn stack_size(&self) -> usize {
        self.stack.len()
    }

    pub fn compile_module(&mut self, module: &Module<TcIdent>) -> Assembly {
        let mut initializer = FunctionEnv::new();
        let mut globals = Vec::new();
        for global in module.globals.iter() {
            let index = globals.len();
            globals.push(self.compile_global(&mut initializer, index, global));
        }
        let mut trait_globals = Vec::new();
        let offset = self.globals.next_function_index() - module.next_function_index();
        for imp in module.impls.iter() {
            trait_globals.push(TraitFunctions {
                index: offset + globals.len(),
                trait_name: imp.trait_name.id().clone(),
                impl_type: imp.typ.clone()
            });
            for f in imp.globals.iter() {
                let index = globals.len();
                globals.push(self.compile_global(&mut initializer, index, f));
            }
        }
        let lambdas = ::std::mem::replace(&mut self.compiled_lambdas, Vec::new());

        Assembly {
            initializer: initializer.instructions,
            anonymous_functions: lambdas,
            globals: globals,
            trait_functions: trait_globals
        }
    }

    pub fn compile_global<'b>(&mut self, initializer: &mut FunctionEnv<'b>, index: usize, function: &'b ast::Global<TcIdent>) -> Binding {
        debug!("-- Compiling {}", function.declaration.name.id());
        initializer.dictionary = function.declaration.constraints.as_slice();
        self.compile(&function.expression, initializer);
        initializer.instructions.push(StoreGlobal(index));
        let name = function.declaration.name.name;
        let typ = Constrained {
            constraints: function.declaration.constraints.clone(),
            value: function.declaration.typ.clone()
        };
        if let Lambda(_) = function.expression.value {
            Binding::Function(name, typ, self.compiled_lambdas.len() - 1)
        }
        else {
            Binding::Other(name, typ)
        }
    }
    pub fn compile_function(&mut self, f: &mut FunctionEnv, lambda: &ast::LambdaStruct<TcIdent>) {
        for arg in lambda.arguments.iter() {
            self.new_stack_var(*arg.id());
        }
        self.compile(&lambda.body, f);
        for arg in lambda.arguments.iter() {
            self.stack.remove(arg.id());
        }
    }

    pub fn compile_expr(&mut self, expr: &CExpr) -> (Vec<Instruction>, Vec<CompiledFunction>) {
        let mut env = FunctionEnv::new();
        self.compile(expr, &mut env);
        let lambdas = ::std::mem::replace(&mut self.compiled_lambdas, Vec::new());
        (env.instructions, lambdas)
    }

    fn compile(&mut self, expr: &CExpr, function: &mut FunctionEnv) {
        match expr.value {
            Literal(ref lit) => {
                match *lit {
                    Integer(i) => function.instructions.push(PushInt(i as isize)),
                    Float(f) => function.instructions.push(PushFloat(f)),
                    Bool(b) => function.instructions.push(PushInt(if b { 1 } else { 0 })),
                    String(s) => function.instructions.push(PushString(s))
                }
            }
            Identifier(ref id) => {
                match self.find(id.id(), function).unwrap_or_else(|| panic!("Undefined variable {}", id.id())) {
                    Stack(index) => function.instructions.push(Push(index)),
                    UpVar(index) => function.instructions.push(PushUpVar(index)),
                    Global(index, constraints, typ) => {
                        if constraints.len() != 0 {
                            debug!("Compile dictionary for {}", id.id());
                            self.compile_dictionary(constraints, typ, expr.type_of(), function);
                            function.instructions.push(MakeClosure(index, 1));
                        }
                        else {
                            function.instructions.push(PushGlobal(index));
                        }
                    }
                    TraitFunction(typ) => self.compile_trait_function(typ, id, function),
                    Constructor(..) => panic!("Constructor {:?} is not fully applied", id)
                }
            }
            IfElse(ref pred, ref if_true, ref if_false) => {
                self.compile(&**pred, function);
                let jump_index = function.instructions.len();
                function.instructions.push(CJump(0));
                match *if_false {
                    Some(ref if_false) => self.compile(&**if_false, function),
                    None => ()
                }
                let false_jump_index = function.instructions.len();
                function.instructions.push(Jump(0));
                function.instructions[jump_index] = CJump(function.instructions.len());
                self.compile(&**if_true, function);
                function.instructions[false_jump_index] = Jump(function.instructions.len());
            }
            Block(ref exprs) => {
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
                let stack_size = self.stack_size();
                for expr in exprs.iter() {
                    match expr.value {
                        Let(ref id, _) => {
                            self.stack.remove(id.id());
                        }
                        _ => ()
                    }
                }
                //If the stack has changed size during the block we need to adjust
                //it back to its initial size
                let diff_size = stack_size - self.stack_size();
                if diff_size != 0 {
                    if *expr.type_of() == UNIT_TYPE {
                        function.instructions.push(Pop(diff_size));
                    }
                    else {
                        function.instructions.push(Slide(diff_size));
                    }
                }
                
            }
            BinOp(ref lhs, ref op, ref rhs) => {
                if op.as_slice() == "&&" {
                    self.compile(&**lhs, function);
                    let lhs_end = function.instructions.len();
                    function.instructions.push(CJump(lhs_end + 3));//Jump to rhs evaluation
                    function.instructions.push(PushInt(0));
                    function.instructions.push(Jump(0));//lhs false, jump to after rhs
                    self.compile(&**rhs, function);
                    function.instructions[lhs_end + 2] = Jump(function.instructions.len());//replace jump instruction
                }
                else if op.as_slice() == "||" {
                    self.compile(&**lhs, function);
                    let lhs_end = function.instructions.len();
                    function.instructions.push(CJump(0));
                    self.compile(&**rhs, function);
                    function.instructions.push(Jump(0));
                    function.instructions[lhs_end] = CJump(function.instructions.len());
                    function.instructions.push(PushInt(1));
                    let end = function.instructions.len();
                    function.instructions[end - 2] = Jump(end);
                }
                else {
                    self.compile(&**lhs, function);
                    self.compile(&**rhs, function);
                    let typ = lhs.type_of();
                    let instr = if *typ == INT_TYPE {
                        match op.as_slice() {
                            "+" => AddInt,
                            "-" => SubtractInt,
                            "*" => MultiplyInt,
                            "<" => IntLT,
                            "==" => IntEQ,
                            _ => panic!()
                        }
                    }
                    else if *typ == FLOAT_TYPE {
                        match op.as_slice() {
                            "+" => AddFloat,
                            "-" => SubtractFloat,
                            "*" => MultiplyFloat,
                            "<" => FloatLT,
                            "==" => FloatEQ,
                            _ => panic!()
                        }
                    }
                    else {
                        panic!("Unexpected type {:?} in expression {}", typ, op.id())
                    };
                    function.instructions.push(instr);
                }
            }
            Let(ref id, ref expr) => {
                self.compile(&**expr, function);
                self.new_stack_var(*id.id());
                //unit expressions do not return a value so we need to add a dummy value
                //To make the stack correct
                if *expr.type_of() == UNIT_TYPE {
                    function.instructions.push(PushInt(0));
                }
            }
            Call(ref func, ref args) => {
                match func.value {
                    Identifier(ref id) => {
                        match self.find(id.id(), function).unwrap_or_else(|| panic!("Undefined variable {}", id.id())) {
                            Constructor(tag, num_args) => {
                                for arg in args.iter() {
                                    self.compile(arg, function);
                                }
                                function.instructions.push(Construct(tag, num_args));
                                return
                            }
                            _ => ()
                        }
                    }
                    _ => ()
                }
                self.compile(&**func, function);
                let arg_types = match *func.type_of() {
                    FunctionType(ref args, _) => args.as_slice(),
                    _ => panic!("Non function type inferred in call")
                };
                let is_trait_func = match func.value {
                    Identifier(ref func_id) => {
                        self.find(func_id.id(), function).map(|x| {
                            match x {
                                TraitFunction(_) => true,
                                _ => false
                            }
                        })
                    }
                    _ => None
                }.unwrap_or(false);
                for (arg, real_arg_type) in args.iter().zip(arg_types.iter()) {
                    self.compile(arg, function);
                    match (arg.type_of(), real_arg_type, is_trait_func) {
                        (&TraitType(..), &TraitType(..), true) => {
                            //Call through a trait object
                            //Need to unpack the trait object for this argument
                            function.instructions.push(Unpack);
                        }
                        (actual, &TraitType(ref id, _), _) => {
                            let offset = self.globals.find_trait_offset(id, actual)
                                .expect("Missing trait");
                            function.instructions.push(ConstructTraitObject(offset));
                        }
                        _ => ()
                    }
                }
                function.instructions.push(CallGlobal(args.len()));
            }
            While(ref pred, ref expr) => {
                //jump #test
                //#start:
                //[compile(expr)]
                //#test:
                //[compile(pred)]
                //cjump #start
                let pre_jump_index = function.instructions.len();
                function.instructions.push(Jump(0));
                self.compile(&**expr, function);
                function.instructions[pre_jump_index] = Jump(function.instructions.len());
                self.compile(&**pred, function);
                function.instructions.push(CJump(pre_jump_index + 1));
            }
            Assign(ref lhs, ref rhs) => {
                match ***lhs {
                    Identifier(ref id) => {
                        self.compile(&**rhs, function);
                        let var = self.find(id.id(), function)
                            .unwrap_or_else(|| panic!("Undefined variable {:?}", id));
                        match var {
                            Stack(i) => function.instructions.push(Store(i)),
                            UpVar(i) => function.instructions.push(StoreUpVar(i)),
                            Global(..) => panic!("Assignment to global {:?}", id),
                            Constructor(..) => panic!("Assignment to constructor {:?}", id),
                            TraitFunction(..) => panic!("Assignment to trait function {:?}", id),
                        }
                    }
                    FieldAccess(ref expr, ref field) => {
                        self.compile(&**expr, function);
                        self.compile(&**rhs, function);
                        let field_index = match *expr.type_of() {
                            Type(ref id, _) => {
                                self.find_field(id, field.id())
                                    .unwrap()
                            }
                            _ => panic!()
                        };
                        function.instructions.push(SetField(field_index));
                    }
                    ArrayAccess(ref expr, ref index) => {
                        self.compile(&**expr, function);
                        self.compile(&**index, function);
                        self.compile(&**rhs, function);
                        function.instructions.push(SetIndex);
                    }
                    _ => panic!("Assignment to {:?}", lhs)
                }
            }
            FieldAccess(ref expr, ref field) => {
                self.compile(&**expr, function);
                let field_index = match *expr.type_of() {
                    Type(ref id, _) => {
                        self.find_field(id, field.id())
                            .unwrap()
                    }
                    _ => panic!()
                };
                function.instructions.push(GetField(field_index));
            }
            Match(ref expr, ref alts) => {
                self.compile(&**expr, function);
                let mut start_jumps = Vec::new();
                let mut end_jumps = Vec::new();
                let typename = match expr.type_of() {
                    &Type(ref id, _) => id,
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
                            function.instructions[start_index] = CJump(function.instructions.len());
                            function.instructions.push(Split);
                            for arg in args.iter() {
                                self.new_stack_var(arg.id().clone());
                            }
                        }
                        IdentifierPattern(ref id) => {
                            function.instructions[start_index] = Jump(function.instructions.len());
                            self.new_stack_var(id.id().clone());
                        }
                    }
                    self.compile(&alt.expression, function);
                    end_jumps.push(function.instructions.len());
                    function.instructions.push(Jump(0));

                    match alt.pattern {
                        ConstructorPattern(_, ref args) => {
                            for arg in args.iter() {
                                self.stack.remove(arg.id());
                            }
                        }
                        IdentifierPattern(ref id) => { self.stack.remove(id.id()); }
                    }
                }
                for &index in end_jumps.iter() {
                    function.instructions[index] = Jump(function.instructions.len());
                }
            }
            Array(ref a) => {
                for expr in a.expressions.iter() {
                    self.compile(expr, function);
                }
                function.instructions.push(Construct(0, a.expressions.len()));
            }
            ArrayAccess(ref array, ref index) => {
                self.compile(&**array, function);
                self.compile(&**index, function);
                function.instructions.push(GetIndex);
            }
            Lambda(ref lambda) => {
                let cf = self.compile_lambda(lambda, function);
                self.compiled_lambdas.push(cf);
            }
        }
    }

    fn compile_lambda(&mut self, lambda: &LambdaStruct<TcIdent>, function: &mut FunctionEnv) -> CompiledFunction {
        self.closure_limits.push(self.stack.len());
        for arg in lambda.arguments.iter() {
            self.new_stack_var(*arg.id());
        }
        let mut f = FunctionEnv::new();
        f.dictionary = function.dictionary.clone();
        self.compile(&*lambda.body, &mut f);
        for arg in lambda.arguments.iter() {
            self.stack.remove(arg.id());
        }
        self.closure_limits.pop();
        //Insert all free variables into the above globals free variables
        //if they arent in that lambdas scope
        for var in f.free_vars.iter() {
            match self.find(var, function).unwrap() {
                Stack(index) => function.instructions.push(Push(index)),
                UpVar(index) => function.instructions.push(PushUpVar(index)),
                _ => panic!("Free variables can only be on the stack or another upvar")
            }
        }
        let function_index = self.compiled_lambdas.len() + self.globals.next_function_index();
        function.instructions.push(MakeClosure(function_index,f.free_vars.len()));
        CompiledFunction {
            id: lambda.id.id().clone(),
            typ: Constrained { constraints: Vec::new(), value: lambda.id.typ.clone() },
            instructions: f.instructions
        }
    }

    fn compile_dictionary(&self
                        , constraints: &[Constraint]
                        , function_type: &TcType
                        , expr_type: &TcType
                        , function: &mut FunctionEnv) {
        debug!("Find type for dictionary {:?} <=> {:?}", function_type, expr_type);
        let real_types = find_real_type(function_type, expr_type);
        let mut dict_size = 0;
        for (i, constraint) in constraints.iter().enumerate() {
            let real_type = real_types[constraint.type_variable];
            dict_size += self.add_dictionary(i, constraint, real_type, function);
        }
        function.instructions.push(Construct(0, dict_size));
    }

    fn add_dictionary(&self, i: usize, constraint: &Constraint, real_type: &TcType, function: &mut FunctionEnv) -> usize {
        match real_type {
            &TypeVariable(_) => {
                debug!("In dict");
                //Load dictionary from stack
                //TODO actually look for what part of the dictionary that is needed
                function.instructions.push(PushDictionary(i));
            }
            real_type => {
                debug!("Found {:?} for {:?}", real_type, constraint);
                let impl_index = self.globals.find_trait_offset(&constraint.name, real_type)
                    .unwrap_or_else(|| panic!("ICE"));
                function.instructions.push(PushGlobal(impl_index));
            }
        }
        1
    }

    fn compile_trait_function(&self, trait_func_type: &TcType, id: &TcIdent, function: &mut FunctionEnv) {
        debug!("Find real {:?} <=> {:?}", trait_func_type, id.typ);
        let types = find_real_type(trait_func_type, &id.typ);
        let types: Vec<_> = types.into_iter().map(|tup| Some(tup.1)).collect();//TODO
        assert!(types.len() != 0);
        match types[0] {
            Some(&TraitType(ref trait_name, _)) => {//TODO parameterized traits
                    let index = self.globals.find_object_function(trait_name, id.id())
                        .expect("Trait object function does not exist");
                    function.instructions.push(PushTraitFunction(index));
                }
            Some(t0) => {
                debug!("Find trait function {:?} {:?}", types, id.id());
                match self.find_trait_function(t0, id.id()) {
                    Some(result) => {//Found a match
                        if result.constraints.len() != 0 {
                            self.compile_dictionary(result.constraints, result.typ, &id.typ, function);
                            function.instructions.push(MakeClosure(result.value, 1));
                        }
                        else {
                            debug!("PUSH {:?}", result);
                            function.instructions.push(PushGlobal(result.value));
                        }
                    }
                    None => {//Function must be in the dictionary
                        match types[0] {
                            Some(&TypeVariable(var_index)) if (var_index as usize - 1) < function.dictionary.len() => {
                                let constraint = &function.dictionary[var_index as usize - 1];
                                let func_index = self.globals.find_object_function(&constraint.name, id.id());
                                match func_index {
                                    Some(index) => {
                                        function.instructions.push(PushDictionaryMember(var_index - 1, index as u32));
                                        return
                                    }
                                    None => ()
                                }
                                panic!("{:?}   {:?}\n{:?}   {:?}", trait_func_type, id, function.dictionary, types)
                            }
                            x => panic!("ICE {:?} {:?}", x, function.dictionary)
                        }
                    }
                }
            }
            _ => panic!()
        }
    }
}

fn find_real_type<'a>(trait_func_type: &TcType, real_type: &'a TcType) -> HashMap<InternedStr, &'a TcType> {
    let mut result = HashMap::new();
    find_real_type_(trait_func_type, real_type, &mut result);
    result
}
fn find_real_type_<'a>(trait_func_type: &TcType, real_type: &'a TcType, out: &mut HashMap<InternedStr, &'a TcType>) {
    match (trait_func_type, real_type) {
        (&FunctionType(ref l_args, ref l_ret), &FunctionType(ref r_args, ref r_ret)) => {
            for (l, r) in l_args.iter().zip(r_args.iter()) {
                find_real_type_(l, r, out);
            }
            find_real_type_(&**l_ret, &**r_ret, out)
        }
        (&TypeVariable(_), _) => {
            panic!()
        }
        (&Generic(i), real_type) => {
            out.insert(i, real_type);
        }
        (&ArrayType(ref l), &ArrayType(ref r)) => find_real_type_(&**l, &**r, out),
        (&Type(_, ref l_args), &Type(_, ref r_args)) => {
            for (l, r) in l_args.iter().zip(r_args.iter()) {
                find_real_type_(l, r, out);
            }
        }
        (&TraitType(_, ref l_args), &TraitType(_, ref r_args)) => {
            for (l, r) in l_args.iter().zip(r_args.iter()) {
                find_real_type_(l, r, out);
            }
        }
        _ => ()
    }
}
