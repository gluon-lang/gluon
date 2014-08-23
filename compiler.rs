use std::collections::HashMap;
use interner::*;
use ast::{Module, LExpr, Identifier, Literal, While, IfElse, Block, FieldAccess, Match, Assign, Call, Let, BinOp, Array, ArrayAccess, Lambda, Integer, Float, String, Bool, ConstructorPattern, IdentifierPattern, Function};
use typecheck::*;

#[deriving(Show)]
pub enum Instruction {
    PushInt(int),
    PushFloat(f64),
    Push(uint),
    PushGlobal(uint),
    Store(uint),
    CallGlobal(uint),
    Construct(uint, uint),
    GetField(uint),
    SetField(uint),
    Split,
    TestTag(uint),
    Jump(uint),
    CJump(uint),
    Pop(uint),
    Slide(uint),

    //Creates a closure with 'n' upvariables
    //Pops the 'n' values on top of the stack and creates a closure
    MakeClosure(uint, uint),
    PushUpVar(uint),
    StoreUpVar(uint),

    ConstructTraitObject(uint),
    PushTraitFunction(uint),
    Unpack,

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
    Stack(uint),
    Global(uint),
    Constructor(uint, uint),
    TraitFunction(&'a TcType),
    UpVar(uint)
}

pub struct CompiledFunction {
    pub id: InternedStr,
    pub typ: Constrained<TcType>,
    pub instructions: Vec<Instruction>
}

#[deriving(PartialEq, Clone)]
pub struct TraitFunctions {
    //The where the first function of the implemented trait is at
    pub index: uint
}

pub struct FunctionEnv {
    pub instructions: Vec<Instruction>,
    pub free_vars: Vec<InternedStr>
}

impl FunctionEnv {
    pub fn new() -> FunctionEnv {
        FunctionEnv { instructions: Vec::new(), free_vars: Vec::new() }
    }
    fn upvar(&mut self, s: InternedStr) -> uint {
        match self.free_vars.iter().enumerate().find(|t| *t.val1() == s).map(|t| t.val0()) {
            Some(index) => index,
            None => {
                self.free_vars.push(s);
                self.free_vars.len() - 1
            }
        }
    }
}

pub trait CompilerEnv {
    fn find_var(&self, id: &InternedStr) -> Option<Variable>;
    fn find_field(&self, _struct: &InternedStr, _field: &InternedStr) -> Option<uint>;
    fn find_tag(&self, _: &InternedStr, _: &InternedStr) -> Option<uint>;
    fn find_trait_offset(&self, trait_name: &InternedStr, trait_type: &TcType) -> Option<uint>;
    fn find_trait_function(&self, typ: &TcType, id: &InternedStr) -> Option<uint>;
    fn find_object_function(&self, trait_type: &InternedStr, name: &InternedStr) -> Option<uint>;
    fn next_function_index(&self) -> uint;
}

impl <T: CompilerEnv, U: CompilerEnv> CompilerEnv for (T, U) {
    fn find_var(&self, s: &InternedStr) -> Option<Variable> {
        let &(ref outer, ref inner) = self;
        inner.find_var(s)
            .map(|var| match var {
                Global(i) => Global(i + outer.next_function_index()),
                var => var
            })
            .or_else(|| outer.find_var(s))
    }
    fn find_field(&self, struct_: &InternedStr, field: &InternedStr) -> Option<uint> {
        let &(ref outer, ref inner) = self;
        inner.find_field(struct_, field)
            .or_else(|| outer.find_field(struct_, field))
    }

    fn find_tag(&self, struct_: &InternedStr, field: &InternedStr) -> Option<uint> {
        let &(ref outer, ref inner) = self;
        inner.find_tag(struct_, field)
            .or_else(|| outer.find_tag(struct_, field))
    }
    fn find_trait_offset(&self, trait_name: &InternedStr, trait_type: &TcType) -> Option<uint> {
        let &(ref outer, ref inner) = self;
        inner.find_trait_offset(trait_name, trait_type)
            .map(|index| index + outer.next_function_index())
            .or_else(|| outer.find_trait_offset(trait_name, trait_type))
    }
    fn find_trait_function(&self, typ: &TcType, id: &InternedStr) -> Option<uint> {
        let &(ref outer, ref inner) = self;
        inner.find_trait_function(typ, id)
            .map(|index| index + outer.next_function_index())
            .or_else(|| outer.find_trait_function(typ, id))
    }
    fn find_object_function(&self, trait_type: &InternedStr, name: &InternedStr) -> Option<uint> {
        let &(ref outer, ref inner) = self;
        inner.find_object_function(trait_type, name)
            .or_else(|| outer.find_object_function(trait_type, name))
    }
    fn next_function_index(&self) -> uint {
        let &(ref outer, ref inner) = self;
        outer.next_function_index() + inner.next_function_index()
    }
}

impl CompilerEnv for Module<TcIdent> {
    fn find_var(&self, id: &InternedStr) -> Option<Variable> {
        self.functions.iter()
            .enumerate()
            .find(|&(_, f)| f.declaration.name.id() == id)
            .map(|(i, _)| Global(i))
            .or_else(|| self.structs.iter()
                .find(|s| s.name.id() == id)
                .map(|s| Constructor(0, s.fields.len()))
            )
            .or_else(|| {
                for e in self.enums.iter() {
                    let x = e.constructors.iter().enumerate()
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
    fn find_field(&self, struct_: &InternedStr, field: &InternedStr) -> Option<uint> {
        self.structs.iter()
            .find(|s| s.name.id() == struct_)
            .map(|s| s.fields.iter()
                .enumerate()
                .find(|&(_, f)| f.name == *field)
                .map(|(i, _)| i).unwrap())
    }
    fn find_tag(&self, enum_: &InternedStr, ctor_name: &InternedStr) -> Option<uint> {
        self.enums.iter()
            .find(|e| e.name.id() == enum_)
            .map(|e| e.constructors.iter()
                .enumerate()
                .find(|&(_, c)| c.name.id() == ctor_name)
                .map(|(i, _)| i).unwrap())
    }
    fn find_trait_offset(&self, trait_name: &InternedStr, trait_type: &TcType) -> Option<uint> {
        let mut offset = self.functions.len();
        self.impls.iter()
            .find(|imp| {
                offset += imp.functions.len();
                imp.trait_name.id() == trait_name && match_types(trait_type, &imp.typ)
            })
            .map(|imp| offset - imp.functions.len())
    }
    fn find_trait_function(&self, typ: &TcType, id: &InternedStr) -> Option<uint> {
        let mut offset = self.functions.len();
        for imp in self.impls.iter() {
            if match_types(&imp.typ, typ) {
                for (i, func) in imp.functions.iter().enumerate() {
                    if func.declaration.name.id() == id {
                        return Some(offset + i);
                    }
                }
            }
            offset += imp.functions.len();
        }
        None
    }
    fn find_object_function(&self, trait_type: &InternedStr, name: &InternedStr) -> Option<uint> {
        self.traits.iter()
            .find(|trait_| trait_.name.id() == trait_type)
            .and_then(|trait_| trait_.declarations.iter().enumerate()
                .find(|&(_, func)| func.name.id() == name)
                .map(|(i, _)| i)
            )
    }
    fn next_function_index(&self) -> uint {
        self.functions.len() + self.impls.iter().fold(0, |y, i| i.functions.len() + y)
    }
}

impl <'a, T: CompilerEnv> CompilerEnv for &'a T {
    fn find_var(&self, s: &InternedStr) -> Option<Variable> {
        (*self).find_var(s)
    }
    fn find_field(&self, struct_: &InternedStr, field: &InternedStr) -> Option<uint> {
        (*self).find_field(struct_, field)
    }

    fn find_tag(&self, enum_: &InternedStr, ctor_name: &InternedStr) -> Option<uint> {
        (*self).find_tag(enum_, ctor_name)
    }
    fn find_trait_offset(&self, trait_name: &InternedStr, trait_type: &TcType) -> Option<uint> {
        (*self).find_trait_offset(trait_name, trait_type)
    }
    fn find_trait_function(&self, typ: &TcType, id: &InternedStr) -> Option<uint> {
        (*self).find_trait_function(typ, id)
    }
    fn find_object_function(&self, trait_type: &InternedStr, name: &InternedStr) -> Option<uint> {
        (*self).find_object_function(trait_type, name)
    }
    fn next_function_index(&self) -> uint {
        (*self).next_function_index()
    }
}

pub struct Compiler<'a> {
    globals: &'a CompilerEnv,
    stack: HashMap<InternedStr, uint>,
    //Stack which holds indexes for where each closure starts its stack variables
    closure_limits: Vec<uint>,
    compiled_lambdas: Vec<CompiledFunction>
}

impl <'a> Compiler<'a> {

    pub fn new(globals: &'a CompilerEnv) -> Compiler<'a> {
        Compiler {
            globals: globals,
            stack: HashMap::new(),
            closure_limits: Vec::new(),
            compiled_lambdas: Vec::new()
        }
    }

    fn find(&self, s: &InternedStr, env: &mut FunctionEnv) -> Option<Variable> {
        self.stack.find(s)
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

    fn find_field(&self, struct_: &InternedStr, field: &InternedStr) -> Option<uint> {
        self.globals.find_field(struct_, field)
    }

    fn find_tag(&self, enum_: &InternedStr, constructor: &InternedStr) -> Option<uint> {
        self.globals.find_tag(enum_, constructor)
    }

    fn find_trait_function(&self, typ: &TcType, id: &InternedStr) -> Option<uint> {
        self.globals.find_trait_function(typ, id)
    }

    fn new_stack_var(&mut self, s: InternedStr) {
        let v = self.stack.len();
        if self.stack.find(&s).is_some() {
            fail!("Variable shadowing is not allowed")
        }
        self.stack.insert(s, v);
    }

    fn stack_size(&self) -> uint {
        self.stack.len()
    }

    pub fn compile_module(&mut self, module: &Module<TcIdent>) -> (Vec<CompiledFunction>, Vec<TraitFunctions>) {
        let mut functions: Vec<CompiledFunction> = module.functions.iter()
            .map(|f| self.compile_function(f))
            .collect();
        let mut trait_functions = Vec::new();
        let offset = self.globals.next_function_index();
        for imp in module.impls.iter() {
            trait_functions.push(TraitFunctions { index: offset + functions.len() });
            for f in imp.functions.iter() {
                functions.push(self.compile_function(f));
            }
        }
        let lambdas = ::std::mem::replace(&mut self.compiled_lambdas, Vec::new());
        functions.extend(lambdas.move_iter());


        (functions, trait_functions)
    }

    pub fn compile_function(&mut self, function: &Function<TcIdent>) -> CompiledFunction {
        for arg in function.declaration.arguments.iter() {
            self.new_stack_var(arg.name);
        }
        let mut f = FunctionEnv::new();
        self.compile(&function.expression, &mut f);
        for arg in function.declaration.arguments.iter() {
            self.stack.remove(&arg.name);
        }
        debug!("Stack {} {}", function.declaration.name.id(), self.stack);
        let FunctionEnv { instructions: instructions, .. } = f;
        let constraints = function.declaration.type_variables.iter()
            .map(|constraints| constraints.constraints.iter()
                .map(|typ| from_generic_type(function.declaration.type_variables.as_slice(), typ))
                .collect())
            .collect();
        CompiledFunction {
            id: function.declaration.name.id().clone(),
            typ: Constrained { constraints: constraints, value: function.type_of().clone() },
            instructions: instructions
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
                    Integer(i) => function.instructions.push(PushInt(i)),
                    Float(f) => function.instructions.push(PushFloat(f)),
                    Bool(b) => function.instructions.push(PushInt(if b { 1 } else { 0 })),
                    String(_) => fail!("String is not implemented")
                }
            }
            Identifier(ref id) => {
                match self.find(id.id(), function).unwrap_or_else(|| fail!("Undefined variable {}", id.id())) {
                    Stack(index) => function.instructions.push(Push(index)),
                    UpVar(index) => function.instructions.push(PushUpVar(index)),
                    Global(index) => function.instructions.push(PushGlobal(index)),
                    TraitFunction(typ) => self.compile_trait_function(typ, id, function),
                    Constructor(..) => fail!("Constructor {} is not fully applied", id)
                }
            }
            IfElse(ref pred, ref if_true, ref if_false) => {
                self.compile(&**pred, function);
                let jump_index = function.instructions.len();
                function.instructions.push(CJump(0));
                self.compile(&**if_false, function);
                let false_jump_index = function.instructions.len();
                function.instructions.push(Jump(0));
                *function.instructions.get_mut(jump_index) = CJump(function.instructions.len());
                self.compile(&**if_true, function);
                *function.instructions.get_mut(false_jump_index) = Jump(function.instructions.len());
            }
            Block(ref exprs) => {
                if exprs.len() != 0 {
                    for expr in exprs.slice_to(exprs.len() - 1).iter() {
                        self.compile(expr, function);
                        //Since this line is executed as a statement we need to remove
                        //the value from the stack if it exists
                        if *expr.type_of() != unit_type_tc {
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
                    if *expr.type_of() == unit_type_tc {
                        function.instructions.push(Pop(diff_size));
                    }
                    else {
                        function.instructions.push(Slide(diff_size));
                    }
                }
                
            }
            BinOp(ref lhs, ref op, ref rhs) => {
                self.compile(&**lhs, function);
                self.compile(&**rhs, function);
                let typ = lhs.type_of();
                let instr = if *typ == int_type_tc {
                    match op.as_slice() {
                        "+" => AddInt,
                        "-" => SubtractInt,
                        "*" => MultiplyInt,
                        "<" => IntLT,
                        "==" => IntEQ,
                        _ => fail!()
                    }
                }
                else if *typ == float_type_tc {
                    match op.as_slice() {
                        "+" => AddFloat,
                        "-" => SubtractFloat,
                        "*" => MultiplyFloat,
                        "<" => FloatLT,
                        "==" => FloatEQ,
                        _ => fail!()
                    }
                }
                else {
                    fail!("Unexpected type {} in expression {}", typ, op.id())
                };
                function.instructions.push(instr);
            }
            Let(ref id, ref expr) => {
                self.compile(&**expr, function);
                self.new_stack_var(*id.id());
                //unit expressions do not return a value so we need to add a dummy value
                //To make the stack correct
                if *expr.type_of() == unit_type_tc {
                    function.instructions.push(PushInt(0));
                }
            }
            Call(ref func, ref args) => {
                match func.value {
                    Identifier(ref id) => {
                        match self.find(id.id(), function).unwrap_or_else(|| fail!("Undefined variable {}", id.id())) {
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
                    _ => fail!("Non function type inferred in call")
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
                *function.instructions.get_mut(pre_jump_index) = Jump(function.instructions.len());
                self.compile(&**pred, function);
                function.instructions.push(CJump(pre_jump_index + 1));
            }
            Assign(ref lhs, ref rhs) => {
                match ***lhs {
                    Identifier(ref id) => {
                        self.compile(&**rhs, function);
                        let var = self.find(id.id(), function)
                            .unwrap_or_else(|| fail!("Undefined variable {}", id));
                        match var {
                            Stack(i) => function.instructions.push(Store(i)),
                            UpVar(i) => function.instructions.push(StoreUpVar(i)),
                            Global(_) => fail!("Assignment to global {}", id),
                            Constructor(..) => fail!("Assignment to constructor {}", id),
                            TraitFunction(..) => fail!("Assignment to trait function {}", id),
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
                            _ => fail!()
                        };
                        function.instructions.push(SetField(field_index));
                    }
                    ArrayAccess(ref expr, ref index) => {
                        self.compile(&**expr, function);
                        self.compile(&**index, function);
                        self.compile(&**rhs, function);
                        function.instructions.push(SetIndex);
                    }
                    _ => fail!("Assignment to {}", lhs)
                }
            }
            FieldAccess(ref expr, ref field) => {
                self.compile(&**expr, function);
                let field_index = match *expr.type_of() {
                    Type(ref id, _) => {
                        self.find_field(id, field.id())
                            .unwrap()
                    }
                    _ => fail!()
                };
                function.instructions.push(GetField(field_index));
            }
            Match(ref expr, ref alts) => {
                self.compile(&**expr, function);
                let mut start_jumps = Vec::new();
                let mut end_jumps = Vec::new();
                let typename = match expr.type_of() {
                    &Type(ref id, _) => id,
                    _ => fail!()
                };
                for alt in alts.iter() {
                    match alt.pattern {
                        ConstructorPattern(ref id, _) => {
                            let tag = self.find_tag(typename, id.id())
                                .unwrap_or_else(|| fail!("Could not find tag for {}::{}", typename, id.id()));
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
                            *function.instructions.get_mut(start_index) = CJump(function.instructions.len());
                            function.instructions.push(Split);
                            for arg in args.iter() {
                                self.new_stack_var(arg.id().clone());
                            }
                        }
                        IdentifierPattern(ref id) => {
                            *function.instructions.get_mut(start_index) = Jump(function.instructions.len());
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
                    *function.instructions.get_mut(index) = Jump(function.instructions.len());
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

    fn compile_lambda(&mut self, lambda: &Lambda<TcIdent>, function: &mut FunctionEnv) -> CompiledFunction {
        self.closure_limits.push(self.stack.len());
        for arg in lambda.arguments.iter() {
            self.new_stack_var(*arg.id());
        }
        let mut f = FunctionEnv::new();
        self.compile(&*lambda.body, &mut f);
        for arg in lambda.arguments.iter() {
            self.stack.remove(arg.id());
        }
        self.closure_limits.pop();
        //Insert all free variables into the above functions free variables
        //if they arent in that lambdas scope
        for var in f.free_vars.iter() {
            match self.find(var, function).unwrap() {
                Stack(index) => function.instructions.push(Push(index)),
                UpVar(index) => function.instructions.push(PushUpVar(index)),
                _ => fail!("Free variables can only be on the stack or another upvar")
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

    fn compile_trait_function(&self, trait_func_type: &TcType, id: &TcIdent, function: &mut FunctionEnv) {
        debug!("Find real {} <=> {}", trait_func_type, id.typ);
        let typ = find_real_type(trait_func_type, &id.typ)
            .unwrap_or_else(|| fail!("Could not find the real type between {} <=> {}", trait_func_type, id.typ));
        
        match *typ {
            TraitType(ref trait_name, _) => {//TODO parameterized traits
                    let index = self.globals.find_object_function(trait_name, id.id())
                        .expect("Trait object function does not exist");
                    function.instructions.push(PushTraitFunction(index));
                }
            _ => {
                debug!("Find trait function {} {}", typ, id.id());
                let index = self.find_trait_function(typ, id.id())
                    .expect("Trait function does not exist");
                function.instructions.push(PushGlobal(index));
            }
        }
    }
}

fn find_real_type<'a>(trait_func_type: &TcType, real_type: &'a TcType) -> Option<&'a TcType> {
    match (trait_func_type, real_type) {
        (&FunctionType(ref l_args, ref l_ret), &FunctionType(ref r_args, ref r_ret)) => {
            for (l, r) in l_args.iter().zip(r_args.iter()) {
                let x = find_real_type(l, r);
                if x.is_some() {
                    return x;
                }
            }
            find_real_type(&**l_ret, &**r_ret)
        }
        (&TypeVariable(_), real_type) => Some(real_type),
        (&Generic(_), real_type) => Some(real_type),
        _ => None
    }
}
