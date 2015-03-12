use std::collections::HashMap;
use interner::*;
use ast;
use ast::{Module, LExpr, Identifier, Literal, While, IfElse, Block, FieldAccess, Match, Assign, Call, Let, BinOp, Array, ArrayAccess, Lambda, LambdaStruct, Integer, Float, String, Bool, ConstructorPattern, IdentifierPattern, Constraint, Constrained};
use typecheck::*;
use self::Instruction::*;
use self::Variable::*;

pub type VMIndex = u32;
pub type VMTag = u32;

#[derive(Copy, Debug)]
pub enum Instruction {
    PushInt(isize),
    PushFloat(f64),
    PushString(VMIndex),
    Push(VMIndex),
    PushGlobal(VMIndex),
    Store(VMIndex),
    StoreGlobal(VMIndex),
    CallGlobal(VMIndex),
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

    ConstructTraitObject(VMIndex),
    PushTraitFunction(VMIndex),
    Unpack,

    PushDictionaryMember(VMIndex, VMIndex),
    PushDictionary(VMIndex),

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
    Global(VMIndex, &'a [Constraint], &'a TcType),
    Constructor(VMTag, VMIndex),
    TraitFunction(&'a TcType),
    UpVar(VMIndex)
}

pub struct Assembly {
    pub initializer: Vec<Instruction>,
    pub globals: Vec<Binding>,
    pub anonymous_functions: Vec<CompiledFunction>,
    pub trait_functions: Vec<TraitFunctions>
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

#[derive(PartialEq, Clone)]
pub struct TraitFunctions {
    //The where the first function of the implemented trait is at
    pub index: VMIndex,
    pub trait_name: InternedStr,
    pub impl_type: TcType
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
    fn find_trait_offset(&self, trait_name: &InternedStr, trait_type: &TcType) -> Option<VMIndex>;
    fn find_trait_function(&self, typ: &TcType, id: &InternedStr) -> Option<TypeResult<VMIndex>>;
    fn find_object_function(&self, trait_type: &InternedStr, name: &InternedStr) -> Option<VMIndex>;
    fn next_global_index(&self) -> VMIndex;
}

impl <T: CompilerEnv, U: CompilerEnv> CompilerEnv for (T, U) {
    fn find_var(&self, s: &InternedStr) -> Option<Variable> {
        let &(ref outer, ref inner) = self;
        inner.find_var(s)
            .map(|var| match var {
                Global(i, x, y) => Global(i + outer.next_global_index(), x, y),
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
    fn find_trait_offset(&self, trait_name: &InternedStr, trait_type: &TcType) -> Option<VMIndex> {
        let &(ref outer, ref inner) = self;
        inner.find_trait_offset(trait_name, trait_type)
            .map(|index| index + outer.next_global_index())
            .or_else(|| outer.find_trait_offset(trait_name, trait_type))
    }
    fn find_trait_function(&self, typ: &TcType, id: &InternedStr) -> Option<TypeResult<VMIndex>> {
        let &(ref outer, ref inner) = self;
        inner.find_trait_function(typ, id)
            .map(|mut result| {
                result.value += outer.next_global_index();
                result
            })
            .or_else(|| outer.find_trait_function(typ, id))
    }
    fn find_object_function(&self, trait_type: &InternedStr, name: &InternedStr) -> Option<VMIndex> {
        let &(ref outer, ref inner) = self;
        inner.find_object_function(trait_type, name)
            .or_else(|| outer.find_object_function(trait_type, name))
    }
    fn next_global_index(&self) -> VMIndex {
        let &(ref outer, ref inner) = self;
        outer.next_global_index() + inner.next_global_index()
    }
}

impl CompilerEnv for Module<TcIdent> {
    fn find_var(&self, id: &InternedStr) -> Option<Variable> {
        (0..).zip(self.globals.iter())
            .find(|&(_, f)| f.declaration.name.id() == id)
            .map(|(i, f)| Global(i, f.declaration.typ.constraints.as_slice(), &f.declaration.name.typ))
            .or_else(|| {
                for d in self.datas.iter() {
                    let x = (0..).zip(d.constructors.iter())
                        .find(|&(_, ctor)| ctor.name.id() == id)
                        .map(|(i, ctor)| Constructor(i, ctor.arguments.len() as VMIndex));
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
    fn find_field(&self, data_name: &InternedStr, field: &InternedStr) -> Option<VMIndex> {
        self.datas.iter()
            .find(|d| d.name.id() == data_name)
            .and_then(|d| match &*d.constructors {
                [ast::Constructor { arguments: ast::ConstructorType::Record(ref fields), .. }] => {
                    (0..).zip(fields.iter())
                        .find(|&(_, f)| f.name == *field)
                        .map(|(i, _)| i)
                }
                _ => None
            })
    }
    fn find_tag(&self, enum_: &InternedStr, ctor_name: &InternedStr) -> Option<VMTag> {
        self.datas.iter()
            .find(|e| e.name.id() == enum_)
            .map(|e| (0..).zip(e.constructors.iter())
                .find(|&(_, c)| c.name.id() == ctor_name)
                .map(|(i, _)| i).unwrap())
    }
    fn find_trait_offset(&self, trait_name: &InternedStr, trait_type: &TcType) -> Option<VMIndex> {
        let mut offset = self.globals.len();
        self.impls.iter()
            .find(|imp| {
                offset += imp.globals.len();
                imp.trait_name.id() == trait_name && match_types(&imp.typ, trait_type)
            })
            .map(|imp| (offset - imp.globals.len()) as VMIndex)
    }
    fn find_trait_function(&self, typ: &TcType, id: &InternedStr) -> Option<TypeResult<VMIndex>> {
        let mut offset = self.globals.len() as VMIndex;
        for imp in self.impls.iter() {
            if match_types(&imp.typ, typ) {
                for (i, func) in (0..).zip(imp.globals.iter()) {
                    if func.declaration.name.id() == id {
                        return Some(TypeResult {
                            constraints: func.declaration.typ.constraints.as_slice(),
                            typ: func.type_of(),
                            value: offset + i
                        });
                    }
                }
            }
            offset += imp.globals.len() as VMIndex;
        }
        None
    }
    fn find_object_function(&self, trait_type: &InternedStr, name: &InternedStr) -> Option<VMIndex> {
        self.traits.iter()
            .find(|trait_| trait_.name.id() == trait_type)
            .and_then(|trait_| (0..).zip(trait_.declarations.iter())
                .find(|&(_, func)| func.name.id() == name)
                .map(|(i, _)| i)
            )
    }
    fn next_global_index(&self) -> VMIndex {
        self.globals.len() as VMIndex + self.impls.iter().fold(0, |y, i| i.globals.len() as VMIndex + y)
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
    fn find_trait_offset(&self, trait_name: &InternedStr, trait_type: &TcType) -> Option<VMIndex> {
        (*self).find_trait_offset(trait_name, trait_type)
    }
    fn find_trait_function(&self, typ: &TcType, id: &InternedStr) -> Option<TypeResult<VMIndex>> {
        (*self).find_trait_function(typ, id)
    }
    fn find_object_function(&self, trait_type: &InternedStr, name: &InternedStr) -> Option<VMIndex> {
        (*self).find_object_function(trait_type, name)
    }
    fn next_global_index(&self) -> VMIndex {
        (*self).next_global_index()
    }
}

pub struct Compiler<'a> {
    globals: &'a (CompilerEnv + 'a),
    stack: HashMap<InternedStr, VMIndex>,
    //Stack which holds indexes for where each closure starts its stack variables
    closure_limits: Vec<VMIndex>,
}

impl <'a> Compiler<'a> {

    pub fn new(globals: &'a CompilerEnv) -> Compiler<'a> {
        Compiler {
            globals: globals,
            stack: HashMap::new(),
            closure_limits: Vec::new(),
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

    fn find_field(&self, struct_: &InternedStr, field: &InternedStr) -> Option<VMIndex> {
        self.globals.find_field(struct_, field)
    }

    fn find_tag(&self, enum_: &InternedStr, constructor: &InternedStr) -> Option<VMTag> {
        self.globals.find_tag(enum_, constructor)
    }

    fn find_trait_function(&self, typ: &TcType, id: &InternedStr) -> Option<TypeResult<VMIndex>> {
        self.globals.find_trait_function(typ, id)
    }

    fn new_stack_var(&mut self, s: InternedStr) {
        let v = self.stack.len() as VMIndex;
        if self.stack.get(&s).is_some() {
            panic!("Variable shadowing is not allowed")
        }
        self.stack.insert(s, v);
    }

    fn stack_size(&self) -> VMIndex {
        self.stack.len() as VMIndex
    }

    pub fn compile_module(&mut self, module: &Module<TcIdent>) -> Assembly {
        let mut initializer = FunctionEnv::new();
        let mut globals = Vec::new();
        let global_offset = self.globals.next_global_index() - module.next_global_index();
        for global in module.globals.iter() {
            let index = global_offset + globals.len() as VMIndex;
            globals.push(self.compile_global(&mut initializer, index, global));
        }
        let mut trait_globals = Vec::new();
        for imp in module.impls.iter() {
            trait_globals.push(TraitFunctions {
                index: global_offset + globals.len() as VMIndex,
                trait_name: imp.trait_name.id().clone(),
                impl_type: imp.typ.clone()
            });
            for f in imp.globals.iter() {
                let index = global_offset + globals.len() as VMIndex;
                globals.push(self.compile_global(&mut initializer, index, f));
            }
        }

        let FunctionEnv { instructions, inner_functions, .. } = initializer;
        debug!("Done compiling module");
        Assembly {
            initializer: instructions,
            anonymous_functions: inner_functions,
            globals: globals,
            trait_functions: trait_globals
        }
    }

    pub fn compile_global<'b>(&mut self, initializer: &mut FunctionEnv<'b>, index: VMIndex, function: &'b ast::Global<TcIdent>) -> Binding {
        debug!("-- Compiling {}", function.declaration.name.id());
        initializer.dictionary = function.declaration.typ.constraints.as_slice();
        self.compile(&function.expression, initializer);
        initializer.instructions.push(StoreGlobal(index));
        let name = function.declaration.name.name;
        let typ = function.declaration.typ.clone();
        Binding { name: name, typ: typ }
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
        let FunctionEnv { instructions, inner_functions, .. } = env;
        (instructions, inner_functions)
    }

    fn compile(&mut self, expr: &CExpr, function: &mut FunctionEnv) {
        match expr.value {
            Literal(ref lit) => {
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
            Identifier(ref id) => {
                match self.find(id.id(), function).unwrap_or_else(|| panic!("Undefined variable {}", id.id())) {
                    Stack(index) => function.instructions.push(Push(index)),
                    UpVar(index) => function.instructions.push(PushUpVar(index)),
                    Global(index, constraints, typ) => {
                        if constraints.len() != 0 {
                            debug!("Compile dictionary for {}", id.id());
                            self.compile_dictionary(constraints, typ, expr.type_of(), function);
                            function.instructions.push(InstantiateConstrained(index));
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
                function.instructions[jump_index] = CJump(function.instructions.len() as VMIndex);
                self.compile(&**if_true, function);
                function.instructions[false_jump_index] = Jump(function.instructions.len() as VMIndex);
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
                    function.instructions.push(CJump(lhs_end as VMIndex + 3));//Jump to rhs evaluation
                    function.instructions.push(PushInt(0));
                    function.instructions.push(Jump(0));//lhs false, jump to after rhs
                    self.compile(&**rhs, function);
                    function.instructions[lhs_end + 2] = Jump(function.instructions.len() as VMIndex);//replace jump instruction
                }
                else if op.as_slice() == "||" {
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
                function.instructions.push(CallGlobal(args.len() as VMIndex));
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
                function.instructions[pre_jump_index] = Jump(function.instructions.len() as VMIndex);
                self.compile(&**pred, function);
                function.instructions.push(CJump(pre_jump_index as VMIndex + 1));
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
                            for arg in args.iter() {
                                self.stack.remove(arg.id());
                            }
                        }
                        IdentifierPattern(ref id) => { self.stack.remove(id.id()); }
                    }
                }
                for &index in end_jumps.iter() {
                    function.instructions[index] = Jump(function.instructions.len() as VMIndex);
                }
            }
            Array(ref a) => {
                for expr in a.expressions.iter() {
                    self.compile(expr, function);
                }
                function.instructions.push(Construct(0, a.expressions.len() as VMIndex));
            }
            ArrayAccess(ref array, ref index) => {
                self.compile(&**array, function);
                self.compile(&**index, function);
                function.instructions.push(GetIndex);
            }
            Lambda(ref lambda) => {
                let cf = self.compile_lambda(lambda, function);
                function.inner_functions.push(cf);
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
        for arg in lambda.arguments.iter() {
            self.stack.remove(arg.id());
        }
        self.closure_limits.pop();
        //Insert all free variables into the above globals free variables
        //if they arent in that lambdas scope
        for var in f.free_vars.iter() {
            match self.find(var, parent).unwrap() {
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
            dict_size += self.add_dictionary(i as VMIndex, constraint, real_type, function);
        }
        function.instructions.push(Construct(0, dict_size));
    }

    fn add_dictionary(&self, i: VMIndex, constraint: &Constraint, real_type: &TcType, function: &mut FunctionEnv) -> VMIndex {
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
                function.instructions.push(PushInt(impl_index as isize));
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
                            function.instructions.push(InstantiateConstrained(result.value));
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
