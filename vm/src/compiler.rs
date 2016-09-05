use std::ops::{Deref, DerefMut};
use interner::InternedStr;
use base::ast::{self, TypedIdent};
use base::instantiate;
use base::symbol::{Symbol, SymbolRef, SymbolModule};
use base::ast::{Typed, DisplayEnv, SpannedExpr, Expr};
use base::types;
use base::types::{Alias, KindEnv, ArcType, Type, TypeEnv};
use base::scoped_map::ScopedMap;
use types::*;
use vm::GlobalVmState;
use self::Variable::*;

use Result;

pub type CExpr = SpannedExpr<TypedIdent>;

#[derive(Clone, Debug)]
pub enum Variable<G> {
    Stack(VmIndex),
    Global(G),
    Constructor(VmTag, VmIndex),
    UpVar(VmIndex),
}

#[derive(Debug)]
pub struct CompiledFunction {
    pub args: VmIndex,
    pub id: Symbol,
    pub typ: ArcType,
    pub instructions: Vec<Instruction>,
    pub inner_functions: Vec<CompiledFunction>,
    pub strings: Vec<InternedStr>,
    /// Storage for globals which are needed by the module which is currently being compiled
    pub module_globals: Vec<Symbol>,
}

impl CompiledFunction {
    pub fn new(args: VmIndex, id: Symbol, typ: ArcType) -> CompiledFunction {
        CompiledFunction {
            args: args,
            id: id,
            typ: typ,
            instructions: Vec::new(),
            inner_functions: Vec::new(),
            strings: Vec::new(),
            module_globals: Vec::new(),
        }
    }
}

struct FunctionEnv {
    stack: Vec<(VmIndex, Symbol)>,
    stack_size: VmIndex,
    free_vars: Vec<Symbol>,
    function: CompiledFunction,
}

struct FunctionEnvs {
    envs: Vec<FunctionEnv>,
}

impl Deref for FunctionEnvs {
    type Target = FunctionEnv;
    fn deref(&self) -> &FunctionEnv {
        self.envs.last().expect("FunctionEnv")
    }
}

impl DerefMut for FunctionEnvs {
    fn deref_mut(&mut self) -> &mut FunctionEnv {
        self.envs.last_mut().expect("FunctionEnv")
    }
}

impl FunctionEnvs {
    fn new() -> FunctionEnvs {
        FunctionEnvs { envs: vec![] }
    }

    fn start_function(&mut self,
                      compiler: &mut Compiler,
                      args: VmIndex,
                      id: Symbol,
                      typ: ArcType) {
        compiler.stack_types.enter_scope();
        compiler.stack_constructors.enter_scope();
        self.envs.push(FunctionEnv::new(args, id, typ));
    }

    fn end_function(&mut self, compiler: &mut Compiler) -> FunctionEnv {
        compiler.stack_types.exit_scope();
        compiler.stack_constructors.exit_scope();
        self.envs.pop().expect("FunctionEnv in scope")
    }
}

impl FunctionEnv {
    fn new(args: VmIndex, id: Symbol, typ: ArcType) -> FunctionEnv {
        FunctionEnv {
            free_vars: Vec::new(),
            stack: Vec::new(),
            stack_size: 0,
            function: CompiledFunction::new(args, id, typ),
        }
    }

    fn emit(&mut self, i: Instruction) {
        if let Slide(0) = i {
            return;
        }
        debug!("{:?} {} {}", i, self.stack_size, i.adjust());
        self.stack_size = (self.stack_size as i32 + i.adjust()) as VmIndex;
        self.function.instructions.push(i);
    }

    fn emit_call(&mut self, args: VmIndex, tail_position: bool) {
        let i = if tail_position {
            TailCall(args)
        } else {
            Call(args)
        };
        self.emit(i);
    }

    fn emit_string(&mut self, s: InternedStr) {
        let index = match self.function.strings.iter().position(|t| *t == s) {
            Some(i) => i,
            None => {
                self.function.strings.push(s);
                self.function.strings.len() - 1
            }
        };
        self.emit(PushString(index as VmIndex));
    }

    fn upvar(&mut self, s: &Symbol) -> VmIndex {
        match self.free_vars.iter().position(|t| t == s) {
            Some(index) => index as VmIndex,
            None => {
                self.free_vars.push(s.clone());
                (self.free_vars.len() - 1) as VmIndex
            }
        }
    }

    fn stack_size(&mut self) -> VmIndex {
        (self.stack_size - 1) as VmIndex
    }

    fn push_stack_var(&mut self, s: Symbol) {
        self.stack_size += 1;
        self.new_stack_var(s)
    }

    fn new_stack_var(&mut self, s: Symbol) {
        debug!("Push var: {:?} at {}", s, self.stack_size - 1);
        self.stack.push((self.stack_size - 1, s));
    }

    fn pop_var(&mut self) {
        let x = self.stack.pop();
        debug!("Pop var: {:?}", x);
    }

    fn pop_pattern(&mut self, pattern: &ast::Pattern<TypedIdent>) -> VmIndex {
        match *pattern {
            ast::Pattern::Constructor(_, ref args) => {
                for _ in 0..args.len() {
                    self.pop_var();
                }
                args.len() as VmIndex
            }
            ast::Pattern::Record { ref fields, .. } => {
                for _ in fields {
                    self.pop_var();
                }
                fields.len() as VmIndex
            }
            ast::Pattern::Ident(_) => {
                self.pop_var();
                1
            }
        }
    }
}

pub trait CompilerEnv: TypeEnv {
    fn find_var(&self, id: &Symbol) -> Option<Variable<Symbol>>;
}

impl CompilerEnv for TypeInfos {
    fn find_var(&self, id: &Symbol) -> Option<Variable<Symbol>> {
        fn count_function_args(typ: &ArcType) -> VmIndex {
            match typ.as_function() {
                Some((_, ret)) => 1 + count_function_args(ret),
                None => 0,
            }
        }

        self.id_to_type
            .iter()
            .filter_map(|(_, ref alias)| {
                alias.typ.as_ref().and_then(|typ| {
                    match **typ {
                        Type::Variants(ref variants) => {
                            variants.iter()
                                .enumerate()
                                .find(|&(_, v)| v.0 == *id)
                        }
                        _ => None,
                    }
                })
            })
            .next()
            .map(|(tag, &(_, ref typ))| {
                Variable::Constructor(tag as VmTag, count_function_args(&typ))
            })
    }
}

pub struct Compiler<'a> {
    globals: &'a (CompilerEnv + 'a),
    vm: &'a GlobalVmState,
    symbols: SymbolModule<'a>,
    stack_constructors: ScopedMap<Symbol, ArcType>,
    stack_types: ScopedMap<Symbol, Alias<Symbol, ArcType>>,
}

impl<'a> KindEnv for Compiler<'a> {
    fn find_kind(&self, _type_name: &SymbolRef) -> Option<types::RcKind> {
        None
    }
}

impl<'a> TypeEnv for Compiler<'a> {
    fn find_type(&self, _id: &SymbolRef) -> Option<&ArcType> {
        None
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>> {
        self.stack_types
            .get(id)
    }

    fn find_record(&self, _fields: &[Symbol]) -> Option<(&ArcType, &ArcType)> {
        None
    }
}

impl<'a, T: CompilerEnv> CompilerEnv for &'a T {
    fn find_var(&self, s: &Symbol) -> Option<Variable<Symbol>> {
        (**self).find_var(s)
    }
}

impl<'a> Compiler<'a> {
    pub fn new(globals: &'a (CompilerEnv + 'a),
               vm: &'a GlobalVmState,
               symbols: SymbolModule<'a>)
               -> Compiler<'a> {
        Compiler {
            globals: globals,
            vm: vm,
            symbols: symbols,
            stack_constructors: ScopedMap::new(),
            stack_types: ScopedMap::new(),
        }
    }

    fn intern(&mut self, s: &str) -> Result<InternedStr> {
        self.vm.intern(s)
    }

    fn find(&self, id: &Symbol, current: &mut FunctionEnvs) -> Option<Variable<VmIndex>> {
        let variable = self.stack_constructors
            .iter()
            .filter_map(|(_, typ)| {
                match **typ {
                    Type::Variants(ref variants) => {
                        variants.iter()
                            .enumerate()
                            .find(|&(_, v)| v.0 == *id)
                    }
                    _ => None,
                }
            })
            .next()
            .map(|(tag, &(_, ref typ))| {
                Constructor(tag as VmIndex, types::arg_iter(typ).count() as VmIndex)
            })
            .or_else(|| {
                current.stack
                    .iter()
                    .rev()
                    .cloned()
                    .find(|&(_, ref var)| var == id)
                    .map(|(index, _)| Stack(index))
                    .or_else(|| {
                        let i = current.envs.len() - 1;
                        let (rest, current) = current.envs.split_at_mut(i);
                        rest.iter()
                            .rev()
                            .filter_map(|env| {
                                env.stack
                                    .iter()
                                    .rev()
                                    .cloned()
                                    .find(|&(_, ref var)| var == id)
                                    .map(|_| UpVar(current[0].upvar(id)))
                            })
                            .next()
                    })
            })
            .or_else(|| self.globals.find_var(&id));
        variable.map(|variable| {
            match variable {
                Stack(i) => Stack(i),
                Global(s) => {
                    let existing = current.function
                        .module_globals
                        .iter()
                        .position(|existing| existing == &s);
                    Global(existing.unwrap_or_else(|| {
                        current.function.module_globals.push(s);
                        current.function.module_globals.len() - 1
                    }) as VmIndex)
                }
                Constructor(tag, args) => Constructor(tag, args),
                UpVar(i) => UpVar(i),
            }
        })
    }

    fn find_field(&self, typ: &ArcType, field: &Symbol) -> Option<VmIndex> {
        // Walk through all type aliases
        match **instantiate::remove_aliases_cow(self, typ) {
            Type::Record { ref fields, .. } => {
                fields.iter()
                    .position(|f| f.name.name_eq(field))
                    .map(|i| i as VmIndex)
            }
            ref typ => {
                panic!("ICE: Projection on {}",
                       types::display_type(&self.symbols, typ))
            }
        }
    }

    fn find_tag(&self, typ: &ArcType, constructor: &Symbol) -> Option<VmTag> {
        match **instantiate::remove_aliases_cow(self, typ) {
            Type::Variants(ref variants) => {
                variants.iter()
                    .enumerate()
                    .find(|&(_, v)| v.0 == *constructor)
                    .map(|(tag, _)| tag as VmTag)
            }
            _ => None,
        }
    }

    /// Compiles an expression to a zero argument function which can be directly fed to the
    /// interpreter
    pub fn compile_expr(&mut self, expr: &CExpr) -> Result<CompiledFunction> {
        let mut env = FunctionEnvs::new();
        let id = self.symbols.symbol("");
        let typ = Type::function(vec![],
                                 ArcType::from(expr.env_type_of(&self.globals).clone()));
        env.start_function(self, 0, id, typ);
        try!(self.compile(expr, &mut env, true));
        let FunctionEnv { function, .. } = env.end_function(self);
        Ok(function)
    }

    fn load_identifier(&self, id: &Symbol, function: &mut FunctionEnvs) {
        match self.find(id, function)
            .unwrap_or_else(|| panic!("Undefined variable {}", self.symbols.string(&id))) {
            Stack(index) => function.emit(Push(index)),
            UpVar(index) => function.emit(PushUpVar(index)),
            Global(index) => function.emit(PushGlobal(index)),
            // Zero argument constructors can be compiled as integers
            Constructor(tag, 0) => {
                function.emit(Construct {
                    tag: tag,
                    args: 0,
                })
            }
            Constructor(..) => panic!("Constructor {:?} is not fully applied", id),
        }
    }

    fn compile(&mut self,
               mut expr: &CExpr,
               function: &mut FunctionEnvs,
               tail_position: bool)
               -> Result<()> {
        // Store a stack of expressions which need to be cleaned up after this "tailcall" loop is
        // done
        let mut exprs = Vec::new();
        exprs.push(expr);
        while let Some(next) = try!(self.compile_(expr, function, tail_position)) {
            exprs.push(next);
            expr = next;
        }
        for expr in exprs.iter().rev() {
            let mut count = 0;
            if let Expr::LetBindings(ref bindings, _) = expr.value {
                for binding in bindings {
                    count += function.pop_pattern(&binding.name.value);
                }
                self.stack_constructors.exit_scope();
            }
            function.emit(Slide(count));
        }
        Ok(())
    }

    fn compile_<'e>(&mut self,
                    expr: &'e CExpr,
                    function: &mut FunctionEnvs,
                    tail_position: bool)
                    -> Result<Option<&'e CExpr>> {
        match expr.value {
            Expr::Literal(ref lit) => {
                match *lit {
                    ast::Literal::Integer(i) => function.emit(PushInt(i as isize)),
                    ast::Literal::Byte(b) => function.emit(PushByte(b)),
                    ast::Literal::Float(f) => function.emit(PushFloat(f)),
                    ast::Literal::String(ref s) => function.emit_string(try!(self.intern(&s))),
                    ast::Literal::Char(c) => function.emit(PushInt(c as isize)),
                }
            }
            Expr::Ident(ref id) => self.load_identifier(&id.name, function),
            Expr::IfElse(ref pred, ref if_true, ref if_false) => {
                try!(self.compile(&**pred, function, false));
                let jump_index = function.function.instructions.len();
                function.emit(CJump(0));

                try!(self.compile(&**if_false, function, tail_position));
                // The stack size of the true branch should not be increased by the false branch
                function.stack_size -= 1;
                let false_jump_index = function.function.instructions.len();
                function.emit(Jump(0));

                function.function.instructions[jump_index] =
                    CJump(function.function.instructions.len() as VmIndex);
                try!(self.compile(&**if_true, function, tail_position));
                function.function.instructions[false_jump_index] =
                    Jump(function.function.instructions.len() as VmIndex);
            }
            Expr::Infix(ref lhs, ref op, ref rhs) => {
                if op.name.as_ref() == "&&" {
                    try!(self.compile(&**lhs, function, false));
                    let lhs_end = function.function.instructions.len();
                    function.emit(CJump(lhs_end as VmIndex + 3));//Jump to rhs evaluation
                    function.emit(Construct { tag: 0, args: 0 });
                    function.emit(Jump(0));//lhs false, jump to after rhs
                    // Dont count the integer added added above as the next part of the code never
                    // pushed it
                    function.stack_size -= 1;
                    try!(self.compile(&**rhs, function, tail_position));
                    // replace jump instruction
                    function.function.instructions[lhs_end + 2] =
                        Jump(function.function.instructions.len() as VmIndex);
                } else if op.name.as_ref() == "||" {
                    try!(self.compile(&**lhs, function, false));
                    let lhs_end = function.function.instructions.len();
                    function.emit(CJump(0));
                    try!(self.compile(&**rhs, function, tail_position));
                    function.emit(Jump(0));
                    function.function.instructions[lhs_end] =
                        CJump(function.function.instructions.len() as VmIndex);
                    function.emit(Construct { tag: 1, args: 0 });
                    // Dont count the integer above
                    function.stack_size -= 1;
                    let end = function.function.instructions.len();
                    function.function.instructions[end - 2] = Jump(end as VmIndex);
                } else {
                    let instr = match self.symbols.string(&op.name) {
                        "#Int+" => AddInt,
                        "#Int-" => SubtractInt,
                        "#Int*" => MultiplyInt,
                        "#Int/" => DivideInt,
                        "#Int<" | "#Char<" => IntLT,
                        "#Int==" | "#Char==" => IntEQ,
                        "#Byte+" => AddByte,
                        "#Byte-" => SubtractByte,
                        "#Byte*" => MultiplyByte,
                        "#Byte/" => DivideByte,
                        "#Byte<" => ByteLT,
                        "#Byte==" => ByteEQ,
                        "#Float+" => AddFloat,
                        "#Float-" => SubtractFloat,
                        "#Float*" => MultiplyFloat,
                        "#Float/" => DivideFloat,
                        "#Float<" => FloatLT,
                        "#Float==" => FloatEQ,
                        _ => {
                            self.load_identifier(&op.name, function);
                            Call(2)
                        }
                    };
                    try!(self.compile(&**lhs, function, false));
                    try!(self.compile(&**rhs, function, false));
                    function.emit(instr);
                }
            }
            Expr::LetBindings(ref bindings, ref body) => {
                self.stack_constructors.enter_scope();
                let stack_start = function.stack_size;
                // Index where the instruction to create the first closure should be at
                let first_index = function.function.instructions.len();
                let is_recursive = bindings.iter().all(|bind| bind.arguments.len() > 0);
                if is_recursive {
                    for bind in bindings.iter() {
                        // Add the NewClosure instruction before hand
                        // it will be fixed later
                        function.emit(NewClosure {
                            function_index: 0,
                            upvars: 0,
                        });
                        match bind.name.value {
                            ast::Pattern::Ident(ref name) => {
                                function.new_stack_var(name.name.clone());
                            }
                            _ => panic!("ICE: Unexpected non identifer pattern"),
                        }
                    }
                }
                for (i, bind) in bindings.iter().enumerate() {

                    if is_recursive {
                        function.emit(Push(stack_start + i as VmIndex));
                        let name = match bind.name.value {
                            ast::Pattern::Ident(ref name) => name,
                            _ => panic!("Lambda binds to non identifer pattern"),
                        };
                        let (function_index, vars, cf) = try!(self.compile_lambda(name,
                                                                             &bind.arguments,
                                                                             &bind.expression,
                                                                             function));
                        let offset = first_index + i;
                        function.function.instructions[offset] = NewClosure {
                            function_index: function_index,
                            upvars: vars,
                        };
                        function.emit(CloseClosure(vars));
                        function.stack_size -= vars;
                        function.function.inner_functions.push(cf);
                    } else {
                        try!(self.compile(&bind.expression, function, false));
                        let typ = bind.expression.env_type_of(self);
                        self.compile_let_pattern(&bind.name.value, &typ, function);
                    }
                }
                return Ok(Some(body));
            }
            Expr::App(ref func, ref args) => {
                if let Expr::Ident(ref id) = func.value {
                    if let Some(Constructor(tag, num_args)) = self.find(&id.name, function) {
                        for arg in args.iter() {
                            try!(self.compile(arg, function, false));
                        }
                        function.emit(Construct {
                            tag: tag,
                            args: num_args,
                        });
                        return Ok(None);
                    }
                }
                try!(self.compile(&**func, function, false));
                for arg in args.iter() {
                    try!(self.compile(arg, function, false));
                }
                function.emit_call(args.len() as VmIndex, tail_position);
            }
            Expr::Projection(ref expr, ref field) => {
                try!(self.compile(&**expr, function, false));
                debug!("{:?} {:?}", expr, field);
                let typ = expr.env_type_of(self);
                debug!("Projection {}", types::display_type(&self.symbols, &typ));
                let field_index = self.find_field(&typ, &field.name)
                    .expect("ICE: Undefined field in field access");
                function.emit(GetField(field_index));
            }
            Expr::Match(ref expr, ref alts) => {
                try!(self.compile(&**expr, function, false));
                // Indexes for each alternative for a successful match to the alternatives code
                let mut start_jumps = Vec::new();
                let typ = expr.env_type_of(self);
                let mut catch_all = false;
                // Emit a TestTag + Jump instuction for each alternative which jumps to the
                // alternatives code if TestTag is sucessesful
                for alt in alts.iter() {
                    match alt.pattern.value {
                        ast::Pattern::Constructor(ref id, _) => {
                            let tag = self.find_tag(&typ, &id.name)
                                .unwrap_or_else(|| {
                                    panic!("Could not find tag for {}::{}",
                                           types::display_type(&self.symbols, &typ),
                                           self.symbols.string(&id.name))
                                });
                            function.emit(TestTag(tag));
                            start_jumps.push(function.function.instructions.len());
                            function.emit(CJump(0));
                        }
                        ast::Pattern::Record { .. } => {
                            catch_all = true;
                            start_jumps.push(function.function.instructions.len());
                        }
                        _ => {
                            catch_all = true;
                            start_jumps.push(function.function.instructions.len());
                            function.emit(Jump(0));
                        }
                    }
                }
                // Create a catch all to prevent us from running into undefined behaviour
                if !catch_all {
                    let error_fn = self.symbols.symbol("#error");
                    self.load_identifier(&error_fn, function);
                    function.emit_string(try!(self.intern("Non-exhaustive pattern")));
                    function.emit(Call(1));
                    // The stack has been increased by 1 here but it should not affect compiling the
                    // alternatives
                    function.stack_size -= 1;
                }
                // Indexes for each alternative from the end of the alternatives code to code
                // after the alternative
                let mut end_jumps = Vec::new();
                for (alt, &start_index) in alts.iter().zip(start_jumps.iter()) {
                    self.stack_constructors.enter_scope();
                    match alt.pattern.value {
                        ast::Pattern::Constructor(_, ref args) => {
                            function.function.instructions[start_index] =
                                CJump(function.function.instructions.len() as VmIndex);
                            function.emit(Split);
                            for arg in args.iter() {
                                function.push_stack_var(arg.name.clone());
                            }
                        }
                        ast::Pattern::Record { .. } => {
                            let typ = &expr.env_type_of(self);
                            self.compile_let_pattern(&alt.pattern.value, typ, function);
                        }
                        ast::Pattern::Ident(ref id) => {
                            function.function.instructions[start_index] =
                                Jump(function.function.instructions.len() as VmIndex);
                            function.new_stack_var(id.name.clone());
                        }
                    }
                    try!(self.compile(&alt.expression, function, tail_position));
                    let count = function.pop_pattern(&alt.pattern.value);
                    self.stack_constructors.exit_scope();
                    function.emit(Slide(count));
                    end_jumps.push(function.function.instructions.len());
                    function.emit(Jump(0));
                }
                for &index in end_jumps.iter() {
                    function.function.instructions[index] =
                        Jump(function.function.instructions.len() as VmIndex);
                }
            }
            Expr::Array(ref a) => {
                for expr in a.expressions.iter() {
                    try!(self.compile(expr, function, false));
                }
                function.emit(ConstructArray(a.expressions.len() as VmIndex));
            }
            Expr::Lambda(ref lambda) => {
                let (function_index, vars, cf) = try!(self.compile_lambda(&lambda.id,
                                                                          &lambda.arguments,
                                                                          &lambda.body,
                                                                          function));
                function.emit(MakeClosure {
                    function_index: function_index,
                    upvars: vars,
                });
                function.stack_size -= vars;
                function.function.inner_functions.push(cf);
            }
            Expr::TypeBindings(ref type_bindings, ref expr) => {
                for bind in type_bindings {
                    self.stack_types.insert(bind.alias.name.clone(), bind.alias.clone());
                    let typ = bind.alias.typ.as_ref().expect("TypeBinding type").clone();
                    self.stack_constructors.insert(bind.name.clone(), typ);
                }
                return Ok(Some(expr));
            }
            Expr::Record { exprs: ref fields, .. } => {
                for field in fields {
                    match field.1 {
                        Some(ref field_expr) => try!(self.compile(field_expr, function, false)),
                        None => self.load_identifier(&field.0, function),
                    }
                }
                function.emit(Construct {
                    tag: 0,
                    args: fields.len() as u32,
                });
            }
            Expr::Tuple(ref exprs) => {
                for expr in exprs {
                    try!(self.compile(expr, function, false));
                }
                function.emit(Construct {
                    tag: 0,
                    args: exprs.len() as u32,
                });
            }
            Expr::Block(ref exprs) => {
                let (last, exprs) = exprs.split_last().expect("Expr in block");
                for expr in exprs {
                    try!(self.compile(expr, function, false));
                }
                try!(self.compile(last, function, tail_position));
                function.emit(Slide(exprs.len() as u32 - 1));
            }
        }
        Ok(None)
    }

    fn compile_let_pattern(&mut self,
                           pattern: &ast::Pattern<TypedIdent>,
                           pattern_type: &ArcType,
                           function: &mut FunctionEnvs) {
        match *pattern {
            ast::Pattern::Ident(ref name) => {
                function.new_stack_var(name.name.clone());
            }
            ast::Pattern::Record { ref types, ref fields, .. } => {
                let typ = instantiate::remove_aliases(self, pattern_type.clone());
                // Insert all variant constructor into scope
                with_pattern_types(types, &typ, |name, alias| {
                    // FIXME: Workaround so that both the types name in this module and its global
                    // name are imported. Without this aliases may not be traversed properly
                    self.stack_types.insert(alias.name.clone(), alias.clone());
                    self.stack_types.insert(name.clone(), alias.clone());
                    if let Some(ref typ) = alias.typ {
                        self.stack_constructors.insert(alias.name.clone(), typ.clone());
                        self.stack_constructors.insert(name.clone(), typ.clone());
                    }
                });
                match *typ {
                    Type::Record { fields: ref type_fields, .. } => {
                        if fields.len() == 0 ||
                           (type_fields.len() > 4 && type_fields.len() / fields.len() >= 4) {
                            // For pattern matches on large records where only a few of the fields
                            // are used we instead emit a series of GetField instructions to avoid
                            // pushing a lot of unnecessary fields to the stack
                            let record_index = function.stack_size();
                            for pattern_field in fields {
                                let offset = type_fields.iter()
                                    .position(|field| field.name.name_eq(&pattern_field.0))
                                    .expect("Field to exist");
                                function.emit(Push(record_index));
                                function.emit(GetField(offset as VmIndex));
                                function.new_stack_var(pattern_field.1
                                    .as_ref()
                                    .unwrap_or(&pattern_field.0)
                                    .clone());
                            }
                        } else {
                            function.emit(Split);
                            for field in type_fields {
                                let name = match fields.iter()
                                    .find(|tup| tup.0.name_eq(&field.name)) {
                                    Some(&(ref name, ref bind)) => {
                                        bind.as_ref().unwrap_or(name).clone()
                                    }
                                    None => self.symbols.symbol(""),
                                };
                                function.push_stack_var(name);
                            }
                        }
                    }
                    _ => {
                        panic!("Expected record, got {} at {:?}",
                               types::display_type(&self.symbols, &typ),
                               pattern)
                    }
                }
            }
            ast::Pattern::Constructor(..) => panic!("constructor pattern in let"),
        }
    }

    fn compile_lambda(&mut self,
                      id: &TypedIdent,
                      arguments: &[TypedIdent],
                      body: &SpannedExpr<TypedIdent>,
                      function: &mut FunctionEnvs)
                      -> Result<(VmIndex, VmIndex, CompiledFunction)> {
        function.start_function(self,
                                arguments.len() as VmIndex,
                                id.name.clone(),
                                id.typ.clone());
        for arg in arguments {
            function.push_stack_var(arg.name.clone());
        }
        try!(self.compile(body, function, true));

        for _ in 0..arguments.len() {
            function.pop_var();
        }
        // Insert all free variables into the above globals free variables
        // if they arent in that lambdas scope
        let f = function.end_function(self);
        for var in f.free_vars.iter() {
            match self.find(var, function).expect("free_vars: find") {
                Stack(index) => function.emit(Push(index)),
                UpVar(index) => function.emit(PushUpVar(index)),
                _ => panic!("Free variables can only be on the stack or another upvar"),
            }
        }
        let function_index = function.function.inner_functions.len() as VmIndex;
        let free_vars = f.free_vars.len() as VmIndex;
        let FunctionEnv { function, .. } = f;
        Ok((function_index, free_vars, function))
    }
}

fn with_pattern_types<F>(types: &[(Symbol, Option<Symbol>)], typ: &ArcType, mut f: F)
    where F: FnMut(&Symbol, &Alias<Symbol, ArcType>),
{
    if let Type::Record { types: ref record_type_fields, .. } = **typ {
        for field in types {
            let associated_type = record_type_fields.iter()
                .find(|type_field| type_field.name.name_eq(&field.0))
                .expect("Associated type to exist in record");
            f(&field.0, &associated_type.typ);
        }
    }
}
