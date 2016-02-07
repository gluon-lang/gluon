use std::ops::{Deref, DerefMut};
use interner::{Interner, InternedStr};
use gc::Gc;
use base::ast;
use base::symbol::{Symbol, SymbolModule};
use base::ast::{Typed, DisplayEnv, LExpr, Expr};
use base::types;
use base::types::{Type, TcIdent, TcType, TypeEnv};
use base::scoped_map::ScopedMap;
use types::*;
use self::Variable::*;

pub type CExpr = LExpr<TcIdent>;

#[derive(Clone, Debug)]
pub enum Variable<'a> {
    Stack(VMIndex),
    Global(VMIndex, &'a TcType),
    Constructor(VMTag, VMIndex),
    UpVar(VMIndex),
}

#[derive(Debug)]
pub struct CompiledFunction {
    pub args: VMIndex,
    pub id: Symbol,
    pub typ: TcType,
    pub instructions: Vec<Instruction>,
    pub inner_functions: Vec<CompiledFunction>,
    pub strings: Vec<InternedStr>,
}

struct FunctionEnv {
    instructions: Vec<Instruction>,
    free_vars: Vec<Symbol>,
    inner_functions: Vec<CompiledFunction>,
    strings: Vec<InternedStr>,
    stack: Vec<(VMIndex, Symbol)>,
    stack_size: VMIndex,
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
        FunctionEnvs { envs: vec![FunctionEnv::new()] }
    }

    fn start_function(&mut self, compiler: &mut Compiler) {
        compiler.stack_types.enter_scope();
        compiler.stack_constructors.enter_scope();
        self.envs.push(FunctionEnv::new());
    }

    fn end_function(&mut self, compiler: &mut Compiler) -> FunctionEnv {
        compiler.stack_types.exit_scope();
        compiler.stack_constructors.exit_scope();
        self.envs.pop().expect("FunctionEnv in scope")
    }
}

impl FunctionEnv {
    fn new() -> FunctionEnv {
        FunctionEnv {
            instructions: Vec::new(),
            free_vars: Vec::new(),
            inner_functions: Vec::new(),
            strings: Vec::new(),
            stack: Vec::new(),
            stack_size: 0,
        }
    }

    fn emit(&mut self, i: Instruction) {
        debug!("{:?} {} {}", i, self.stack_size, i.adjust());
        self.stack_size = (self.stack_size as i32 + i.adjust()) as VMIndex;
        self.instructions.push(i);
    }

    fn emit_call(&mut self, args: VMIndex, tail_position: bool) {
        let i = if tail_position {
            TailCall(args)
        } else {
            Call(args)
        };
        self.emit(i);
    }

    fn emit_string(&mut self, s: InternedStr) {
        let index = match self.strings.iter().position(|t| *t == s) {
            Some(i) => i,
            None => {
                self.strings.push(s);
                self.strings.len() - 1
            }
        };
        self.emit(PushString(index as VMIndex));
    }

    fn upvar(&mut self, s: Symbol) -> VMIndex {
        match (0..).zip(self.free_vars.iter()).find(|t| *t.1 == s).map(|t| t.0) {
            Some(index) => index,
            None => {
                self.free_vars.push(s);
                (self.free_vars.len() - 1) as VMIndex
            }
        }
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

    fn pop_pattern(&mut self, pattern: &ast::Pattern<TcIdent>) -> VMIndex {
        match *pattern {
            ast::Pattern::Constructor(_, ref args) => {
                for _ in 0..args.len() {
                    self.pop_var();
                }
                args.len() as VMIndex
            }
            ast::Pattern::Record { ref fields, .. } => {
                for _ in fields {
                    self.pop_var();
                }
                fields.len() as VMIndex
            }
            ast::Pattern::Identifier(_) => {
                self.pop_var();
                1
            }
        }
    }
}

pub trait CompilerEnv: TypeEnv {
    fn find_var(&self, id: &Symbol) -> Option<Variable>;
}

impl<T: CompilerEnv, U: CompilerEnv> CompilerEnv for (T, U) {
    fn find_var(&self, s: &Symbol) -> Option<Variable> {
        let &(ref outer, ref inner) = self;
        inner.find_var(s)
             .or_else(|| outer.find_var(s))
    }
}

impl<'a, T: CompilerEnv> CompilerEnv for &'a T {
    fn find_var(&self, s: &Symbol) -> Option<Variable> {
        (**self).find_var(s)
    }
}
impl CompilerEnv for TypeInfos {
    fn find_var(&self, id: &Symbol) -> Option<Variable> {
        fn count_function_args(typ: &TcType) -> VMIndex {
            match **typ {
                Type::Function(_, ref rest) => 1 + count_function_args(rest),
                _ => 0,
            }
        }

        self.id_to_type
            .iter()
            .filter_map(|(_, &(_, ref typ))| {
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
                Variable::Constructor(tag as VMTag, count_function_args(&typ))
            })
    }
}

pub struct Compiler<'a> {
    globals: &'a (CompilerEnv + 'a),
    interner: &'a mut Interner,
    gc: &'a mut Gc,
    symbols: SymbolModule<'a>,
    stack_constructors: ScopedMap<Symbol, TcType>,
    stack_types: ScopedMap<Symbol, (Vec<types::Generic<Symbol>>, TcType)>,
}

impl<'a> ::base::types::KindEnv for Compiler<'a> {
    fn find_kind(&self, _type_name: Symbol) -> Option<types::RcKind> {
        None
    }
}

impl<'a> TypeEnv for Compiler<'a> {
    fn find_type(&self, _id: &Symbol) -> Option<&TcType> {
        None
    }
    fn find_type_info(&self, id: &Symbol) -> Option<(&[types::Generic<Symbol>], Option<&TcType>)> {
        self.stack_types
            .get(id)
            .map(|&(ref generics, ref typ)| (&generics[..], Some(typ)))
    }
    fn find_record(&self, _fields: &[Symbol]) -> Option<(&TcType, &TcType)> {
        None
    }
}

impl<'a> Compiler<'a> {
    pub fn new(globals: &'a CompilerEnv,
               interner: &'a mut Interner,
               gc: &'a mut Gc,
               symbols: SymbolModule<'a>)
               -> Compiler<'a> {
        Compiler {
            globals: globals,
            interner: interner,
            gc: gc,
            symbols: symbols,
            stack_constructors: ScopedMap::new(),
            stack_types: ScopedMap::new(),
        }
    }

    fn intern(&mut self, s: &str) -> InternedStr {
        self.interner.intern(self.gc, s)
    }

    fn find(&self, id: Symbol, current: &mut FunctionEnvs) -> Option<Variable> {
        self.stack_constructors
            .iter()
            .filter_map(|(_, typ)| {
                match **typ {
                    Type::Variants(ref variants) => {
                        variants.iter()
                                .enumerate()
                                .find(|&(_, v)| v.0 == id)
                    }
                    _ => None,
                }
            })
            .next()
            .map(|(tag, &(_, ref typ))| {
                Constructor(tag as VMIndex, types::arg_iter(typ).count() as VMIndex)
            })
            .or_else(|| {
                current.stack
                       .iter()
                       .rev()
                       .cloned()
                       .find(|&(_, var)| var == id)
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
                                      .find(|&(_, var)| var == id)
                                      .map(|_| UpVar(current[0].upvar(id)))
                               })
                               .next()
                       })
            })
            .or_else(|| self.globals.find_var(&id))
    }


    fn remove_aliases<'s>(&'s self, typ: &'s Type<Symbol, TcType>) -> &'s Type<Symbol, TcType> {
        let mut typ = typ;
        loop {
            match *typ {
                Type::Data(types::TypeConstructor::Data(id), _) => {
                    match self.find_type_info(&id) {
                        Some((_, Some(real_type))) => {
                            typ = real_type;
                        }
                        _ => break,
                    }
                }
                _ => break,
            }
        }
        typ
    }
    fn find_field(&self, typ: &Type<Symbol, TcType>, field: &Symbol) -> Option<VMIndex> {
        // Walk through all type aliases
        match *self.remove_aliases(typ) {
            Type::Record { ref fields, .. } => {
                fields.iter()
                      .position(|f| f.name == *field)
                      .map(|i| i as VMIndex)
            }
            ref typ => {
                panic!("ICE: FieldAccess on {}",
                       types::display_type(&self.symbols, typ))
            }
        }
    }

    fn find_tag(&self, typ: &TcType, constructor: &Symbol) -> Option<VMTag> {
        match *self.remove_aliases(typ) {
            Type::Variants(ref variants) => {
                variants.iter()
                        .enumerate()
                        .find(|&(_, v)| v.0 == *constructor)
                        .map(|(tag, _)| tag as VMTag)
            }
            _ => None,
        }
    }

    ///Compiles an expression to a zero argument function which can be directly fed to the
    ///interpreter
    pub fn compile_expr(&mut self, expr: &CExpr) -> CompiledFunction {
        let mut env = FunctionEnvs::new();
        self.compile(expr, &mut env, true);
        let FunctionEnv { instructions, inner_functions, strings, .. } = env.end_function(self);
        CompiledFunction {
            args: 0,
            id: self.symbols.symbol(""),
            typ: Type::function(vec![],
                                TcType::from(expr.env_type_of(&self.globals).clone())),
            instructions: instructions,
            inner_functions: inner_functions,
            strings: strings,
        }
    }

    fn load_identifier(&self, id: Symbol, function: &mut FunctionEnvs) {
        match self.find(id, function)
                  .unwrap_or_else(|| panic!("Undefined variable {}", self.symbols.string(&id))) {
            Stack(index) => function.emit(Push(index)),
            UpVar(index) => function.emit(PushUpVar(index)),
            Global(index, _) => function.emit(PushGlobal(index)),
            Constructor(tag, 0) => function.emit(Construct(tag, 0)),
            Constructor(..) => panic!("Constructor {:?} is not fully applied", id),
        }
    }

    fn compile(&mut self, expr: &CExpr, function: &mut FunctionEnvs, tail_position: bool) {
        match expr.value {
            Expr::Literal(ref lit) => {
                match *lit {
                    ast::LiteralEnum::Integer(i) => function.emit(PushInt(i as isize)),
                    ast::LiteralEnum::Float(f) => function.emit(PushFloat(f)),
                    ast::LiteralEnum::Bool(b) => {
                        function.emit(PushInt(if b {
                            1
                        } else {
                            0
                        }))
                    }
                    ast::LiteralEnum::String(ref s) => function.emit_string(self.intern(&s)),
                    ast::LiteralEnum::Char(c) => function.emit(PushInt(c as isize)),
                }
            }
            Expr::Identifier(ref id) => self.load_identifier(*id.id(), function),
            Expr::IfElse(ref pred, ref if_true, ref if_false) => {
                self.compile(&**pred, function, false);
                let jump_index = function.instructions.len();
                function.emit(CJump(0));
                if let Some(ref if_false) = *if_false {
                    self.compile(&**if_false, function, tail_position);
                }
                let false_jump_index = function.instructions.len();
                function.emit(Jump(0));
                function.instructions[jump_index] = CJump(function.instructions.len() as VMIndex);
                self.compile(&**if_true, function, tail_position);
                function.instructions[false_jump_index] =
                    Jump(function.instructions.len() as VMIndex);
            }
            Expr::BinOp(ref lhs, ref op, ref rhs) => {
                if op.name == self.symbols.symbol("&&") {
                    self.compile(&**lhs, function, false);
                    let lhs_end = function.instructions.len();
                    function.emit(CJump(lhs_end as VMIndex + 3));//Jump to rhs evaluation
                    function.emit(PushInt(0));
                    function.emit(Jump(0));//lhs false, jump to after rhs
                    self.compile(&**rhs, function, tail_position);
                    function.instructions[lhs_end + 2] =
                        Jump(function.instructions.len() as VMIndex);//replace jump instruction
                } else if op.name == self.symbols.symbol("||") {
                    self.compile(&**lhs, function, false);
                    let lhs_end = function.instructions.len();
                    function.emit(CJump(0));
                    self.compile(&**rhs, function, tail_position);
                    function.emit(Jump(0));
                    function.instructions[lhs_end] = CJump(function.instructions.len() as VMIndex);
                    function.emit(PushInt(1));
                    let end = function.instructions.len();
                    function.instructions[end - 2] = Jump(end as VMIndex);
                } else {
                    let instr = match self.symbols.string(&op.name) {
                        "#Int+" => AddInt,
                        "#Int-" => SubtractInt,
                        "#Int*" => MultiplyInt,
                        "#Int/" => DivideInt,
                        "#Int<" => IntLT,
                        "#Int==" => IntEQ,
                        "#Float+" => AddFloat,
                        "#Float-" => SubtractFloat,
                        "#Float*" => MultiplyFloat,
                        "#Float/" => DivideFloat,
                        "#Float<" => FloatLT,
                        "#Float==" => FloatEQ,
                        _ => {
                            self.load_identifier(*op.id(), function);
                            Call(2)
                        }
                    };
                    self.compile(&**lhs, function, false);
                    self.compile(&**rhs, function, false);
                    function.emit(instr);
                }
            }
            Expr::Let(ref bindings, ref body) => {
                self.stack_constructors.enter_scope();
                let stack_start = function.stack_size;
                // Index where the instruction to create the first closure should be at
                let first_index = function.instructions.len();
                let is_recursive = bindings.iter().all(|bind| bind.arguments.len() > 0);
                if is_recursive {
                    for bind in bindings.iter() {
                        // Add the NewClosure instruction before hand
                        // it will be fixed later
                        function.emit(NewClosure(0, 0));
                        match bind.name.value {
                            ast::Pattern::Identifier(ref name) => {
                                function.new_stack_var(*name.id());
                            }
                            _ => panic!("ICE: Unexpected non identifer pattern"),
                        }
                    }
                }
                for (i, bind) in bindings.iter().enumerate() {

                    if is_recursive {
                        function.emit(Push(stack_start + i as VMIndex));
                        let name = match bind.name.value {
                            ast::Pattern::Identifier(ref name) => name,
                            _ => panic!("Lambda binds to non identifer pattern"),
                        };
                        let (function_index, vars, cf) = self.compile_lambda(name,
                                                                             &bind.arguments,
                                                                             &bind.expression,
                                                                             function);
                        let offset = first_index + i;
                        function.instructions[offset] = NewClosure(function_index, vars);
                        function.emit(CloseClosure(vars));
                        function.stack_size -= vars;
                        function.inner_functions.push(cf);
                    } else {
                        self.compile(&bind.expression, function, false);
                        let typ = bind.expression.env_type_of(self);
                        self.compile_let_pattern(&bind.name, &typ, function);
                    }
                }
                self.compile(&body, function, tail_position);
                let mut count = 0;
                for binding in bindings {
                    count += function.pop_pattern(&binding.name);
                }
                self.stack_constructors.exit_scope();
                function.emit(Slide(count));
            }
            Expr::Call(ref func, ref args) => {
                if let Expr::Identifier(ref id) = func.value {
                    if let Some(Constructor(tag, num_args)) = self.find(*id.id(), function) {
                        for arg in args.iter() {
                            self.compile(arg, function, false);
                        }
                        function.emit(Construct(tag, num_args));
                        return;
                    }
                }
                self.compile(&**func, function, false);
                for arg in args.iter() {
                    self.compile(arg, function, false);
                }
                function.emit_call(args.len() as VMIndex, tail_position);
            }
            Expr::FieldAccess(ref expr, ref field) => {
                self.compile(&**expr, function, false);
                debug!("{:?} {:?}", expr, field);
                let typ = expr.env_type_of(self);
                let typ = typ.inner_app();
                debug!("FieldAccess {}", types::display_type(&self.symbols, typ));
                let field_index = self.find_field(typ, field.id())
                                      .expect("ICE: Undefined field in field access");
                function.emit(GetField(field_index));
            }
            Expr::Match(ref expr, ref alts) => {
                self.compile(&**expr, function, false);
                let mut start_jumps = Vec::new();
                let mut end_jumps = Vec::new();
                let typ = expr.env_type_of(self);
                let mut catch_all = false;
                for alt in alts.iter() {
                    match alt.pattern.value {
                        ast::Pattern::Constructor(ref id, _) => {
                            let tag = self.find_tag(&typ, id.id())
                                          .unwrap_or_else(|| {
                                              panic!("Could not find tag for {}::{}",
                                                     types::display_type(&self.symbols, &typ),
                                                     self.symbols.string(id.id()))
                                          });
                            function.emit(TestTag(tag));
                            start_jumps.push(function.instructions.len());
                            function.emit(CJump(0));
                        }
                        ast::Pattern::Record { .. } => {
                            catch_all = true;
                            start_jumps.push(function.instructions.len());
                        }
                        _ => {
                            catch_all = true;
                            start_jumps.push(function.instructions.len());
                            function.emit(Jump(0));
                        }
                    }
                }
                // Create a catch all to prevent us from running into undefined behaviour
                if !catch_all {
                    let error_fn = self.symbols.symbol("#error");
                    self.load_identifier(error_fn, function);
                    function.emit_string(self.intern("Non-exhaustive pattern"));
                    function.emit(Call(1));
                    // The stack has been increased by 1 here but it should not affect compiling the
                    // alternatives
                    function.stack_size -= 1;
                }
                for (alt, &start_index) in alts.iter().zip(start_jumps.iter()) {
                    self.stack_constructors.enter_scope();
                    match alt.pattern.value {
                        ast::Pattern::Constructor(_, ref args) => {
                            function.instructions[start_index] =
                                CJump(function.instructions.len() as VMIndex);
                            function.emit(Split);
                            for arg in args.iter() {
                                function.push_stack_var(arg.id().clone());
                            }
                        }
                        ast::Pattern::Record { .. } => {
                            let typ = &expr.env_type_of(self);
                            self.compile_let_pattern(&alt.pattern, typ, function);
                        }
                        ast::Pattern::Identifier(ref id) => {
                            function.instructions[start_index] =
                                Jump(function.instructions.len() as VMIndex);
                            function.new_stack_var(id.id().clone());
                        }
                    }
                    self.compile(&alt.expression, function, tail_position);
                    end_jumps.push(function.instructions.len());
                    let count = function.pop_pattern(&alt.pattern);
                    self.stack_constructors.exit_scope();
                    function.emit(Slide(count));
                    function.emit(Jump(0));
                }
                for &index in end_jumps.iter() {
                    function.instructions[index] = Jump(function.instructions.len() as VMIndex);
                }
            }
            Expr::Array(ref a) => {
                for expr in a.expressions.iter() {
                    self.compile(expr, function, false);
                }
                function.emit(Construct(0, a.expressions.len() as VMIndex));
            }
            Expr::Lambda(ref lambda) => {
                let (function_index, vars, cf) = self.compile_lambda(&lambda.id,
                                                                     &lambda.arguments,
                                                                     &lambda.body,
                                                                     function);
                function.emit(MakeClosure(function_index, vars));
                function.stack_size -= vars;
                function.inner_functions.push(cf);
            }
            Expr::Type(ref type_bindings, ref expr) => {
                for type_binding in type_bindings {
                    if let Type::Data(types::TypeConstructor::Data(name), ref args) =
                           *type_binding.name {
                        let generic_args = extract_generics(args);
                        self.stack_types.insert(name, (generic_args, type_binding.typ.clone()));
                        self.stack_constructors.insert(name, type_binding.typ.clone());
                    }
                }
                self.compile(&**expr, function, tail_position)
            }
            Expr::Record { exprs: ref fields, .. } => {
                for field in fields {
                    match field.1 {
                        Some(ref field_expr) => self.compile(field_expr, function, false),
                        None => self.load_identifier(field.0, function),
                    }
                }
                function.emit(Construct(0, fields.len() as u32));
            }
            Expr::Tuple(ref exprs) => {
                for expr in exprs {
                    self.compile(expr, function, false);
                }
                function.emit(Construct(0, exprs.len() as u32));
            }
        }
    }

    fn compile_let_pattern(&mut self,
                           pattern: &ast::Pattern<TcIdent>,
                           typ: &TcType,
                           function: &mut FunctionEnvs) {
        match *pattern {
            ast::Pattern::Identifier(ref name) => {
                function.new_stack_var(*name.id());
            }
            ast::Pattern::Record { ref types, ref fields, .. } => {
                let mut typ = typ.clone();
                if let Type::Data(types::TypeConstructor::Data(id), _) = *typ {
                    typ = self.find_type_info(&id)
                              .and_then(|(_, typ)| typ.cloned())
                              .unwrap_or(typ);
                }
                // Insert all variant constructor into scope
                with_pattern_types(types, &typ, |name, alias| {
                    // FIXME: Workaround so that both the types name in this module and its global
                    // name are imported. Without this aliases may not be traversed properly
                    self.stack_types.insert(alias.name, (alias.args.clone(), alias.typ.clone()));
                    self.stack_constructors.insert(alias.name, alias.typ.clone());
                    self.stack_types.insert(name, (alias.args.clone(), alias.typ.clone()));
                    self.stack_constructors.insert(name, alias.typ.clone());
                });
                match *typ {
                    Type::Record { fields: ref type_fields, .. } => {
                        function.emit(Split);
                        for field in type_fields {
                            let name = match fields.iter().find(|tup| tup.0 == field.name) {
                                Some(&(name, bind)) => bind.unwrap_or(name),
                                None => self.symbols.symbol(""),
                            };
                            function.push_stack_var(name);
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
                      id: &TcIdent,
                      arguments: &[TcIdent],
                      body: &LExpr<TcIdent>,
                      function: &mut FunctionEnvs)
                      -> (VMIndex, VMIndex, CompiledFunction) {
        function.start_function(self);
        for arg in arguments {
            function.push_stack_var(*arg.id());
        }
        self.compile(body, function, true);

        for _ in 0..arguments.len() {
            function.pop_var();
        }
        // Insert all free variables into the above globals free variables
        // if they arent in that lambdas scope
        let f = function.end_function(self);
        for &var in f.free_vars.iter() {
            match self.find(var, function).expect("free_vars: find") {
                Stack(index) => function.emit(Push(index)),
                UpVar(index) => function.emit(PushUpVar(index)),
                _ => panic!("Free variables can only be on the stack or another upvar"),
            }
        }
        let function_index = function.inner_functions.len() as VMIndex;
        let free_vars = f.free_vars.len() as VMIndex;
        let FunctionEnv { instructions, inner_functions, strings, .. } = f;
        (function_index,
         free_vars,
         CompiledFunction {
            args: arguments.len() as VMIndex,
            id: id.id().clone(),
            typ: id.typ.clone(),
            instructions: instructions,
            inner_functions: inner_functions,
            strings: strings,
        })
    }
}

fn with_pattern_types<F>(types: &[(Symbol, Option<Symbol>)], typ: &TcType, mut f: F)
    where F: FnMut(Symbol, &types::Alias<Symbol, TcType>)
{
    if let Type::Record { types: ref record_type_fields, .. } = **typ {
        for field in types {
            let associated_type = record_type_fields.iter()
                                                    .find(|type_field| type_field.name == field.0)
                                                    .expect("Associated type to exist in record");
            f(field.0, &associated_type.typ);
        }
    }
}

fn extract_generics(args: &[TcType]) -> Vec<types::Generic<Symbol>> {
    args.iter()
        .map(|arg| {
            match **arg {
                Type::Generic(ref gen) => gen.clone(),
                _ => {
                    panic!("The type on the lhs of a type binding did not have all generic \
                            arguments")
                }
            }
        })
        .collect()
}
