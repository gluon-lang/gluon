use std::ops::{Deref, DerefMut};
use interner::InternedStr;
use base::ast::{Literal, Pattern, TypedIdent, Typed, DisplayEnv, SpannedExpr, Expr};
use base::resolve;
use base::kind::{ArcKind, KindEnv};
use base::types::{self, Alias, ArcType, Type, TypeEnv};
use base::scoped_map::ScopedMap;
use base::symbol::{Symbol, SymbolRef, SymbolModule};
use base::pos::{Line, NO_EXPANSION};
use base::source::Source;
use types::*;
use vm::GlobalVmState;
use source_map::{LocalMap, SourceMap};
use self::Variable::*;

use {Error, Result};

pub type CExpr = SpannedExpr<Symbol>;

#[derive(Clone, Debug)]
pub enum Variable<G> {
    Stack(VmIndex),
    Global(G),
    Constructor(VmTag, VmIndex),
    UpVar(VmIndex),
}

/// Field accesses on records can either be by name in the case of polymorphic records or by offset
/// when the record is non-polymorphic (which is faster)
enum FieldAccess {
    Name,
    Index(VmIndex),
}

#[derive(Debug)]
pub struct DebugInfo {
    /// Maps instruction indexes to the line that spawned them
    pub source_map: SourceMap,
    pub local_map: LocalMap,
    pub upvar_names: Vec<String>,
    pub source_name: String,
}

#[derive(Debug)]
pub struct CompiledFunction {
    pub args: VmIndex,
    /// The maximum possible number of stack slots needed for this function
    pub max_stack_size: VmIndex,
    pub id: Symbol,
    pub typ: ArcType,
    pub instructions: Vec<Instruction>,
    pub inner_functions: Vec<CompiledFunction>,
    pub strings: Vec<InternedStr>,
    /// Storage for globals which are needed by the module which is currently being compiled
    pub module_globals: Vec<Symbol>,
    pub records: Vec<Vec<Symbol>>,
    pub debug_info: DebugInfo,
}

impl CompiledFunction {
    pub fn new(args: VmIndex, id: Symbol, typ: ArcType, source_name: String) -> CompiledFunction {
        CompiledFunction {
            args: args,
            max_stack_size: 0,
            id: id,
            typ: typ,
            instructions: Vec::new(),
            inner_functions: Vec::new(),
            strings: Vec::new(),
            module_globals: Vec::new(),
            records: Vec::new(),
            debug_info: DebugInfo {
                source_map: SourceMap::new(),
                local_map: LocalMap::new(),
                upvar_names: Vec::new(),
                source_name: source_name,
            },
        }
    }
}

struct FunctionEnv {
    /// The variables currently in scope in the this function.
    stack: ScopedMap<Symbol, VmIndex>,
    /// The current size of the stack. Not the same as `stack.len()`.
    /// The current size of the stack. Not the same as `stack.len()`.
    stack_size: VmIndex,
    /// The variables which this function takes from the outer scope
    free_vars: Vec<Symbol>,
    /// The line where instructions are currently being emitted
    current_line: Line,
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
        self.envs.push(FunctionEnv::new(args, id, typ, compiler.source_name.clone()));
    }

    fn end_function(&mut self, compiler: &mut Compiler, current_line: Line) -> FunctionEnv {
        compiler.stack_types.exit_scope();
        compiler.stack_constructors.exit_scope();
        let instructions = self.function.instructions.len();
        self.function.debug_info.source_map.close(instructions, current_line);
        {
            let function = &mut **self;
            function.function
                .debug_info
                .upvar_names
                .extend(function.free_vars.iter().map(|s| s.declared_name().to_string()));
        }
        self.envs.pop().expect("FunctionEnv in scope")
    }
}

impl FunctionEnv {
    fn new(args: VmIndex, id: Symbol, typ: ArcType, source_name: String) -> FunctionEnv {
        FunctionEnv {
            free_vars: Vec::new(),
            stack: ScopedMap::new(),
            stack_size: 0,
            function: CompiledFunction::new(args, id, typ, source_name),
            current_line: Line::from(0),
        }
    }

    fn emit(&mut self, instruction: Instruction) {
        if let Slide(0) = instruction {
            return;
        }

        let adjustment = instruction.adjust();
        debug!("{:?} {} {}", instruction, self.stack_size, adjustment);
        if adjustment > 0 {
            self.increase_stack(adjustment as VmIndex);
        } else {
            self.stack_size -= -adjustment as VmIndex;
        }

        self.function.instructions.push(instruction);
        self.function
            .debug_info
            .source_map
            .emit(self.function.instructions.len() - 1, self.current_line);
    }

    fn increase_stack(&mut self, adjustment: VmIndex) {
        use std::cmp::max;

        self.stack_size += adjustment;
        self.function.max_stack_size = max(self.function.max_stack_size, self.stack_size);
    }

    fn emit_call(&mut self, args: VmIndex, tail_position: bool) {
        let i = if tail_position {
            TailCall(args)
        } else {
            Call(args)
        };
        self.emit(i);
    }

    fn emit_field(&mut self, compiler: &mut Compiler, typ: &ArcType, field: &Symbol) -> Result<()> {
        let field_index = compiler.find_field(typ, field)
            .expect("ICE: Undefined field in field access");
        match field_index {
            FieldAccess::Index(i) => self.emit(GetOffset(i)),
            FieldAccess::Name => {
                let interned = compiler.intern(field.as_ref())?;
                let index = self.add_string_constant(interned);
                self.emit(GetField(index));
            }
        }
        Ok(())
    }


    fn add_record_map(&mut self, fields: Vec<Symbol>) -> VmIndex {
        match self.function.records.iter().position(|t| *t == fields) {
            Some(i) => i as VmIndex,
            None => {
                self.function.records.push(fields);
                (self.function.records.len() - 1) as VmIndex
            }
        }
    }

    fn add_string_constant(&mut self, s: InternedStr) -> VmIndex {
        match self.function.strings.iter().position(|t| *t == s) {
            Some(i) => i as VmIndex,
            None => {
                self.function.strings.push(s);
                (self.function.strings.len() - 1) as VmIndex
            }
        }
    }

    fn emit_string(&mut self, s: InternedStr) {
        let index = self.add_string_constant(s);
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

    fn push_stack_var(&mut self, compiler: &Compiler, s: Symbol) {
        self.increase_stack(1);
        self.new_stack_var(compiler, s)
    }

    fn new_stack_var(&mut self, _compiler: &Compiler, s: Symbol) {
        debug!("Push var: {:?} at {}", s, self.stack_size - 1);
        self.function.debug_info.local_map.emit(self.function.instructions.len(), s.clone());
        self.stack.insert(s, self.stack_size - 1);
    }

    fn exit_scope(&mut self, compiler: &Compiler) -> VmIndex {
        let mut count = 0;
        for x in self.stack.exit_scope() {
            count += 1;
            debug!("Pop var: {:?}", x);
        }
        count
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
                match *alias.typ {
                    Type::Variant(ref row) => {
                        row.row_iter()
                            .enumerate()
                            .find(|&(_, field)| field.name == *id)
                    }
                    _ => None,
                }
            })
            .next()
            .map(|(tag, field)| {
                Variable::Constructor(tag as VmTag, count_function_args(&field.typ))
            })
    }
}

pub struct Compiler<'a> {
    globals: &'a (CompilerEnv + 'a),
    vm: &'a GlobalVmState,
    symbols: SymbolModule<'a>,
    stack_constructors: ScopedMap<Symbol, ArcType>,
    stack_types: ScopedMap<Symbol, Alias<Symbol, ArcType>>,
    source: &'a Source<'a>,
    source_name: String,
    empty_symbol: Symbol,
}

impl<'a> KindEnv for Compiler<'a> {
    fn find_kind(&self, _type_name: &SymbolRef) -> Option<ArcKind> {
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
               mut symbols: SymbolModule<'a>,
               source: &'a Source<'a>,
               source_name: String)
               -> Compiler<'a> {
        Compiler {
            globals: globals,
            vm: vm,
            empty_symbol: symbols.symbol(""),
            symbols: symbols,
            stack_constructors: ScopedMap::new(),
            stack_types: ScopedMap::new(),
            source: source,
            source_name: source_name,
        }
    }

    fn intern(&mut self, s: &str) -> Result<InternedStr> {
        self.vm.intern(s)
    }

    fn find(&self, id: &Symbol, current: &mut FunctionEnvs) -> Option<Variable<VmIndex>> {
        let variable = self.stack_constructors
            .iter()
            .filter_map(|(_, typ)| match **typ {
                Type::Variant(ref row) => {
                    row.row_iter()
                        .enumerate()
                        .find(|&(_, field)| field.name == *id)
                }
                _ => None,
            })
            .next()
            .map(|(tag, field)| {
                Constructor(tag as VmIndex,
                            types::arg_iter(&field.typ).count() as VmIndex)
            })
            .or_else(|| {
                current.stack
                    .get(id)
                    .map(|&index| Stack(index))
                    .or_else(|| {
                        let i = current.envs.len() - 1;
                        let (rest, current) = current.envs.split_at_mut(i);
                        rest.iter()
                            .rev()
                            .filter_map(|env| {
                                env.stack
                                    .get(id)
                                    .map(|_| UpVar(current[0].upvar(id)))
                            })
                            .next()
                    })
            })
            .or_else(|| self.globals.find_var(&id));
        variable.map(|variable| match variable {
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
        })
    }

    fn find_field(&self, typ: &ArcType, field: &Symbol) -> Option<FieldAccess> {
        // Remove all type aliases to get the actual record type
        let typ = resolve::remove_aliases_cow(self, typ);
        let mut iter = typ.row_iter();
        match iter.by_ref().position(|f| f.name.name_eq(field)) {
            Some(index) => {
                for _ in iter.by_ref() {}
                Some(if **iter.current_type() == Type::EmptyRow {
                    // Non-polymorphic record, access by index
                    FieldAccess::Index(index as VmIndex)
                } else {
                    FieldAccess::Name
                })
            }
            None => None,
        }
    }

    fn find_tag(&self, typ: &ArcType, constructor: &Symbol) -> Option<VmTag> {
        match **resolve::remove_aliases_cow(self, typ) {
            Type::Variant(ref row) => {
                row.row_iter()
                    .enumerate()
                    .find(|&(_, field)| field.name == *constructor)
                    .map(|(tag, _)| tag as VmTag)
            }
            _ => None,
        }
    }

    /// Compiles an expression to a zero argument function which can be directly fed to the
    /// interpreter
    pub fn compile_expr(&mut self, expr: &CExpr) -> Result<CompiledFunction> {
        let mut env = FunctionEnvs::new();
        let id = self.empty_symbol.clone();
        let typ = Type::function(vec![],
                                 ArcType::from(expr.env_type_of(&self.globals).clone()));

        env.start_function(self, 0, id, typ);
        self.compile(expr, &mut env, true)?;
        let current_line = self.source.line_number_at_byte(expr.span.end);
        let FunctionEnv { function, .. } = env.end_function(self, current_line);
        Ok(function)
    }

    fn load_identifier(&self, id: &Symbol, function: &mut FunctionEnvs) -> Result<()> {
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
            Constructor(..) => {
                return Err(Error::Message(format!("Constructor `{}` is not fully applied", id)))
            }
        }
        Ok(())
    }

    fn compile(&mut self,
               mut expr: &CExpr,
               function: &mut FunctionEnvs,
               tail_position: bool)
               -> Result<()> {
        // Store a stack of expressions which need to be cleaned up after this "tailcall" loop is
        // done
        function.stack.enter_scope();
        // Don't update the current_line for macro expanded code as the lines in that code do not come
        // from this module
        if expr.span.expansion_id == NO_EXPANSION {
            function.current_line = self.source
                .line_number_at_byte(expr.span.start);
        }
        while let Some(next) = self.compile_(expr, function, tail_position)? {
            expr = next;
            if expr.span.expansion_id == NO_EXPANSION {
                function.current_line = self.source
                    .line_number_at_byte(expr.span.start);
            }
        }
        let count = function.exit_scope(self);
        function.emit(Slide(count));
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
                    Literal::Int(i) => function.emit(PushInt(i as isize)),
                    Literal::Byte(b) => function.emit(PushByte(b)),
                    Literal::Float(f) => function.emit(PushFloat(f)),
                    Literal::String(ref s) => function.emit_string(self.intern(&s)?),
                    Literal::Char(c) => function.emit(PushInt(c as isize)),
                }
            }
            Expr::Ident(ref id) => self.load_identifier(&id.name, function)?,
            Expr::IfElse(ref pred, ref if_true, ref if_false) => {
                self.compile(&**pred, function, false)?;
                let jump_index = function.function.instructions.len();
                function.emit(CJump(0));

                self.compile(&**if_false, function, tail_position)?;
                // The stack size of the true branch should not be increased by the false branch
                function.stack_size -= 1;
                let false_jump_index = function.function.instructions.len();
                function.emit(Jump(0));

                function.function.instructions[jump_index] =
                    CJump(function.function.instructions.len() as VmIndex);
                self.compile(&**if_true, function, tail_position)?;
                function.function.instructions[false_jump_index] =
                    Jump(function.function.instructions.len() as VmIndex);
            }
            Expr::Infix(ref lhs, ref op, ref rhs) => {
                if op.value.name.as_ref() == "&&" {
                    self.compile(&**lhs, function, false)?;
                    let lhs_end = function.function.instructions.len();
                    function.emit(CJump(lhs_end as VmIndex + 3));//Jump to rhs evaluation
                    function.emit(Construct { tag: 0, args: 0 });
                    function.emit(Jump(0));//lhs false, jump to after rhs
                    // Dont count the integer added added above as the next part of the code never
                    // pushed it
                    function.stack_size -= 1;
                    self.compile(&**rhs, function, tail_position)?;
                    // replace jump instruction
                    function.function.instructions[lhs_end + 2] =
                        Jump(function.function.instructions.len() as VmIndex);
                } else if op.value.name.as_ref() == "||" {
                    self.compile(&**lhs, function, false)?;
                    let lhs_end = function.function.instructions.len();
                    function.emit(CJump(0));
                    self.compile(&**rhs, function, tail_position)?;
                    function.emit(Jump(0));
                    function.function.instructions[lhs_end] =
                        CJump(function.function.instructions.len() as VmIndex);
                    function.emit(Construct { tag: 1, args: 0 });
                    // Dont count the integer above
                    function.stack_size -= 1;
                    let end = function.function.instructions.len();
                    function.function.instructions[end - 2] = Jump(end as VmIndex);
                } else {
                    let instr = match self.symbols.string(&op.value.name) {
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
                            self.load_identifier(&op.value.name, function)?;
                            Call(2)
                        }
                    };
                    self.compile(&**lhs, function, false)?;
                    self.compile(&**rhs, function, false)?;
                    function.emit(instr);
                }
            }
            Expr::LetBindings(ref bindings, ref body) => {
                self.stack_constructors.enter_scope();
                let stack_start = function.stack_size;
                // Index where the instruction to create the first closure should be at
                let first_index = function.function.instructions.len();
                let is_recursive = bindings.iter().all(|bind| bind.args.len() > 0);
                if is_recursive {
                    for bind in bindings.iter() {
                        // Add the NewClosure instruction before hand
                        // it will be fixed later
                        function.emit(NewClosure {
                            function_index: 0,
                            upvars: 0,
                        });
                        match bind.name.value {
                            Pattern::Ident(ref name) => {
                                function.new_stack_var(self, name.name.clone());
                            }
                            _ => panic!("ICE: Unexpected non identifer pattern"),
                        }
                    }
                }
                for (i, bind) in bindings.iter().enumerate() {

                    if is_recursive {
                        function.emit(Push(stack_start + i as VmIndex));
                        let name = match bind.name.value {
                            Pattern::Ident(ref name) => name,
                            _ => panic!("Lambda binds to non identifer pattern"),
                        };
                        let (function_index, vars, cf) =
                            self.compile_lambda(name, &bind.args, &bind.expr, function)?;
                        let offset = first_index + i;
                        function.function.instructions[offset] = NewClosure {
                            function_index: function_index,
                            upvars: vars,
                        };
                        function.emit(CloseClosure(vars));
                        function.stack_size -= vars;
                        function.function.inner_functions.push(cf);
                    } else {
                        self.compile(&bind.expr, function, false)?;
                        let typ = bind.expr.env_type_of(self);
                        self.compile_let_pattern(&bind.name.value, &typ, function)?;
                    }
                }
                return Ok(Some(body));
            }
            Expr::App(ref func, ref args) => {
                if let Expr::Ident(ref id) = func.value {
                    if let Some(Constructor(tag, num_args)) = self.find(&id.name, function) {
                        for arg in args.iter() {
                            self.compile(arg, function, false)?;
                        }
                        function.emit(Construct {
                            tag: tag,
                            args: num_args,
                        });
                        return Ok(None);
                    }
                }
                self.compile(&**func, function, false)?;
                for arg in args.iter() {
                    self.compile(arg, function, false)?;
                }
                function.emit_call(args.len() as VmIndex, tail_position);
            }
            Expr::Projection(ref expr, ref id, ref typ) => {
                self.compile(&**expr, function, false)?;
                debug!("{:?} {:?} {:?}", expr, id, typ);
                let typ = expr.env_type_of(self);
                debug!("Projection {}", types::display_type(&self.symbols, &typ));

                function.emit_field(self, &typ, id)?;
            }
            Expr::Match(ref expr, ref alts) => {
                self.compile(&**expr, function, false)?;
                // Indexes for each alternative for a successful match to the alternatives code
                let mut start_jumps = Vec::new();
                let typ = expr.env_type_of(self);
                let mut catch_all = false;
                // Emit a TestTag + Jump instuction for each alternative which jumps to the
                // alternatives code if TestTag is sucessesful
                for alt in alts.iter() {
                    match alt.pattern.value {
                        Pattern::Constructor(ref id, _) => {
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
                        Pattern::Record { .. } => {
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
                    self.load_identifier(&error_fn, function)?;
                    function.emit_string(self.intern("Non-exhaustive pattern")?);
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
                    function.stack.enter_scope();
                    match alt.pattern.value {
                        Pattern::Constructor(_, ref args) => {
                            function.function.instructions[start_index] =
                                CJump(function.function.instructions.len() as VmIndex);
                            function.emit(Split);
                            for arg in args.iter() {
                                function.push_stack_var(self, arg.name.clone());
                            }
                        }
                        Pattern::Record { .. } => {
                            let typ = &expr.env_type_of(self);
                            self.compile_let_pattern(&alt.pattern.value, typ, function)?;
                        }
                        Pattern::Ident(ref id) => {
                            function.function.instructions[start_index] =
                                Jump(function.function.instructions.len() as VmIndex);
                            function.new_stack_var(self, id.name.clone());
                        }
                    }
                    self.compile(&alt.expr, function, tail_position)?;
                    let count = function.exit_scope(self);
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
                for expr in a.exprs.iter() {
                    self.compile(expr, function, false)?;
                }
                function.emit(ConstructArray(a.exprs.len() as VmIndex));
            }
            Expr::Lambda(ref lambda) => {
                let (function_index, vars, cf) =
                    self.compile_lambda(&lambda.id, &lambda.args, &lambda.body, function)?;
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
                    self.stack_constructors.insert(bind.name.clone(), bind.alias.typ.clone());
                }
                return Ok(Some(expr));
            }
            Expr::Record { exprs: ref fields, .. } => {
                for field in fields {
                    match field.1 {
                        Some(ref field_expr) => self.compile(field_expr, function, false)?,
                        None => self.load_identifier(&field.0, function)?,
                    }
                }
                let index =
                    function.add_record_map(fields.iter().map(|field| field.0.clone()).collect());
                function.emit(ConstructRecord {
                    record: index,
                    args: fields.len() as u32,
                });
            }
            Expr::Tuple(ref exprs) => {
                for expr in exprs {
                    self.compile(expr, function, false)?;
                }
                function.emit(Construct {
                    tag: 0,
                    args: exprs.len() as u32,
                });
            }
            Expr::Block(ref exprs) => {
                let (last, inits) = exprs.split_last().expect("Expr in block");
                for expr in inits {
                    self.compile(expr, function, false)?;
                }
                self.compile(last, function, tail_position)?;
                function.emit(Slide(inits.len() as u32));
            }
            Expr::Error => panic!("ICE: Error expression found in the compiler"),
        }
        Ok(None)
    }

    fn compile_let_pattern(&mut self,
                           pattern: &Pattern<Symbol>,
                           pattern_type: &ArcType,
                           function: &mut FunctionEnvs)
                           -> Result<()> {
        match *pattern {
            Pattern::Ident(ref name) => {
                function.new_stack_var(self, name.name.clone());
            }
            Pattern::Record { ref types, ref fields, .. } => {
                let typ = resolve::remove_aliases(self, pattern_type.clone());
                // Insert all variant constructor into scope
                with_pattern_types(types, &typ, |name, alias| {
                    // FIXME: Workaround so that both the types name in this module and its global
                    // name are imported. Without this aliases may not be traversed properly
                    self.stack_types.insert(alias.name.clone(), alias.clone());
                    self.stack_types.insert(name.clone(), alias.clone());
                    self.stack_constructors.insert(alias.name.clone(), alias.typ.clone());
                    self.stack_constructors.insert(name.clone(), alias.typ.clone());
                });
                match *typ {
                    Type::Record(_) => {
                        let mut field_iter = typ.row_iter();
                        let number_of_fields = field_iter.by_ref().count();
                        let is_polymorphic = **field_iter.current_type() != Type::EmptyRow;
                        if fields.len() == 0 ||
                           (number_of_fields > 4 && number_of_fields / fields.len() >= 4) ||
                           is_polymorphic {
                            // For pattern matches on large records where only a few of the fields
                            // are used we instead emit a series of GetOffset instructions to avoid
                            // pushing a lot of unnecessary fields to the stack
                            // Polymorphic records also needs to generate field accesses as `Split`
                            // would push the fields in a different order depending on the record

                            // Add a dummy variable for the record itself so the correct number
                            // of slots are removed when exiting
                            function.new_stack_var(self, self.empty_symbol.clone());

                            let record_index = function.stack_size();
                            for pattern_field in fields {
                                function.emit(Push(record_index));
                                function.emit_field(self, &typ, &pattern_field.0)?;
                                function.new_stack_var(self,
                                                       pattern_field.1
                                                           .as_ref()
                                                           .unwrap_or(&pattern_field.0)
                                                           .clone());
                            }
                        } else {
                            function.emit(Split);
                            for field in typ.row_iter() {
                                let name = match fields.iter()
                                    .find(|tup| tup.0.name_eq(&field.name)) {
                                    Some(&(ref name, ref bind)) => {
                                        bind.as_ref().unwrap_or(name).clone()
                                    }
                                    None => self.empty_symbol.clone(),
                                };
                                function.push_stack_var(self, name);
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
            Pattern::Constructor(..) => panic!("constructor pattern in let"),
        }
        Ok(())
    }

    fn compile_lambda(&mut self,
                      id: &TypedIdent,
                      args: &[TypedIdent],
                      body: &SpannedExpr<Symbol>,
                      function: &mut FunctionEnvs)
                      -> Result<(VmIndex, VmIndex, CompiledFunction)> {
        function.start_function(self, args.len() as VmIndex, id.name.clone(), id.typ.clone());

        function.stack.enter_scope();
        for arg in args {
            function.push_stack_var(self, arg.name.clone());
        }
        self.compile(body, function, true)?;

        function.exit_scope(self);

        // Insert all free variables into the above globals free variables
        // if they arent in that lambdas scope
        let current_line = self.source.line_number_at_byte(body.span.end);
        let f = function.end_function(self, current_line);
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
    for field in types {
        let associated_type = typ.type_field_iter()
            .find(|type_field| type_field.name.name_eq(&field.0))
            .expect("Associated type to exist in record");
        f(&field.0, &associated_type.typ);
    }
}
