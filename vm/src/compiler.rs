use std::ops::{Deref, DerefMut};

use crate::base::{
    ast::{DisplayEnv, Typed, TypedIdent},
    kind::{ArcKind, KindEnv},
    pos::Line,
    resolve,
    scoped_map::ScopedMap,
    source::{FileMap, Source},
    symbol::{Symbol, SymbolData, SymbolModule, SymbolRef},
    types::{Alias, ArcType, BuiltinType, NullInterner, Type, TypeEnv, TypeExt},
};

use crate::{
    core::{self, is_primitive, CExpr, Expr, Literal, Pattern},
    interner::InternedStr,
    source_map::{LocalMap, SourceMap},
    types::*,
    vm::GlobalVmState,
    Error, Result,
};

use self::Variable::*;

#[derive(Clone, Debug)]
pub enum Variable<G> {
    Stack(VmIndex),
    Constructor(VmTag, VmIndex),
    UpVar(G),
}

/// Field accesses on records can either be by name in the case of polymorphic records or by offset
/// when the record is non-polymorphic (which is faster)
enum FieldAccess {
    Name,
    Index(VmIndex),
}

#[derive(Debug, Default, PartialEq, Eq, Hash, Clone)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive",
    serde(
        deserialize_state = "crate::serialization::DeSeed<'gc>",
        de_parameters = "'gc"
    )
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(serialize_state = "crate::serialization::SeSeed")
)]
pub struct UpvarInfo {
    pub name: String,
    #[cfg_attr(
        feature = "serde_derive",
        serde(state_with = "crate::serialization::borrow")
    )]
    pub typ: ArcType,
}

#[derive(Debug, Default, PartialEq, Eq, Hash, Clone)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive",
    serde(
        deserialize_state = "crate::serialization::DeSeed<'gc>",
        de_parameters = "'gc"
    )
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(serialize_state = "crate::serialization::SeSeed")
)]
pub struct DebugInfo {
    /// Maps instruction indexes to the line that spawned them
    pub source_map: SourceMap,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub local_map: LocalMap,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub upvars: Vec<UpvarInfo>,
    pub source_name: String,
}

#[derive(Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive_state",
    serde(
        deserialize_state = "crate::serialization::DeSeed<'gc>",
        de_parameters = "'gc"
    )
)]
#[cfg_attr(
    feature = "serde_derive_state",
    serde(serialize_state = "crate::serialization::SeSeed")
)]
pub struct CompiledModule {
    /// Storage for globals which are needed by the module which is currently being compiled
    #[cfg_attr(
        feature = "serde_derive",
        serde(state_with = "crate::serialization::borrow")
    )]
    pub module_globals: Vec<Symbol>,
    #[cfg_attr(
        feature = "serde_derive",
        serde(state_with = "crate::serialization::borrow")
    )]
    pub function: CompiledFunction,
}

#[derive(Debug, Eq, PartialEq, Hash)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive_state",
    serde(
        deserialize_state = "crate::serialization::DeSeed<'gc>",
        de_parameters = "'gc"
    )
)]
#[cfg_attr(
    feature = "serde_derive_state",
    serde(serialize_state = "crate::serialization::SeSeed")
)]
pub struct CompiledFunction {
    pub args: VmIndex,
    /// The maximum possible number of stack slots needed for this function
    pub max_stack_size: VmIndex,

    #[cfg_attr(
        feature = "serde_derive",
        serde(state_with = "crate::serialization::borrow")
    )]
    pub id: Symbol,

    #[cfg_attr(
        feature = "serde_derive",
        serde(state_with = "crate::serialization::borrow")
    )]
    pub typ: ArcType,
    pub instructions: Vec<Instruction>,

    #[cfg_attr(feature = "serde_derive_state", serde(state))]
    pub inner_functions: Vec<CompiledFunction>,

    #[cfg_attr(feature = "serde_derive_state", serde(state))]
    pub strings: Vec<InternedStr>,

    #[cfg_attr(
        feature = "serde_derive",
        serde(state_with = "crate::serialization::borrow")
    )]
    pub records: Vec<Vec<Symbol>>,

    #[cfg_attr(feature = "serde_derive_state", serde(state))]
    pub debug_info: DebugInfo,
}

impl From<CompiledFunction> for CompiledModule {
    fn from(function: CompiledFunction) -> Self {
        CompiledModule {
            module_globals: Vec::new(),
            function,
        }
    }
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
            records: Vec::new(),
            debug_info: DebugInfo {
                source_map: SourceMap::new(),
                local_map: LocalMap::new(),
                upvars: Vec::new(),
                source_name: source_name,
            },
        }
    }
}

struct FunctionEnv {
    /// The variables currently in scope in the this function.
    stack: ScopedMap<Symbol, (VmIndex, ArcType)>,
    /// The current size of the stack. Not the same as `stack.len()`.
    /// The current size of the stack. Not the same as `stack.len()`.
    stack_size: VmIndex,
    /// The variables which this function takes from the outer scope
    free_vars: Vec<(Symbol, ArcType)>,
    /// The line where instructions are currently being emitted
    current_line: Line,
    emit_debug_info: bool,
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

    fn start_function(&mut self, compiler: &mut Compiler, args: VmIndex, id: Symbol, typ: ArcType) {
        compiler.stack_types.enter_scope();
        self.envs.push(FunctionEnv::new(
            args,
            id,
            typ,
            compiler.source_name.clone(),
            compiler.emit_debug_info,
        ));
    }

    fn end_function(&mut self, compiler: &mut Compiler, current_line: Option<Line>) -> FunctionEnv {
        compiler.stack_types.exit_scope();
        self.function.instructions.push(Instruction::Return);
        let instructions = self.function.instructions.len();

        if compiler.emit_debug_info {
            self.function
                .debug_info
                .source_map
                .close(instructions, current_line);

            let upvars_are_globals = self.envs.len() == 1;
            if !upvars_are_globals {
                let function = &mut **self;
                function
                    .function
                    .debug_info
                    .upvars
                    .extend(
                        function
                            .free_vars
                            .iter()
                            .map(|&(ref name, ref typ)| UpvarInfo {
                                name: name.declared_name().to_string(),
                                typ: typ.clone(),
                            }),
                    );
            }
        }

        self.envs.pop().expect("FunctionEnv in scope")
    }
}

impl FunctionEnv {
    fn new(
        args: VmIndex,
        id: Symbol,
        typ: ArcType,
        source_name: String,
        emit_debug_info: bool,
    ) -> FunctionEnv {
        FunctionEnv {
            free_vars: Vec::new(),
            stack: ScopedMap::new(),
            stack_size: 0,
            function: CompiledFunction::new(args, id, typ, source_name),
            current_line: Line::from(0),
            emit_debug_info,
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

        if self.emit_debug_info {
            self.function
                .debug_info
                .source_map
                .emit(self.function.instructions.len() - 1, self.current_line);
        }
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
        let field_index = compiler
            .find_field(typ, field)
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

    fn upvar(&mut self, s: &Symbol, typ: &ArcType) -> VmIndex {
        match self.free_vars.iter().position(|t| t.0 == *s) {
            Some(index) => index as VmIndex,
            None => {
                self.free_vars.push((s.clone(), typ.clone()));
                (self.free_vars.len() - 1) as VmIndex
            }
        }
    }

    fn stack_size(&mut self) -> VmIndex {
        self.stack_size as VmIndex
    }

    fn push_stack_var(&mut self, compiler: &Compiler, s: Symbol, typ: ArcType) {
        self.increase_stack(1);
        self.new_stack_var(compiler, s, typ)
    }

    fn new_stack_var(&mut self, compiler: &Compiler, s: Symbol, typ: ArcType) {
        debug!("Push var: {:?} at {}", s, self.stack_size - 1);
        let index = self.stack_size - 1;
        if self.emit_debug_info && compiler.empty_symbol != s {
            self.function.debug_info.local_map.emit(
                self.function.instructions.len(),
                index,
                s.clone(),
                typ.clone(),
            );
        }
        self.stack.insert(s, (index, typ));
    }

    fn exit_scope(&mut self, compiler: &Compiler) -> VmIndex {
        let mut count = 0;
        for x in self.stack.exit_scope() {
            count += 1;
            debug!("Pop var: ({:?}, {:?})", x.0, (x.1).0);
            if self.emit_debug_info && compiler.empty_symbol != x.0 {
                self.function
                    .debug_info
                    .local_map
                    .close(self.function.instructions.len());
            }
        }
        count
    }
}

pub trait CompilerEnv: TypeEnv {
    fn find_var(&self, id: &Symbol) -> Option<(Variable<Symbol>, ArcType)>;
}

impl CompilerEnv for TypeInfos {
    fn find_var(&self, id: &Symbol) -> Option<(Variable<Symbol>, ArcType)> {
        fn count_function_args(typ: &ArcType) -> VmIndex {
            match typ.as_function() {
                Some((_, ret)) => 1 + count_function_args(ret),
                None => 0,
            }
        }

        self.id_to_type
            .iter()
            .filter_map(|(_, ref alias)| match **alias.unresolved_type() {
                Type::Variant(ref row) => row
                    .row_iter()
                    .enumerate()
                    .find(|&(_, field)| field.name == *id),
                _ => None,
            })
            .next()
            .map(|(tag, field)| {
                (
                    Variable::Constructor(tag as VmTag, count_function_args(&field.typ)),
                    field.typ.clone(),
                )
            })
    }
}

pub struct Compiler<'a> {
    globals: &'a (dyn CompilerEnv<Type = ArcType> + 'a),
    vm: &'a GlobalVmState,
    symbols: SymbolModule<'a>,
    stack_types: ScopedMap<Symbol, Alias<Symbol, ArcType>>,
    source: &'a FileMap,
    source_name: String,
    emit_debug_info: bool,
    empty_symbol: Symbol,
    hole: ArcType,
}

impl<'a> KindEnv for Compiler<'a> {
    fn find_kind(&self, _type_name: &SymbolRef) -> Option<ArcKind> {
        None
    }
}

impl<'a> TypeEnv for Compiler<'a> {
    type Type = ArcType;

    fn find_type(&self, _id: &SymbolRef) -> Option<ArcType> {
        None
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<Alias<Symbol, ArcType>> {
        self.stack_types.get(id).cloned()
    }
}

impl<'a, T: CompilerEnv> CompilerEnv for &'a T {
    fn find_var(&self, s: &Symbol) -> Option<(Variable<Symbol>, ArcType)> {
        (**self).find_var(s)
    }
}

impl<'a> Compiler<'a> {
    pub fn new(
        globals: &'a (dyn CompilerEnv<Type = ArcType> + 'a),
        vm: &'a GlobalVmState,
        mut symbols: SymbolModule<'a>,
        source: &'a FileMap,
        source_name: String,
        emit_debug_info: bool,
    ) -> Compiler<'a> {
        Compiler {
            globals: globals,
            vm: vm,
            empty_symbol: symbols.simple_symbol(""),
            symbols: symbols,
            stack_types: ScopedMap::new(),
            source: source,
            source_name: source_name,
            emit_debug_info,
            hole: Type::hole(),
        }
    }

    fn intern(&mut self, s: &str) -> Result<InternedStr> {
        self.vm.intern(s)
    }

    fn find(&self, id: &Symbol, current: &mut FunctionEnvs) -> Option<Variable<VmIndex>> {
        current
            .stack
            .get(id)
            .map(|&(index, _)| Stack(index))
            .or_else(|| {
                let i = current.envs.len() - 1;
                let (rest, current) = current.envs.split_at_mut(i);
                rest.iter()
                    .rev()
                    .filter_map(|env| {
                        env.stack
                            .get(id)
                            .map(|&(_, ref typ)| UpVar(current[0].upvar(id, typ)))
                    })
                    .next()
            })
            .or_else(|| {
                self.globals
                    .find_var(&id)
                    .map(|(variable, typ)| match variable {
                        Stack(i) => Stack(i),
                        UpVar(id) => UpVar(current.upvar(&id, &typ)),
                        Constructor(tag, args) => Constructor(tag, args),
                    })
            })
    }

    fn find_field(&self, typ: &ArcType, field: &Symbol) -> Option<FieldAccess> {
        // Remove all type aliases to get the actual record type
        let typ = resolve::remove_aliases_cow(self, &mut NullInterner, typ);
        let mut iter = typ.remove_forall().row_iter();
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

    fn find_tag(&self, typ: &ArcType, constructor: &Symbol) -> Option<FieldAccess> {
        let typ = resolve::remove_aliases_cow(self, &mut NullInterner, typ);
        self.find_resolved_tag(&typ, constructor)
    }

    fn find_resolved_tag(&self, typ: &ArcType, constructor: &Symbol) -> Option<FieldAccess> {
        match **typ {
            Type::Variant(ref row) => {
                let mut iter = row.row_iter();
                match iter.position(|field| field.name.name_eq(constructor)) {
                    Some(index) => {
                        for _ in iter.by_ref() {}
                        Some(if **iter.current_type() == Type::EmptyRow {
                            // Non-polymorphic variant, access by index
                            FieldAccess::Index(index as VmIndex)
                        } else {
                            FieldAccess::Name
                        })
                    }
                    None => None,
                }
            }
            _ => None,
        }
    }

    /// Compiles an expression to a zero argument function which can be directly fed to the
    /// interpreter
    pub fn compile_expr(&mut self, expr: CExpr) -> Result<CompiledModule> {
        let mut env = FunctionEnvs::new();
        let id = self.empty_symbol.clone();
        let typ = expr.env_type_of(&self.globals);

        env.start_function(self, 0, id, typ);
        info!("COMPILING: {}", expr);
        self.compile(&expr, &mut env, true)?;
        let current_line = self.source.line_number_at_byte(expr.span().end());
        let FunctionEnv {
            function,
            free_vars,
            ..
        } = env.end_function(self, current_line);
        Ok(CompiledModule {
            module_globals: free_vars.into_iter().map(|(symbol, _)| symbol).collect(),
            function,
        })
    }

    fn load_identifier(&self, id: &Symbol, function: &mut FunctionEnvs) -> Result<()> {
        debug!("Load {}", id);
        match self
            .find(id, function)
            .unwrap_or_else(|| ice!("Undefined variable `{:?}` in {}", id, self.source_name,))
        {
            Stack(index) => function.emit(Push(index)),
            UpVar(index) => function.emit(PushUpVar(index)),
            // Zero argument constructors can be compiled as integers
            Constructor(tag, 0) => function.emit(ConstructVariant { tag: tag, args: 0 }),
            Constructor(..) => {
                return Err(Error::Message(format!(
                    "Constructor `{}` is not fully applied",
                    id
                )));
            }
        }
        Ok(())
    }

    fn update_line(&mut self, function: &mut FunctionEnvs, expr: CExpr) {
        // Don't update the current_line for macro expanded code as the lines in that code do not
        // come from this module
        if let Some(current_line) = self.source.line_number_at_byte(expr.span().start()) {
            function.current_line = current_line;
        }
    }

    fn compile(
        &mut self,
        mut expr: CExpr,
        function: &mut FunctionEnvs,
        tail_position: bool,
    ) -> Result<()> {
        // Store a stack of expressions which need to be cleaned up after this "tailcall" loop is
        // done
        function.stack.enter_scope();

        self.update_line(function, expr);

        while let Some(next) = self.compile_(expr, function, tail_position)? {
            expr = next;
            self.update_line(function, expr);
        }
        let count = function.exit_scope(self);
        function.emit(Slide(count));
        Ok(())
    }

    fn compile_<'e>(
        &mut self,
        expr: CExpr<'e>,
        function: &mut FunctionEnvs,
        tail_position: bool,
    ) -> Result<Option<CExpr<'e>>> {
        match *expr {
            Expr::Const(ref lit, _) => match *lit {
                Literal::Int(i) => function.emit(PushInt(i)),
                Literal::Byte(b) => function.emit(PushByte(b)),
                Literal::Float(f) => function.emit(PushFloat(f.into_inner().into())),
                Literal::String(ref s) => function.emit_string(self.intern(&s)?),
                Literal::Char(c) => function.emit(PushInt(u32::from(c).into())),
            },
            Expr::Ident(ref id, _) => self.load_identifier(&id.name, function)?,
            Expr::Let(ref let_binding, ref body) => {
                let stack_start = function.stack_size;
                // Index where the instruction to create the first closure should be at
                let first_index = function.function.instructions.len();
                match let_binding.expr {
                    core::Named::Expr(ref bind_expr) => {
                        self.compile(bind_expr, function, false)?;
                        function.new_stack_var(
                            self,
                            let_binding.name.name.clone(),
                            let_binding.name.typ.clone(),
                        );
                    }
                    core::Named::Recursive(ref closures) => {
                        for closure in closures.iter() {
                            // Add the NewClosure/NewRecord instruction before hand
                            // it will be fixed later
                            if closure.args.is_empty() {
                                function.emit(NewRecord { args: 0, record: 0 });
                            } else {
                                function.emit(NewClosure {
                                    function_index: 0,
                                    upvars: 0,
                                });
                            }
                            function.new_stack_var(
                                self,
                                closure.name.name.clone(),
                                closure.name.typ.clone(),
                            );
                        }

                        for (i, closure) in closures.iter().enumerate() {
                            if let Some(current_line) = self.source.line_number_at_byte(closure.pos)
                            {
                                function.current_line = current_line;
                            }
                            function.stack.enter_scope();

                            let offset = first_index + i;

                            function.emit(Push(stack_start + i as VmIndex));

                            if closure.args.is_empty() {
                                self.compile(closure.expr, function, false)?;

                                let construct_index = function
                                    .function
                                    .instructions
                                    .iter()
                                    .rposition(|inst| match inst {
                                        Slide(_) |
                                        Jump(_) => false,
                                        _ => true,
                                    }).unwrap_or_else(|| {
                                        ice!("Expected record as last expression of recursive binding")
                                    });
                                match function.function.instructions[construct_index] {
                                    ConstructRecord { record, args } => {
                                        function.stack_size -= 1;
                                        function.function.instructions[offset] =
                                            NewRecord { record, args };
                                        function.function.instructions[construct_index] = CloseData { index: stack_start + i as VmIndex };
                                    }
                                    ConstructVariant { tag, args } => {
                                        function.stack_size -= 1;
                                        function.function.instructions[offset] =
                                            NewVariant { tag, args };
                                        function.function.instructions[construct_index] = CloseData { index: stack_start + i as VmIndex };
                                    }
                                    x => ice!(
                                        "Expected record as last expression of recursive binding `{}`: {:?}\n{}", closure.name.name, x, closure.expr
                                    ),
                                }
                            } else {
                                let (function_index, vars, cf) = self.compile_lambda(
                                    &closure.name,
                                    &closure.args,
                                    &closure.expr,
                                    function,
                                )?;
                                function.function.instructions[offset] = NewClosure {
                                    function_index: function_index,
                                    upvars: vars,
                                };
                                function.emit(CloseClosure(vars));
                                function.stack_size -= vars;
                                function.function.inner_functions.push(cf);
                            }

                            function.exit_scope(self);
                        }
                    }
                }
                return Ok(Some(body));
            }
            Expr::Call(func, args) => {
                if let Expr::Ident(ref id, _) = *func {
                    if is_primitive(&id.name) && id.name.declared_name() != "#error" {
                        self.compile_primitive(&id.name, args, function, tail_position)?;
                        return Ok(None);
                    }

                    if let Some(Constructor(tag, num_args)) = self.find(&id.name, function) {
                        for arg in args {
                            self.compile(arg, function, false)?;
                        }
                        function.emit(ConstructVariant {
                            tag: tag,
                            args: num_args,
                        });
                        return Ok(None);
                    }
                }
                self.compile(func, function, false)?;
                for arg in args.iter() {
                    self.compile(arg, function, false)?;
                }
                function.emit_call(args.len() as VmIndex, tail_position);
            }
            Expr::Match(ref scrutinee, ref alts) => {
                self.compile(scrutinee, function, false)?;
                // Indexes for each alternative for a successful match to the alternatives code
                let mut start_jumps = Vec::new();
                let typ = alts[0].pattern.env_type_of(self);
                let typ = resolve::remove_aliases_cow(self, &mut NullInterner, typ.remove_forall());
                // Emit a TestTag + Jump instuction for each alternative which jumps to the
                // alternatives code if TestTag is sucessesful
                for alt in alts.iter() {
                    match alt.pattern {
                        Pattern::Constructor(ref id, _) => {
                            let tag = self.find_resolved_tag(&typ, &id.name).unwrap_or_else(|| {
                                ice!(
                                    "ICE: Could not find tag for {}::{} when matching on \
                                     expression:\n{}",
                                    typ,
                                    self.symbols.string(&id.name),
                                    scrutinee
                                )
                            });

                            match tag {
                                FieldAccess::Index(tag) => function.emit(TestTag(tag)),
                                FieldAccess::Name => {
                                    let interned = self.intern(id.name.as_ref())?;
                                    let index = function.add_string_constant(interned);
                                    function.emit(TestPolyTag(index));
                                }
                            }

                            start_jumps.push(function.function.instructions.len());
                            function.emit(CJump(0));
                        }
                        Pattern::Record { .. } => {
                            start_jumps.push(function.function.instructions.len());
                        }
                        Pattern::Ident(_) => {
                            start_jumps.push(function.function.instructions.len());
                            function.emit(Jump(0));
                        }
                        Pattern::Literal(ref l) => {
                            let lhs_i = function.stack_size() - 1;
                            match *l {
                                Literal::Byte(b) => {
                                    function.emit(Push(lhs_i));
                                    function.emit(PushByte(b));
                                    function.emit(ByteEQ);
                                }
                                Literal::Int(i) => {
                                    function.emit(Push(lhs_i));
                                    function.emit(PushInt(i));
                                    function.emit(IntEQ);
                                }
                                Literal::Char(ch) => {
                                    function.emit(Push(lhs_i));
                                    function.emit(PushInt(u32::from(ch).into()));
                                    function.emit(IntEQ);
                                }
                                Literal::Float(f) => {
                                    function.emit(Push(lhs_i));
                                    function.emit(PushFloat(f.into_inner().into()));
                                    function.emit(FloatEQ);
                                }
                                Literal::String(ref s) => {
                                    let prim_symbol = self.symbols.symbol(SymbolData {
                                        global: true,
                                        name: "std.prim",
                                        location: None,
                                    });
                                    self.load_identifier(&prim_symbol, function)?;
                                    let prim_type = self.globals.find_type(&prim_symbol).unwrap();
                                    let string_eq_symbol = self.symbols.simple_symbol("string_eq");
                                    function.emit_field(self, &prim_type, &string_eq_symbol)?;
                                    let lhs_i = function.stack_size() - 2;
                                    function.emit(Push(lhs_i));
                                    function.emit_string(self.intern(&s)?);
                                    function.emit(Call(2));
                                }
                            };
                            start_jumps.push(function.function.instructions.len());
                            function.emit(CJump(0));
                        }
                    }
                }
                // Indexes for each alternative from the end of the alternatives code to code
                // after the alternative
                let mut end_jumps = Vec::new();
                for (alt, &start_index) in alts.iter().zip(start_jumps.iter()) {
                    function.stack.enter_scope();
                    match alt.pattern {
                        Pattern::Constructor(_, ref args) => {
                            function.function.instructions[start_index] =
                                CJump(function.function.instructions.len() as VmIndex);
                            function.emit(Split);
                            for arg in args.iter() {
                                function.push_stack_var(self, arg.name.clone(), arg.typ.clone());
                            }
                        }
                        Pattern::Record { .. } => {
                            let typ = &scrutinee.env_type_of(self);
                            self.compile_let_pattern(&alt.pattern, typ, function)?;
                        }
                        Pattern::Ident(ref id) => {
                            function.function.instructions[start_index] =
                                Jump(function.function.instructions.len() as VmIndex);
                            function.new_stack_var(self, id.name.clone(), id.typ.clone());
                        }
                        Pattern::Literal(_) => {
                            function.function.instructions[start_index] =
                                CJump(function.function.instructions.len() as VmIndex);
                            // Add a dummy variable to mark where the literal itself is stored
                            function.new_stack_var(self, self.empty_symbol.clone(), Type::hole());
                        }
                    }
                    self.compile(&alt.expr, function, tail_position)?;
                    let count = function.exit_scope(self);
                    function.emit(Slide(count));
                    end_jumps.push(function.function.instructions.len());
                    function.emit(Jump(0));
                }
                for &index in end_jumps.iter() {
                    function.function.instructions[index] =
                        Jump(function.function.instructions.len() as VmIndex);
                }
            }
            Expr::Data(ref id, exprs, _) => {
                for expr in exprs {
                    self.compile(expr, function, false)?;
                }
                let typ =
                    resolve::remove_aliases_cow(self, &mut NullInterner, &id.typ.remove_forall());
                match **typ.remove_forall() {
                    Type::Record(_) => {
                        let index = function.add_record_map(
                            typ.row_iter().map(|field| field.name.clone()).collect(),
                        );
                        function.emit(ConstructRecord {
                            record: index,
                            args: exprs.len() as u32,
                        });
                    }
                    Type::App(ref array, _) if **array == Type::Builtin(BuiltinType::Array) => {
                        function.emit(ConstructArray(exprs.len() as VmIndex));
                    }
                    Type::Variant(_) => {
                        match self.find_tag(&typ, &id.name).unwrap_or_else(|| {
                            ice!("Variant `{}` not found in {:#?}", id.name, typ)
                        }) {
                            FieldAccess::Index(tag) => function.emit(ConstructVariant {
                                tag,
                                args: exprs.len() as u32,
                            }),
                            FieldAccess::Name => {
                                let variant_name = self.intern(&id.name.definition_name())?;
                                let tag = function.add_string_constant(variant_name);
                                function.emit(ConstructPolyVariant {
                                    tag,
                                    args: exprs.len() as u32,
                                });
                            }
                        }
                    }
                    _ => ice!("ICE: Unexpected data type for {}: {}", id.name, typ),
                }
            }

            Expr::Cast(expr, _) => return Ok(Some(expr)),
        }
        Ok(None)
    }

    fn compile_primitive(
        &mut self,
        op: &Symbol,
        args: &[Expr],
        function: &mut FunctionEnvs,
        tail_position: bool,
    ) -> Result<()> {
        assert!(args.len() == 2, "Invalid primitive application: {}", op);
        let lhs = &args[0];
        let rhs = &args[1];
        if op.as_str() == "&&" {
            self.compile(lhs, function, false)?;
            let lhs_end = function.function.instructions.len();
            function.emit(CJump(lhs_end as VmIndex + 3)); //Jump to rhs evaluation
            function.emit(ConstructVariant { tag: 0, args: 0 });
            function.emit(Jump(0)); //lhs false, jump to after rhs
                                    // Dont count the integer added added above as the next part of the code never
                                    // pushed it
            function.stack_size -= 1;
            self.compile(rhs, function, tail_position)?;
            // replace jump instruction
            function.function.instructions[lhs_end + 2] =
                Jump(function.function.instructions.len() as VmIndex);
        } else if op.as_str() == "||" {
            self.compile(lhs, function, false)?;
            let lhs_end = function.function.instructions.len();
            function.emit(CJump(0));
            self.compile(rhs, function, tail_position)?;
            function.emit(Jump(0));
            function.function.instructions[lhs_end] =
                CJump(function.function.instructions.len() as VmIndex);
            function.emit(ConstructVariant { tag: 1, args: 0 });
            // Dont count the integer above
            function.stack_size -= 1;
            let end = function.function.instructions.len();
            function.function.instructions[end - 2] = Jump(end as VmIndex);
        } else {
            let instr = match self.symbols.string(op) {
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
                    self.load_identifier(op, function)?;
                    Call(2)
                }
            };
            self.compile(lhs, function, false)?;
            self.compile(rhs, function, false)?;
            function.emit(instr);
        }
        Ok(())
    }

    fn compile_let_pattern(
        &mut self,
        pattern: &Pattern,
        pattern_type: &ArcType,
        function: &mut FunctionEnvs,
    ) -> Result<()> {
        match *pattern {
            Pattern::Ident(ref name) => {
                function.new_stack_var(self, name.name.clone(), pattern_type.clone());
            }
            Pattern::Record { ref fields, .. } => {
                let typ = resolve::remove_aliases(
                    self,
                    &mut NullInterner,
                    pattern_type.remove_forall().clone(),
                );
                let typ = typ.remove_forall();
                match **typ {
                    Type::Record(_) => {
                        let mut field_iter = typ.row_iter();
                        let number_of_fields = field_iter.by_ref().count();
                        let is_polymorphic = **field_iter.current_type() != Type::EmptyRow;
                        if fields.len() == 0
                            || (number_of_fields > 4 && number_of_fields / fields.len() >= 4)
                            || is_polymorphic
                        {
                            // For pattern matches on large records where only a few of the fields
                            // are used we instead emit a series of GetOffset instructions to avoid
                            // pushing a lot of unnecessary fields to the stack
                            // Polymorphic records also needs to generate field accesses as `Split`
                            // would push the fields in a different order depending on the record

                            // Add a dummy variable for the record itself so the correct number
                            // of slots are removed when exiting
                            function.new_stack_var(
                                self,
                                self.empty_symbol.clone(),
                                self.hole.clone(),
                            );

                            let record_index = function.stack_size() - 1;
                            for pattern_field in fields {
                                function.emit(Push(record_index));
                                function.emit_field(self, &typ, &pattern_field.0.name)?;

                                let field_name = pattern_field
                                    .1
                                    .as_ref()
                                    .unwrap_or(&pattern_field.0.name)
                                    .clone();
                                function.new_stack_var(
                                    self,
                                    field_name,
                                    pattern_field.0.typ.clone(),
                                );
                            }
                        } else {
                            function.emit(Split);
                            for field in typ.row_iter() {
                                let (name, typ) =
                                    match fields.iter().find(|tup| tup.0.name.name_eq(&field.name))
                                    {
                                        Some(&(ref name, ref bind)) => (
                                            bind.as_ref().unwrap_or(&name.name).clone(),
                                            field.typ.clone(),
                                        ),
                                        None => (self.empty_symbol.clone(), self.hole.clone()),
                                    };
                                function.push_stack_var(self, name, typ);
                            }
                        }
                    }
                    _ => ice!("Expected record, got {} at {}", typ, pattern),
                }
            }
            Pattern::Constructor(..) => ice!("constructor pattern in let"),
            Pattern::Literal(_) => ice!("literal pattern in let"),
        }
        Ok(())
    }

    fn compile_lambda(
        &mut self,
        id: &TypedIdent,
        args: &[TypedIdent],
        body: CExpr,
        function: &mut FunctionEnvs,
    ) -> Result<(VmIndex, VmIndex, CompiledFunction)> {
        debug!("Compile function {}", id.name);
        function.start_function(self, args.len() as VmIndex, id.name.clone(), id.typ.clone());

        function.stack.enter_scope();
        for arg in args {
            function.push_stack_var(self, arg.name.clone(), arg.typ.clone());
        }
        self.compile(body, function, true)?;

        function.exit_scope(self);

        // Insert all free variables into the above globals free variables
        // if they arent in that lambdas scope
        let current_line = self.source.line_number_at_byte(body.span().end());
        let f = function.end_function(self, current_line);
        for &(ref var, _) in f.free_vars.iter() {
            match self
                .find(var, function)
                .unwrap_or_else(|| panic!("free_vars: find {}", var))
            {
                Stack(index) => {
                    debug!("Load stack {}", var);
                    function.emit(Push(index))
                }
                UpVar(index) => {
                    debug!("Load upvar {}", var);
                    function.emit(PushUpVar(index))
                }
                _ => ice!("Free variables can only be on the stack or another upvar"),
            }
        }
        let function_index = function.function.inner_functions.len() as VmIndex;
        let free_vars = f.free_vars.len() as VmIndex;
        let FunctionEnv { function, .. } = f;
        debug!("End compile function {}", id.name);
        Ok((function_index, free_vars, function))
    }
}

#[cfg(all(test, feature = "test"))]
mod tests {
    use super::*;

    use crate::{
        base::symbol::Symbols,
        core::{grammar::ExprParser, Allocator},
        vm::GlobalVmState,
    };

    fn verify_instructions<'a>(
        compiled_function: &CompiledFunction,
        instructions: &mut impl Iterator<Item = &'a [Instruction]>,
    ) {
        assert_eq!(
            compiled_function.instructions,
            instructions.next().expect("Instructions")
        );
        for func in &compiled_function.inner_functions {
            verify_instructions(func, instructions);
        }
    }

    fn assert_instructions(source: &str, instructions: &[&[Instruction]]) {
        let mut symbols = Symbols::new();
        let global_allocator = Allocator::new();
        let global = ExprParser::new()
            .parse(&mut symbols, &global_allocator, source)
            .unwrap();

        let globals = TypeInfos::new();
        let vm_state = GlobalVmState::new();
        let source = FileMap::new("".to_string().into(), "".to_string());
        let mut compiler = Compiler::new(
            &globals,
            &vm_state,
            SymbolModule::new("test".into(), &mut symbols),
            &source,
            "test".into(),
            false,
        );
        let module = compiler.compile_expr(&global).unwrap();

        verify_instructions(&module.function, &mut instructions.iter().cloned());
    }

    #[test]
    fn recursive_record() {
        let _ = ::env_logger::try_init();

        assert_instructions(
            "rec let a = { b }
             rec let b = { a }
             in b",
            &[&[
                NewRecord { args: 1, record: 0 },
                NewRecord { args: 1, record: 1 },
                Push(0),
                Push(1),
                CloseData { index: 0 },
                Push(1),
                Push(0),
                CloseData { index: 1 },
                Push(1),
                Slide(2),
                Return,
            ]],
        )
    }

    #[test]
    fn recursive_record_with_functions() {
        let _ = ::env_logger::try_init();

        assert_instructions(
            "rec let a =
                rec let f x = b
                in { f }
             rec let b =
                rec let f y = a
                in { f }
             in b",
            &[
                &[
                    NewRecord { args: 1, record: 0 },
                    NewRecord { args: 1, record: 0 },
                    // a
                    Push(0),
                    NewClosure {
                        function_index: 0,
                        upvars: 1,
                    },
                    Push(3),
                    Push(1),
                    CloseClosure(1),
                    Push(3),
                    CloseData { index: 0 },
                    Slide(1), // Remove closure
                    // b
                    Push(1),
                    NewClosure {
                        function_index: 1,
                        upvars: 1,
                    },
                    Push(4),
                    Push(0),
                    CloseClosure(1),
                    Push(4),
                    CloseData { index: 1 },
                    Slide(1), // Remove closure
                    // body
                    Push(1),
                    Slide(2),
                    Return,
                ],
                &[PushUpVar(0), Return],
                &[PushUpVar(0), Return],
            ],
        )
    }
}
