use std::{
    any::{Any, TypeId},
    result::Result as StdResult,
    string::String as StdString,
    sync::{atomic::AtomicUsize, Arc, Mutex, RwLock},
    usize,
};

#[cfg(feature = "serde_derive_state")]
use serde::de::DeserializeState;

use crate::base::{
    ast,
    fnv::FnvMap,
    kind::{ArcKind, Kind, KindEnv},
    metadata::{Metadata, MetadataEnv},
    symbol::{Name, Symbol, SymbolRef},
    types::{
        Alias, AliasData, AppVec, ArcType, Generic, NullInterner, PrimitiveEnv, Type, TypeCache,
        TypeEnv, TypeExt,
    },
    DebugLevel,
};

use crate::{
    api::{OpaqueValue, ValueRef, IO},
    compiler::{CompiledFunction, CompiledModule, CompilerEnv, Variable},
    core::{interpreter, optimize::OptimizeEnv, CoreExpr},
    gc::{Gc, GcPtr, GcRef, Generation, Move, Trace},
    interner::{InternedStr, Interner},
    lazy::Lazy,
    macros::MacroEnv,
    thread::ThreadInternal,
    types::*,
    value::{BytecodeFunction, ClosureData, ClosureDataDef},
    Error, Result, Variants,
};

pub use crate::{
    thread::{RootedThread, RootedValue, Status, Thread},
    value::Userdata,
};

pub(crate) type ThreadSlab = slab::Slab<GcPtr<Thread>>;

unsafe impl Trace for ThreadSlab {
    impl_trace! { self, gc,
        for (_, x) in self {
            mark(x, gc);
        }
    }
}

fn new_bytecode<'gc>(
    env: &dyn VmEnv<Type = ArcType>,
    interner: &mut Interner,
    gc: &'gc mut Gc,
    vm: &GlobalVmState,
    m: CompiledModule,
) -> Result<GcRef<'gc, ClosureData>> {
    let CompiledModule {
        module_globals,
        function,
    } = m;
    let bytecode_function = new_bytecode_function(interner, gc, vm, function)?;

    let globals = module_globals
        .into_iter()
        .map(|index| {
            env.get_global(index.definition_name())
                .expect("ICE: Global is missing from environment")
                .value
        })
        .collect::<Vec<_>>();

    // SAFETY No collection are done while we create these functions
    unsafe {
        let bytecode_function = bytecode_function.unrooted();
        gc.alloc(ClosureDataDef(
            &bytecode_function,
            globals.iter().map(|v| v.get_value()),
        ))
    }
}

fn new_bytecode_function<'gc>(
    interner: &mut Interner,
    gc: &'gc mut Gc,
    vm: &GlobalVmState,
    f: CompiledFunction,
) -> Result<GcRef<'gc, BytecodeFunction>> {
    let CompiledFunction {
        id,
        args,
        max_stack_size,
        instructions,
        inner_functions,
        strings,
        records,
        debug_info,
        ..
    } = f;

    let fs: Result<_> = inner_functions
        .into_iter()
        // SAFETY No collection are done while we create these functions
        .map(|inner| unsafe { Ok(new_bytecode_function(interner, gc, vm, inner)?.unrooted()) })
        .collect();

    let records: StdResult<_, _> = records
        .into_iter()
        .map(|vec| {
            vec.into_iter()
                .map(|field| Ok(interner.intern(gc, field.as_ref())?))
                .collect::<Result<_>>()
        })
        .collect();

    gc.alloc(Move(BytecodeFunction {
        name: id,
        args,
        max_stack_size,
        instructions,
        inner_functions: fs?,
        strings,
        records: records?,
        debug_info,
    }))
}

#[derive(Clone, Debug)]
#[cfg_attr(
    feature = "serde_derive_state",
    derive(DeserializeState, SerializeState)
)]
#[cfg_attr(
    feature = "serde_derive_state",
    serde(
        deserialize_state = "crate::serialization::DeSeed<'gc>",
        de_parameters = "'gc",
        bound(deserialize = "V: DeserializeState<'de, crate::serialization::DeSeed<'gc>>")
    )
)]
#[cfg_attr(
    feature = "serde_derive_state",
    serde(serialize_state = "crate::serialization::SeSeed")
)]
pub struct Global<V> {
    #[cfg_attr(
        feature = "serde_derive",
        serde(state_with = "crate::serialization::symbol")
    )]
    pub id: Symbol,
    #[cfg_attr(
        feature = "serde_derive",
        serde(state_with = "crate::serialization::borrow")
    )]
    pub typ: ArcType,
    pub metadata: Arc<Metadata>,
    #[cfg_attr(feature = "serde_derive_state", serde(state))]
    pub value: V,
}

pub type RootedGlobal = Global<RootedValue<RootedThread>>;

impl<V> Eq for Global<V> {}

impl<V> PartialEq for Global<V> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<V> std::hash::Hash for Global<V> {
    fn hash<H>(&self, hasher: &mut H)
    where
        H: std::hash::Hasher,
    {
        self.id.hash(hasher)
    }
}

unsafe impl<V> Trace for Global<V>
where
    V: Trace,
{
    impl_trace_fields! { self, gc; value }
}

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
pub struct GlobalVmState {
    #[cfg_attr(
        feature = "serde_derive",
        serde(state_with = "crate::serialization::rw_lock")
    )]
    env: parking_lot::RwLock<Globals>,
    #[cfg_attr(
        feature = "serde_derive",
        serde(state_with = "crate::serialization::borrow")
    )]
    generics: RwLock<FnvMap<StdString, ArcType>>,

    #[cfg_attr(feature = "serde_derive", serde(skip))]
    typeids: RwLock<FnvMap<TypeId, ArcType>>,

    #[cfg_attr(feature = "serde_derive", serde(state))]
    interner: RwLock<Interner>,

    #[cfg_attr(feature = "serde_derive", serde(skip))]
    macros: MacroEnv,

    #[cfg_attr(feature = "serde_derive", serde(skip))]
    type_cache: TypeCache<Symbol, ArcType>,

    // FIXME These fields should not be public
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub gc: Mutex<Gc>,

    // List of all generation 0 threads (ie, threads allocated by the global gc). when doing a
    // generation 0 sweep these threads are scanned as generation 0 values may be refered to by any
    // thread
    #[cfg_attr(feature = "serde_derive", serde(skip))]
    pub generation_0_threads: RwLock<ThreadSlab>,

    #[cfg_attr(feature = "serde_derive", serde(skip))]
    debug_level: RwLock<DebugLevel>,

    /// Tracks how many `RootedThread`s exist that refer to this global state.
    /// Only when all `RootedThread`s are dropped are we sure that we can drop any thread without
    /// resorting to garbage collection
    // The references gets added automatically when recreating the threads
    #[cfg_attr(feature = "serde_derive", serde(skip))]
    pub(crate) thread_reference_count: AtomicUsize,

    #[cfg_attr(feature = "serde_derive", serde(skip))]
    spawner: Option<Box<dyn futures::task::Spawn + Send + Sync>>,
}

unsafe impl Trace for GlobalVmState {
    unsafe fn root(&mut self) {
        self.macros.root();

        // Also need to check the interned string table
        self.interner.get_mut().unwrap().root();
        self.generation_0_threads.get_mut().unwrap().root();
    }
    unsafe fn unroot(&mut self) {
        self.macros.unroot();

        // Also need to check the interned string table
        self.interner.get_mut().unwrap().unroot();
        self.generation_0_threads.get_mut().unwrap().unroot();
    }

    fn trace(&self, gc: &mut Gc) {
        self.macros.trace(gc);

        // Also need to check the interned string table
        self.interner.read().unwrap().trace(gc);
        self.generation_0_threads.read().unwrap().trace(gc);
    }
}

#[derive(Debug, Default)]
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
pub struct Globals {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub type_infos: TypeInfos,
}

pub trait VmEnv:
    OptimizeEnv + CompilerEnv<Type = ArcType> + MetadataEnv + PrimitiveEnv + Trace
{
    fn get_global(&self, name: &str) -> Option<RootedGlobal>;
}

pub struct VmEnvInstance<'a> {
    // FIXME Use the database stored here for lookups
    vm_envs: Vec<Box<dyn VmEnv>>,
    globals: parking_lot::RwLockReadGuard<'a, Globals>,
    thread: &'a Thread,
}

unsafe impl Trace for VmEnvInstance<'_> {
    impl_trace_fields! { self, gc; vm_envs }
}

impl<'a> OptimizeEnv for VmEnvInstance<'a> {
    fn find_expr(&self, id: &Symbol) -> Option<interpreter::Global<CoreExpr>> {
        self.vm_envs.iter().find_map(|env| env.find_expr(id))
    }
}

impl<'a> CompilerEnv for VmEnvInstance<'a> {
    fn find_var(&self, id: &Symbol) -> Option<(Variable<Symbol>, ArcType)> {
        self.vm_envs
            .iter()
            .filter_map(|env| env.find_var(id))
            .next()
            .or_else(|| self.globals.type_infos.find_var(id))
    }
}

impl<'a> KindEnv for VmEnvInstance<'a> {
    fn find_kind(&self, id: &SymbolRef) -> Option<ArcKind> {
        self.vm_envs
            .iter()
            .filter_map(|env| env.find_kind(id))
            .next()
            .or_else(|| self.globals.type_infos.find_kind(id))
    }
}

impl<'a> TypeEnv for VmEnvInstance<'a> {
    type Type = ArcType;

    fn find_type(&self, id: &SymbolRef) -> Option<ArcType> {
        self.vm_envs
            .iter()
            .filter_map(|env| env.find_type(id))
            .next()
            .or_else(|| {
                self.globals
                    .type_infos
                    .id_to_type
                    .values()
                    .filter_map(|alias| match **alias.unresolved_type() {
                        Type::Variant(ref row) => row
                            .row_iter()
                            .find(|field| *field.name == *id)
                            .map(|field| &field.typ),
                        _ => None,
                    })
                    .next()
                    .map(|ctor| ctor.clone())
            })
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<Alias<Symbol, ArcType>> {
        self.vm_envs
            .iter()
            .filter_map(|env| env.find_type_info(id))
            .next()
            .or_else(|| self.globals.type_infos.find_type_info(id))
    }
}

impl<'a> PrimitiveEnv for VmEnvInstance<'a> {
    fn get_bool(&self) -> ArcType {
        self.find_type_info("std.types.Bool")
            .expect("Missing std.types.Bool")
            .into_type()
    }
}

impl<'a> MetadataEnv for VmEnvInstance<'a> {
    fn get_metadata(&self, id: &SymbolRef) -> Option<Arc<Metadata>> {
        self.get_metadata_(id.definition_name())
    }
}

impl<'a> VmEnv for VmEnvInstance<'a> {
    fn get_global(&self, name: &str) -> Option<RootedGlobal> {
        self.vm_envs
            .iter()
            .filter_map(|env| env.get_global(name))
            .next()
    }
}

impl<'a> VmEnvInstance<'a> {
    pub fn find_type_info(&self, name: &str) -> Result<Alias<Symbol, ArcType>> {
        let name = Name::new(name);

        if let Some(alias) = self.globals.type_infos.id_to_type.get(name.as_str()) {
            return Ok(alias.clone());
        }

        let (_, typ) = self
            .get_binding(name.module().as_str())
            .map_err(|mut err| {
                if let Error::UndefinedBinding(module) = &mut err {
                    module.clear();
                    module.push_str(name.as_str());
                }
                err
            })?;
        let maybe_type_info = {
            let field_name = name.name();
            typ.type_field_iter()
                .find(|field| field.name.as_str() == field_name.as_str())
                .map(|field| &field.typ)
                .cloned()
        };
        maybe_type_info.ok_or_else(move || Error::UndefinedField(typ, name.name().as_str().into()))
    }

    fn get_scoped_global<'s, 'n>(&'s self, name: &'n str) -> Option<(&'n Name, RootedGlobal)> {
        let mut module = Name::new(name.trim_start_matches('@'));
        let global;
        // Try to find a global by successively reducing the module path
        // Input: "x.y.z.w"
        // Test: "x.y.z"
        // Test: "x.y"
        // Test: "x"
        // Test: -> Error
        loop {
            if module.as_str() == "" {
                return None;
            }
            if let Some(g) = self.get_global(module.as_str()) {
                global = g;
                break;
            }
            module = module.module();
        }

        let remaining_offset = ::std::cmp::min(name.len(), module.as_str().len() + 1); //Add 1 byte for the '.'
        let remaining_fields = Name::new(&name[remaining_offset..]);
        Some((remaining_fields, global))
    }

    #[doc(hidden)]
    pub fn get_binding(&self, name: &str) -> Result<(RootedValue<RootedThread>, ArcType)> {
        use crate::base::resolve;

        let (remaining_fields, global) = self
            .get_scoped_global(name)
            .ok_or_else(|| Error::UndefinedBinding(name.into()))?;

        if remaining_fields.as_str().is_empty() {
            // No fields left
            return Ok((global.value, global.typ));
        }

        let mut typ = global.typ;
        let mut value = Variants::new(&global.value);

        for mut field_name in remaining_fields.components() {
            if field_name.starts_with('(') && field_name.ends_with(')') {
                field_name = &field_name[1..field_name.len() - 1];
            } else if field_name.contains(ast::is_operator_char) {
                return Err(Error::Message(format!(
                    "Operators cannot be used as fields \
                     directly. To access an operator field, \
                     enclose the operator with parentheses \
                     before passing it in. (test.(+) instead of \
                     test.+)"
                )));
            }
            typ = resolve::remove_aliases(self, &mut NullInterner, typ);
            // HACK Can't return the data directly due to the use of cow on the type
            let next_type = {
                typ.row_iter()
                    .enumerate()
                    .find(|&(_, field)| field.name.as_pretty_str() == field_name)
                    .map(|(index, field)| match value.as_ref() {
                        ValueRef::Data(data) => {
                            value = data.get_variant(index).unwrap();
                            &field.typ
                        }
                        _ => ice!("Unexpected value {:?}", value),
                    })
                    .cloned()
            };
            typ = next_type.ok_or_else(move || Error::UndefinedField(typ, field_name.into()))?;
        }
        Ok((self.thread.root_value(value), typ))
    }

    pub fn get_metadata(&self, name_str: &str) -> Result<Arc<Metadata>> {
        self.get_metadata_(name_str)
            .ok_or_else(|| Error::MetadataDoesNotExist(name_str.into()))
    }

    fn get_metadata_(&self, name_str: &str) -> Option<Arc<Metadata>> {
        let (remaining, global) = self.get_scoped_global(name_str)?;

        let mut metadata = &global.metadata;
        for field_name in remaining.components() {
            metadata = metadata.module.get(field_name)?
        }
        Some(metadata.clone())
    }
}

#[derive(Default)]
pub struct GlobalVmStateBuilder {
    spawner: Option<Box<dyn futures::task::Spawn + Send + Sync>>,
}

impl GlobalVmStateBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn spawner(mut self, spawner: Option<Box<dyn futures::task::Spawn + Send + Sync>>) -> Self {
        self.spawner = spawner;
        self
    }

    pub fn build(self) -> GlobalVmState {
        let mut vm = GlobalVmState {
            env: Default::default(),
            generics: RwLock::new(FnvMap::default()),
            typeids: RwLock::new(FnvMap::default()),
            interner: RwLock::new(Interner::new()),
            gc: Mutex::new(Gc::new(Generation::default(), usize::MAX)),
            macros: MacroEnv::new(),
            type_cache: TypeCache::default(),
            generation_0_threads: Default::default(),
            debug_level: RwLock::new(DebugLevel::default()),
            thread_reference_count: Default::default(),
            spawner: self.spawner,
        };
        vm.add_types().unwrap();
        vm
    }
}

impl GlobalVmState {
    pub fn new() -> Self {
        GlobalVmStateBuilder::new().build()
    }

    fn add_types(&mut self) -> StdResult<(), (TypeId, ArcType)> {
        use crate::api::generic::A;
        use crate::api::Generic;
        use crate::base::types::BuiltinType;
        fn add_builtin_type<T: Any>(self_: &mut GlobalVmState, b: BuiltinType) {
            add_builtin_type_(self_, b, TypeId::of::<T>())
        }
        fn add_builtin_type_(self_: &mut GlobalVmState, b: BuiltinType, id: TypeId) {
            let typ = self_.type_cache.builtin_type(b);
            add_type(self_, b.to_str(), typ, id)
        }
        fn add_type(self_: &mut GlobalVmState, name: &str, typ: ArcType, id: TypeId) {
            let ids = self_.typeids.get_mut().unwrap();
            let env = self_.env.get_mut();
            ids.insert(id, typ);
            // Insert aliases so that `find_info` can retrieve information about the primitives
            env.type_infos.id_to_type.insert(
                name.into(),
                Alias::from(AliasData::new(
                    Symbol::from(name),
                    vec![],
                    self_.type_cache.opaque(),
                )),
            );
        }

        {
            let unit = self.type_cache.unit();
            add_type(self, "()", unit, TypeId::of::<()>());
            add_builtin_type::<VmInt>(self, BuiltinType::Int);
            add_builtin_type::<u8>(self, BuiltinType::Byte);
            add_builtin_type::<f32>(self, BuiltinType::Float);
            add_builtin_type::<f64>(self, BuiltinType::Float);
            add_builtin_type::<::std::string::String>(self, BuiltinType::String);
            add_builtin_type::<char>(self, BuiltinType::Char)
        }
        self.register_type::<IO<Generic<A>>>("std.io.IO", &["a"])
            .unwrap();
        self.register_type::<Lazy<Generic<A>>>("std.lazy.Lazy", &["a"])
            .unwrap();
        self.register_type::<Thread>("std.thread.Thread", &[])
            .unwrap();
        Ok(())
    }

    pub fn type_cache(&self) -> &TypeCache<Symbol, ArcType> {
        &self.type_cache
    }

    pub fn new_global_thunk(
        &self,
        thread: &Thread,
        f: CompiledModule,
    ) -> Result<OpaqueValue<RootedThread, GcPtr<ClosureData>>> {
        let mut gc = self.gc.lock().unwrap();
        let env = self.get_env(thread);
        let mut interner = self.interner.write().unwrap();
        let byte_code = new_bytecode(&env, &mut interner, &mut gc, self, f)?;
        Ok(OpaqueValue::from_value(
            thread.root_value(Variants::from(byte_code)),
        ))
    }

    pub fn get_type<T: ?Sized + Any>(&self) -> Option<ArcType> {
        let id = TypeId::of::<T>();
        self.typeids.read().unwrap().get(&id).cloned()
    }

    pub fn get_generic(&self, name: &str) -> ArcType {
        let mut generics = self.generics.write().unwrap();
        if let Some(g) = generics.get(name) {
            return g.clone();
        }
        let g: ArcType = Type::generic(Generic::new(Symbol::from(name), Kind::typ()));
        generics.insert(name.into(), g.clone());
        g
    }

    /// Registers a new type called `name`
    pub fn register_type<T: ?Sized + Any>(&self, name: &str, args: &[&str]) -> Result<ArcType> {
        self.register_type_(name, args, TypeId::of::<T>())
    }

    fn register_type_(&self, name: &str, args: &[&str], id: TypeId) -> Result<ArcType> {
        let arg_types: AppVec<_> = args.iter().map(|g| self.get_generic(g)).collect();
        let args = arg_types
            .iter()
            .map(|g| match **g {
                Type::Generic(ref g) => g.clone(),
                _ => unreachable!(),
            })
            .collect();
        let n = Symbol::from(name);
        let alias = Alias::from(AliasData::new(n.clone(), args, self.type_cache.opaque()));
        self.register_type_as(n, alias, id)
    }

    pub fn register_type_as(
        &self,
        name: Symbol,
        alias: Alias<Symbol, ArcType>,
        id: TypeId,
    ) -> Result<ArcType> {
        let mut env = self.env.write();
        let type_infos = &mut env.type_infos;
        self.typeids
            .write()
            .unwrap()
            .insert(id, alias.clone().into_type());
        let t = alias.clone().into_type();
        type_infos
            .id_to_type
            .insert(name.definition_name().into(), alias);
        Ok(t)
    }

    #[doc(hidden)]
    pub fn get_cache_alias(&self, name: &str) -> Option<ArcType> {
        let env = self.env.read();
        env
            .type_infos
            .id_to_type
            .get(name)
            .map(|alias| alias.clone().into_type())
    }

    #[doc(hidden)]
    pub fn cache_alias(&self, alias: Alias<Symbol, ArcType>) -> ArcType {
        let mut env = self.env.write();
        let type_infos = &mut env.type_infos;
        let t = alias.clone().into_type();
        type_infos
            .id_to_type
            .insert(alias.name.definition_name().into(), alias);
        t
    }

    pub fn get_macros(&self) -> &MacroEnv {
        &self.macros
    }

    pub fn intern(&self, s: &str) -> Result<InternedStr> {
        let mut gc = self.gc.lock().unwrap();
        let mut interner = self.interner.write().unwrap();
        interner.intern(&mut *gc, s)
    }

    /// Returns a borrowed structure which implements `CompilerEnv`
    pub fn get_env<'t>(&'t self, thread: &'t Thread) -> VmEnvInstance<'t> {
        let capabilities = self.macros.get_capabilities::<Box<dyn VmEnv>>(thread);
        VmEnvInstance {
            vm_envs: capabilities,
            globals: self.env.read_recursive(),
            thread,
        }
    }

    pub fn get_capability<'t, T>(&'t self, thread: &'t Thread) -> Option<T>
    where
        T: Any,
    {
        self.macros.get_capability(thread)
    }

    #[doc(hidden)]
    pub fn get_lookup_env<'t>(&'t self, thread: &'t Thread) -> VmEnvInstance<'t> {
        VmEnvInstance {
            vm_envs: Vec::new(),
            globals: self.env.read_recursive(),
            thread,
        }
    }

    #[doc(hidden)]
    pub fn get_globals(&self) -> parking_lot::RwLockReadGuard<Globals> {
        self.env.read_recursive()
    }

    pub fn get_debug_level(&self) -> DebugLevel {
        self.debug_level.read().unwrap().clone()
    }

    pub fn set_debug_level(&self, debug_level: DebugLevel) {
        *self.debug_level.write().unwrap() = debug_level;
    }

    pub fn spawner(&self) -> Option<&(dyn futures::task::Spawn + Send + Sync)> {
        self.spawner.as_ref().map(|s| &**s)
    }
}
