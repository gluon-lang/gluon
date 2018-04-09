use std::any::{Any, TypeId};
use std::borrow::Cow;
use std::result::Result as StdResult;
use std::string::String as StdString;
use std::sync::{Mutex, RwLock, RwLockReadGuard};
use std::usize;

use base::ast;
use base::fnv::FnvMap;
use base::kind::{ArcKind, Kind, KindEnv};
use base::metadata::{Metadata, MetadataEnv};
use base::symbol::{Name, Symbol, SymbolRef};
use base::types::{Alias, AliasData, AppVec, ArcType, Generic, PrimitiveEnv, Type, TypeCache,
                  TypeEnv};

use api::{ValueRef, IO};
use compiler::{CompiledFunction, CompiledModule, CompilerEnv, Variable};
use gc::{Gc, GcPtr, Generation, Move, Traverseable};
use interner::{InternedStr, Interner};
use lazy::Lazy;
use macros::MacroEnv;
use types::*;
use {Error, Result, Variants};

use value::{BytecodeFunction, ClosureData, ClosureDataDef, Value};

pub use thread::{Root, RootStr, RootedThread, RootedValue, Status, Thread};
pub use value::Userdata;

fn new_bytecode(
    env: &VmEnv,
    interner: &mut Interner,
    gc: &mut Gc,
    vm: &GlobalVmState,
    m: CompiledModule,
) -> Result<GcPtr<ClosureData>> {
    let CompiledModule {
        module_globals,
        function,
    } = m;
    let bytecode_function = new_bytecode_function(interner, gc, vm, function)?;

    let globals = module_globals
        .into_iter()
        .map(|index| env.globals[index.definition_name()].value.clone())
        .collect::<Vec<_>>();

    gc.alloc(ClosureDataDef(bytecode_function, &globals))
}

fn new_bytecode_function(
    interner: &mut Interner,
    gc: &mut Gc,
    vm: &GlobalVmState,
    f: CompiledFunction,
) -> Result<GcPtr<BytecodeFunction>> {
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

    let fs: StdResult<_, _> = inner_functions
        .into_iter()
        .map(|inner| new_bytecode_function(interner, gc, vm, inner))
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
        args: args,
        max_stack_size: max_stack_size,
        instructions: instructions,
        inner_functions: fs?,
        strings: strings,
        records: records?,
        debug_info: debug_info,
    }))
}

#[derive(Debug)]
#[cfg_attr(feature = "serde_derive_state", derive(SerializeState, DeserializeState))]
#[cfg_attr(feature = "serde_derive_state", serde(deserialize_state = "::serialization::DeSeed"))]
#[cfg_attr(feature = "serde_derive_state", serde(serialize_state = "::serialization::SeSeed"))]
pub struct Global {
    #[cfg_attr(feature = "serde_derive", serde(state_with = "::serialization::symbol"))]
    pub id: Symbol,
    #[cfg_attr(feature = "serde_derive", serde(state_with = "::serialization::borrow"))]
    pub typ: ArcType,
    pub metadata: Metadata,
    #[cfg_attr(feature = "serde_derive_state", serde(state))]
    pub value: Value,
}

impl Traverseable for Global {
    fn traverse(&self, gc: &mut Gc) {
        self.value.traverse(gc);
    }
}

#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "::serialization::DeSeed"))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "::serialization::SeSeed"))]
pub struct GlobalVmState {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    env: RwLock<VmEnv>,

    #[cfg_attr(feature = "serde_derive", serde(state_with = "::serialization::borrow"))]
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
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub generation_0_threads: RwLock<Vec<GcPtr<Thread>>>,

    #[cfg_attr(feature = "serde_derive", serde(skip))]
    #[cfg(not(target_arch = "wasm32"))]
    event_loop: Option<::std::panic::AssertUnwindSafe<::tokio_core::reactor::Remote>>,
}

impl Traverseable for GlobalVmState {
    fn traverse(&self, gc: &mut Gc) {
        for g in self.env.read().unwrap().globals.values() {
            g.traverse(gc);
        }
        // Also need to check the interned string table
        self.interner.read().unwrap().traverse(gc);
        self.generation_0_threads.read().unwrap().traverse(gc);
    }
}

/// A borrowed structure which implements `CompilerEnv`, `TypeEnv` and `KindEnv` allowing the
/// typechecker and compiler to lookup things in the virtual machine.
#[derive(Debug)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "::serialization::DeSeed"))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "::serialization::SeSeed"))]
pub struct VmEnv {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub type_infos: TypeInfos,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub globals: FnvMap<StdString, Global>,
}

impl CompilerEnv for VmEnv {
    fn find_var(&self, id: &Symbol) -> Option<(Variable<Symbol>, ArcType)> {
        self.globals
            .get(id.definition_name())
            .map(|g| (Variable::UpVar(g.id.clone()), g.typ.clone()))
            .or_else(|| self.type_infos.find_var(id))
    }
}

impl KindEnv for VmEnv {
    fn find_kind(&self, type_name: &SymbolRef) -> Option<ArcKind> {
        self.type_infos.find_kind(type_name)
    }
}
impl TypeEnv for VmEnv {
    fn find_type(&self, id: &SymbolRef) -> Option<&ArcType> {
        self.globals
            .get(id.definition_name())
            .map(|g| &g.typ)
            .or_else(|| {
                self.type_infos
                    .id_to_type
                    .values()
                    .filter_map(|alias| match **alias.unresolved_type() {
                        Type::Variant(ref row) => row.row_iter()
                            .find(|field| *field.name == *id)
                            .map(|field| &field.typ),
                        _ => None,
                    })
                    .next()
                    .map(|ctor| ctor)
            })
    }

    fn find_type_info(&self, id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>> {
        self.type_infos.find_type_info(id)
    }
}

impl PrimitiveEnv for VmEnv {
    fn get_bool(&self) -> &ArcType {
        self.find_type_info("std.types.Bool")
            .map(|alias| match alias {
                Cow::Borrowed(alias) => alias.as_type(),
                Cow::Owned(_) => ice!("Expected to be able to retrieve a borrowed bool type"),
            })
            .expect("std.types.Bool")
    }
}

impl MetadataEnv for VmEnv {
    fn get_metadata(&self, id: &SymbolRef) -> Option<&Metadata> {
        self.get_metadata(id.definition_name()).ok()
    }
}

fn map_cow_option<T, U, F>(cow: Cow<T>, f: F) -> Option<Cow<U>>
where
    T: Clone,
    U: Clone,
    F: FnOnce(&T) -> Option<&U>,
{
    match cow {
        Cow::Borrowed(b) => f(b).map(Cow::Borrowed),
        Cow::Owned(o) => f(&o).map(|u| Cow::Owned(u.clone())),
    }
}

impl VmEnv {
    pub fn find_type_info(&self, name: &str) -> Result<Cow<Alias<Symbol, ArcType>>> {
        let name = Name::new(name);
        let module_str = name.module().as_str();
        if module_str == "" {
            return match self.type_infos.id_to_type.get(name.as_str()) {
                Some(alias) => Ok(Cow::Borrowed(alias)),
                None => Err(Error::UndefinedBinding(name.as_str().into())),
            };
        }
        let (_, typ) = self.get_binding(name.module().as_str())?;
        let maybe_type_info = map_cow_option(typ.clone(), |typ| {
            let field_name = name.name();
            typ.type_field_iter()
                .find(|field| field.name.as_ref() == field_name.as_str())
                .map(|field| &field.typ)
        });
        maybe_type_info.ok_or_else(move || {
            Error::UndefinedField(typ.into_owned(), name.name().as_str().into())
        })
    }

    fn get_global<'s, 'n>(&'s self, name: &'n str) -> Option<(&'n Name, &'s Global)> {
        let globals = &self.globals;
        let mut module = Name::new(name.trim_left_matches('@'));
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
            if let Some(g) = globals.get(module.as_str()) {
                global = g;
                break;
            }
            module = module.module();
        }
        let remaining_offset = ::std::cmp::min(name.len(), module.as_str().len() + 1); //Add 1 byte for the '.'
        let remaining_fields = Name::new(&name[remaining_offset..]);
        Some((remaining_fields, global))
    }

    pub fn get_binding(&self, name: &str) -> Result<(Value, Cow<ArcType>)> {
        use base::resolve;

        let (remaining_fields, global) = self.get_global(name)
            .ok_or_else(|| Error::UndefinedBinding(name.into()))?;

        if remaining_fields.as_str().is_empty() {
            // No fields left
            return Ok((global.value.clone(), Cow::Borrowed(&global.typ)));
        }

        let mut typ = Cow::Borrowed(&global.typ);
        let mut value = unsafe { Variants::new(&global.value) };

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
            typ = match typ {
                Cow::Borrowed(typ) => resolve::remove_aliases_cow(self, typ),
                Cow::Owned(typ) => Cow::Owned(resolve::remove_aliases(self, typ)),
            };
            // HACK Can't return the data directly due to the use of cow on the type
            let next_type = map_cow_option(typ.clone(), |typ| {
                typ.row_iter()
                    .enumerate()
                    .find(|&(_, field)| field.name.as_ref() == field_name)
                    .map(|(index, field)| match value.as_ref() {
                        ValueRef::Data(data) => {
                            value = data.get_variant(index).unwrap();
                            &field.typ
                        }
                        _ => ice!("Unexpected value {:?}", value),
                    })
            });
            typ = next_type
                .ok_or_else(move || Error::UndefinedField(typ.into_owned(), field_name.into()))?;
        }
        Ok((value.get_value(), typ))
    }

    pub fn get_metadata(&self, name_str: &str) -> Result<&Metadata> {
        let (remaining, global) = self.get_global(name_str)
            .ok_or_else(|| Error::MetadataDoesNotExist(name_str.into()))?;

        let mut metadata = &global.metadata;
        for field_name in remaining.components() {
            metadata = metadata
                .module
                .get(field_name)
                .ok_or_else(|| Error::MetadataDoesNotExist(name_str.into()))?;
        }
        Ok(metadata)
    }
}

macro_rules! option {
    ($(#[$attr:meta])* $name: ident $set_name: ident : $typ: ty) => {
        $(#[$attr])*
        pub fn $name(mut self, $name: $typ) -> Self {
            self.$name = $name;
            self
        }

        $(#[$attr])*
        pub fn $set_name(&mut self, $name: $typ) {
            self.$name = $name;
        }
    };
}

#[derive(Default)]
pub struct GlobalVmStateBuilder {
    #[cfg(not(target_arch = "wasm32"))]
    event_loop: Option<::tokio_core::reactor::Remote>,
}

impl GlobalVmStateBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    option!(
        #[cfg(not(target_arch = "wasm32"))]
        event_loop set_event_loop: Option<::tokio_core::reactor::Remote>
    );

    pub fn build(self) -> GlobalVmState {
        let mut vm = GlobalVmState {
            env: RwLock::new(VmEnv {
                globals: FnvMap::default(),
                type_infos: TypeInfos::new(),
            }),
            generics: RwLock::new(FnvMap::default()),
            typeids: RwLock::new(FnvMap::default()),
            interner: RwLock::new(Interner::new()),
            gc: Mutex::new(Gc::new(Generation::default(), usize::MAX)),
            macros: MacroEnv::new(),
            type_cache: TypeCache::new(),
            generation_0_threads: RwLock::new(Vec::new()),

            #[cfg(not(target_arch = "wasm32"))]
            event_loop: self.event_loop.map(::std::panic::AssertUnwindSafe),
        };
        vm.add_types().unwrap();
        vm
    }
}

impl GlobalVmState {
    fn add_types(&mut self) -> StdResult<(), (TypeId, ArcType)> {
        use api::Generic;
        use api::generic::A;
        use base::types::BuiltinType;
        fn add_builtin_type<T: Any>(self_: &mut GlobalVmState, b: BuiltinType) {
            let typ = self_.type_cache.builtin_type(b);
            add_type::<T>(self_, b.to_str(), typ)
        }
        fn add_type<T: Any>(self_: &mut GlobalVmState, name: &str, typ: ArcType) {
            let ids = self_.typeids.get_mut().unwrap();
            let env = self_.env.get_mut().unwrap();
            ids.insert(TypeId::of::<T>(), typ);
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
            add_type::<()>(self, "()", unit);
            add_builtin_type::<VmInt>(self, BuiltinType::Int);
            add_builtin_type::<u8>(self, BuiltinType::Byte);
            add_builtin_type::<f64>(self, BuiltinType::Float);
            add_builtin_type::<::std::string::String>(self, BuiltinType::String);
            add_builtin_type::<char>(self, BuiltinType::Char)
        }
        self.register_type::<IO<Generic<A>>>("IO", &["a"]).unwrap();
        self.register_type::<Lazy<Generic<A>>>("Lazy", &["a"])
            .unwrap();
        self.register_type::<Thread>("Thread", &[]).unwrap();
        Ok(())
    }

    #[cfg(not(target_arch = "wasm32"))]
    pub fn get_event_loop(&self) -> Option<::tokio_core::reactor::Remote> {
        self.event_loop.as_ref().map(|x| x.0.clone())
    }

    pub fn type_cache(&self) -> &TypeCache<Symbol, ArcType> {
        &self.type_cache
    }

    pub fn new_global_thunk(&self, f: CompiledModule) -> Result<GcPtr<ClosureData>> {
        let env = self.env.read().unwrap();
        let mut interner = self.interner.write().unwrap();
        let mut gc = self.gc.lock().unwrap();
        new_bytecode(&env, &mut interner, &mut gc, self, f)
    }

    pub fn get_type<T: ?Sized + Any>(&self) -> ArcType {
        let id = TypeId::of::<T>();
        self.typeids
            .read()
            .unwrap()
            .get(&id)
            .cloned()
            .unwrap_or_else(|| {
                ice!(
                    "Expected type to be inserted before get_type call. \
                     Did you forget to call `Thread::register_type`?"
                )
            })
    }

    /// Checks if a global exists called `name`
    pub fn global_exists(&self, name: &str) -> bool {
        self.env.read().unwrap().globals.get(name).is_some()
    }

    pub(crate) fn set_global(
        &self,
        id: Symbol,
        typ: ArcType,
        metadata: Metadata,
        value: Value,
    ) -> Result<()> {
        assert!(value.generation().is_root());
        assert!(
            id.as_ref().matches('@').next() == Some("@"),
            "Global symbols must be prefix with '@'"
        );
        let mut env = self.env.write().unwrap();
        let globals = &mut env.globals;
        let global = Global {
            id: id.clone(),
            typ: typ,
            metadata: metadata,
            value: value,
        };
        globals.insert(StdString::from(id.definition_name()), global);
        Ok(())
    }

    // Currently necessary for the language server
    #[doc(hidden)]
    pub fn set_dummy_global(&self, id: &str, typ: ArcType, metadata: Metadata) -> Result<()> {
        self.set_global(
            Symbol::from(format!("@{}", id)),
            typ,
            metadata,
            Value::int(0),
        )
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
        let mut env = self.env.write().unwrap();
        let type_infos = &mut env.type_infos;
        if type_infos.id_to_type.contains_key(name) {
            Err(Error::TypeAlreadyExists(name.into()))
        } else {
            let id = TypeId::of::<T>();
            let arg_types: AppVec<_> = args.iter().map(|g| self.get_generic(g)).collect();
            let args = arg_types
                .iter()
                .map(|g| match **g {
                    Type::Generic(ref g) => g.clone(),
                    _ => unreachable!(),
                })
                .collect();
            let n = Symbol::from(name);
            let typ: ArcType = Type::app(Type::ident(n.clone()), arg_types);
            self.typeids.write().unwrap().insert(id, typ.clone());
            let t = self.typeids.read().unwrap().get(&id).unwrap().clone();
            type_infos.id_to_type.insert(
                name.into(),
                Alias::from(AliasData::new(n, args, self.type_cache.opaque())),
            );
            Ok(t)
        }
    }

    pub fn get_macros(&self) -> &MacroEnv {
        &self.macros
    }

    pub fn intern(&self, s: &str) -> Result<InternedStr> {
        let mut interner = self.interner.write().unwrap();
        let mut gc = self.gc.lock().unwrap();
        interner.intern(&mut *gc, s)
    }

    /// Returns a borrowed structure which implements `CompilerEnv`
    pub fn get_env<'b>(&'b self) -> RwLockReadGuard<'b, VmEnv> {
        self.env.read().unwrap()
    }
}
