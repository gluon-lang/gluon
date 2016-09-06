use std::borrow::Cow;
use std::sync::{Mutex, RwLock, RwLockReadGuard};
use std::any::{Any, TypeId};
use std::result::Result as StdResult;
use std::string::String as StdString;
use std::usize;

use base::metadata::{Metadata, MetadataEnv};
use base::symbol::{Name, Symbol, SymbolRef};
use base::types::{Alias, AliasData, ArcType, Generic, Type, Kind, KindEnv, TypeEnv, PrimitiveEnv,
                  RcKind};
use base::fnv::FnvMap;

use macros::MacroEnv;
use {Error, Result};
use types::*;
use interner::{Interner, InternedStr};
use gc::{Gc, GcPtr, Traverseable, Move};
use compiler::{CompiledFunction, Variable, CompilerEnv};
use api::IO;
use lazy::Lazy;

use value::BytecodeFunction;

pub use value::{ClosureDataDef, Userdata};
pub use value::Value;//FIXME Value should not be exposed
pub use thread::{Thread, RootedThread, Status, Root, RootStr, RootedValue};


fn new_bytecode(gc: &mut Gc,
                vm: &GlobalVmState,
                f: CompiledFunction)
                -> Result<GcPtr<BytecodeFunction>> {
    let CompiledFunction { id,
                           args,
                           instructions,
                           inner_functions,
                           strings,
                           module_globals,
                           records,
                           .. } = f;
    let fs = try!(inner_functions.into_iter()
        .map(|inner| new_bytecode(gc, vm, inner))
        .collect());

    let globals = module_globals.into_iter()
        .map(|index| vm.env.read().unwrap().globals[index.as_ref()].value)
        .collect();
    let records = try!(records.into_iter()
        .map(|vec| {
            vec.into_iter()
                .map(|field| Ok(try!(vm.interner.write().unwrap().intern(gc, field.as_ref()))))
                .collect::<Result<_>>()
        })
        .collect());
    gc.alloc(Move(BytecodeFunction {
        name: id,
        args: args,
        instructions: instructions,
        inner_functions: fs,
        strings: strings,
        globals: globals,
        records: records,
    }))
}


#[derive(Debug)]
pub struct Global {
    pub id: Symbol,
    pub typ: ArcType,
    pub metadata: Metadata,
    pub value: Value,
}

impl Traverseable for Global {
    fn traverse(&self, gc: &mut Gc) {
        self.value.traverse(gc);
    }
}

pub struct GlobalVmState {
    env: RwLock<VmEnv>,
    generics: RwLock<FnvMap<StdString, ArcType>>,
    typeids: RwLock<FnvMap<TypeId, ArcType>>,
    interner: RwLock<Interner>,
    macros: MacroEnv,
    // FIXME These fields should not be public
    pub gc: Mutex<Gc>,
    // List of all generation 0 threads (ie, threads allocated by the global gc). when doing a
    // generation 0 sweep these threads are scanned as generation 0 values may be refered to by any
    // thread
    pub generation_0_threads: RwLock<Vec<GcPtr<Thread>>>,
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
pub struct VmEnv {
    pub type_infos: TypeInfos,
    pub globals: FnvMap<StdString, Global>,
}

impl CompilerEnv for VmEnv {
    fn find_var(&self, id: &Symbol) -> Option<Variable<Symbol>> {
        self.globals
            .get(id.as_ref())
            .map(|g| Variable::Global(g.id.clone()))
            .or_else(|| self.type_infos.find_var(id))
    }
}

impl KindEnv for VmEnv {
    fn find_kind(&self, type_name: &SymbolRef) -> Option<RcKind> {
        self.type_infos
            .find_kind(type_name)
    }
}
impl TypeEnv for VmEnv {
    fn find_type(&self, id: &SymbolRef) -> Option<&ArcType> {
        self.globals
            .get(AsRef::<str>::as_ref(id))
            .map(|g| &g.typ)
            .or_else(|| {
                self.type_infos
                    .id_to_type
                    .values()
                    .filter_map(|alias| {
                        alias.typ
                            .as_ref()
                            .and_then(|typ| {
                                match **typ {
                                    Type::Variants(ref ctors) => {
                                        ctors.iter().find(|ctor| *ctor.0 == *id).map(|t| &t.1)
                                    }
                                    _ => None,
                                }
                            })
                    })
                    .next()
                    .map(|ctor| ctor)
            })
    }
    fn find_type_info(&self, id: &SymbolRef) -> Option<&Alias<Symbol, ArcType>> {
        self.type_infos
            .find_type_info(id)
    }
    fn find_record(&self, fields: &[Symbol]) -> Option<(&ArcType, &ArcType)> {
        self.type_infos.find_record(fields)
    }
}

impl PrimitiveEnv for VmEnv {
    fn get_bool(&self) -> &ArcType {
        self.find_type_info("std.types.Bool")
            .ok()
            .and_then(|alias| match alias {
                Cow::Borrowed(alias) => alias.typ.as_ref(),
                Cow::Owned(_) => panic!("Expected to be able to retrieve a borrowed bool type"),
            })
            .expect("std.types.Bool")
    }
}

impl MetadataEnv for VmEnv {
    fn get_metadata(&self, id: &Symbol) -> Option<&Metadata> {
        self.globals
            .get(AsRef::<str>::as_ref(id))
            .map(|g| &g.metadata)
    }
}

fn map_cow_option<T, U, F>(cow: Cow<T>, f: F) -> Option<Cow<U>>
    where T: Clone,
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
        let (_, typ) = try!(self.get_binding(name.module().as_str()));
        let maybe_type_info = map_cow_option(typ.clone(), |typ| {
            match **typ {
                Type::Record { ref types, .. } => {
                    let field_name = name.name();
                    types.iter()
                        .find(|field| field.name.as_ref() == field_name.as_str())
                        .map(|field| &field.typ)
                }
                _ => None,
            }
        });
        maybe_type_info.ok_or_else(move || {
            Error::UndefinedField(typ.into_owned(), name.name().as_str().into())
        })
    }

    pub fn get_binding(&self, name: &str) -> Result<(Value, Cow<ArcType>)> {
        use base::instantiate;
        let globals = &self.globals;
        let mut module = Name::new(name);
        let global;
        // Try to find a global by successively reducing the module path
        // Input: "x.y.z.w"
        // Test: "x.y.z"
        // Test: "x.y"
        // Test: "x"
        // Test: -> Error
        loop {
            if module.as_str() == "" {
                return Err(Error::UndefinedBinding(name.into()));
            }
            if let Some(g) = globals.get(module.as_str()) {
                global = g;
                break;
            }
            module = module.module();
        }
        let remaining_offset = module.as_str().len() + 1;//Add 1 byte for the '.'
        if remaining_offset >= name.len() {
            // No fields left
            return Ok((global.value, Cow::Borrowed(&global.typ)));
        }
        let remaining_fields = Name::new(&name[remaining_offset..]);

        let mut typ = Cow::Borrowed(&global.typ);
        let mut value = global.value;

        for mut field_name in remaining_fields.components() {
            if field_name.starts_with('(') && field_name.ends_with(')') {
                field_name = &field_name[1..field_name.len() - 1];
            } else if field_name.chars().any(|c| "+-*/&|=<>".chars().any(|x| x == c)) {
                return Err(Error::Message(format!("Operators cannot be used as fields \
                                                   directly. To access an operator field, \
                                                   enclose the operator with parentheses \
                                                   before passing it in. (test.(+) instead of \
                                                   test.+)")));
            }
            typ = match typ {
                Cow::Borrowed(typ) => instantiate::remove_aliases_cow(self, typ),
                Cow::Owned(typ) => Cow::Owned(instantiate::remove_aliases(self, typ)),
            };
            // HACK Can't return the data directly due to the use of cow on the type
            let next_type = map_cow_option(typ.clone(), |typ| {
                typ.field_iter()
                    .enumerate()
                    .find(|&(_, field)| field.name.as_ref() == field_name)
                    .map(|(index, field)| {
                        match value {
                            Value::Data(data) => {
                                value = data.fields[index];
                                &field.typ
                            }
                            _ => panic!("Unexpected value {:?}", value),
                        }
                    })
            });
            typ = try!(next_type.ok_or_else(move || {
                Error::UndefinedField(typ.into_owned(), field_name.into())
            }));
        }
        Ok((value, typ))
    }

    pub fn get_metadata(&self, name_str: &str) -> Result<&Metadata> {
        let globals = &self.globals;
        let name = Name::new(name_str);
        let mut components = name.components();
        let global = match components.next() {
            Some(comp) => {
                try!(globals.get(comp)
                    .or_else(|| {
                        components = name.name().components();
                        globals.get(name.module().as_str())
                    })
                    .ok_or_else(|| Error::MetadataDoesNotExist(name_str.into())))
            }
            None => return Err(Error::MetadataDoesNotExist(name_str.into())),
        };

        let mut metadata = &global.metadata;
        for field_name in components {
            metadata = try!(metadata.module
                .get(field_name)
                .ok_or_else(|| Error::MetadataDoesNotExist(name_str.into())));
        }
        Ok(metadata)
    }
}

impl GlobalVmState {
    /// Creates a new virtual machine
    pub fn new() -> GlobalVmState {
        let mut vm = GlobalVmState {
            env: RwLock::new(VmEnv {
                globals: FnvMap::default(),
                type_infos: TypeInfos::new(),
            }),
            generics: RwLock::new(FnvMap::default()),
            typeids: RwLock::new(FnvMap::default()),
            interner: RwLock::new(Interner::new()),
            gc: Mutex::new(Gc::new(0, usize::MAX)),
            macros: MacroEnv::new(),
            generation_0_threads: RwLock::new(Vec::new()),
        };
        vm.add_types()
            .unwrap();
        vm
    }

    fn add_types(&mut self) -> StdResult<(), (TypeId, ArcType)> {
        use api::generic::A;
        use api::Generic;
        fn add_type<T: Any>(ids: &mut FnvMap<TypeId, ArcType>,
                            env: &mut VmEnv,
                            name: &str,
                            typ: ArcType) {
            ids.insert(TypeId::of::<T>(), typ);
            // Insert aliases so that `find_info` can retrieve information about the primitives
            env.type_infos.id_to_type.insert(name.into(),
                                             Alias::from(AliasData {
                                                 name: Symbol::from(name),
                                                 args: Vec::new(),
                                                 typ: None,
                                             }));
        }

        {
            let ids = self.typeids.get_mut().unwrap();
            let env = self.env.get_mut().unwrap();
            add_type::<()>(ids, env, "()", Type::unit());
            add_type::<VmInt>(ids, env, "Int", Type::int());
            add_type::<u8>(ids, env, "Byte", Type::byte());
            add_type::<f64>(ids, env, "Float", Type::float());
            add_type::<::std::string::String>(ids, env, "String", Type::string());
            add_type::<char>(ids, env, "Char", Type::char());
        }
        self.register_type::<IO<Generic<A>>>("IO", &["a"]).unwrap();
        self.register_type::<Lazy<Generic<A>>>("Lazy", &["a"]).unwrap();
        self.register_type::<RootedThread>("Thread", &[]).unwrap();
        Ok(())
    }

    pub fn new_function(&self, f: CompiledFunction) -> Result<GcPtr<BytecodeFunction>> {
        new_bytecode(&mut self.gc.lock().unwrap(), self, f)
    }

    pub fn get_type<T: ?Sized + Any>(&self) -> ArcType {
        let id = TypeId::of::<T>();
        self.typeids
            .read()
            .unwrap()
            .get(&id)
            .cloned()
            .unwrap_or_else(|| panic!("Expected type to be inserted before get_type call"))
    }

    /// Checks if a global exists called `name`
    pub fn global_exists(&self, name: &str) -> bool {
        self.env.read().unwrap().globals.get(name).is_some()
    }

    /// TODO dont expose this directly
    pub fn set_global(&self,
                      id: Symbol,
                      typ: ArcType,
                      metadata: Metadata,
                      value: Value)
                      -> Result<()> {
        let mut env = self.env.write().unwrap();
        let globals = &mut env.globals;
        let global = Global {
            id: id.clone(),
            typ: typ,
            metadata: metadata,
            value: value,
        };
        globals.insert(StdString::from(id.as_ref()), global);
        Ok(())
    }

    pub fn get_generic(&self, name: &str) -> ArcType {
        let mut generics = self.generics.write().unwrap();
        if let Some(g) = generics.get(name) {
            return g.clone();
        }
        let g: ArcType = Type::generic(Generic {
            id: Symbol::from(name),
            kind: Kind::typ(),
        });
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
            let arg_types: Vec<_> = args.iter().map(|g| self.get_generic(g)).collect();
            let args = arg_types.iter()
                .map(|g| match **g {
                    Type::Generic(ref g) => g.clone(),
                    _ => unreachable!(),
                })
                .collect();
            let n = Symbol::from(name);
            let typ: ArcType = Type::app(Type::ident(n.clone()), arg_types);
            self.typeids
                .write()
                .unwrap()
                .insert(id, typ.clone());
            let t = self.typeids.read().unwrap().get(&id).unwrap().clone();
            type_infos.id_to_type.insert(name.into(),
                                         Alias::from(AliasData {
                                             name: n,
                                             args: args,
                                             typ: None,
                                         }));
            Ok(t)
        }
    }

    pub fn get_macros(&self) -> &MacroEnv {
        &self.macros
    }

    pub fn intern(&self, s: &str) -> Result<InternedStr> {
        self.interner.write().unwrap().intern(&mut *self.gc.lock().unwrap(), s)
    }

    /// Returns a borrowed structure which implements `CompilerEnv`
    pub fn get_env<'b>(&'b self) -> RwLockReadGuard<'b, VmEnv> {
        self.env.read().unwrap()
    }
}
