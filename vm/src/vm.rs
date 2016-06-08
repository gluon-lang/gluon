use std::borrow::Cow;
use std::sync::{Mutex, RwLock, RwLockReadGuard};
use std::fmt;
use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::result::Result as StdResult;
use std::string::String as StdString;

use base::ast::{Typed, ASTType};
use base::metadata::{Metadata, MetadataEnv};
use base::symbol::{Name, Symbol};
use base::types;
use base::types::{Type, KindEnv, TypeEnv, PrimitiveEnv, TcType, RcKind};
use base::macros::MacroEnv;
use types::*;
use interner::{Interner, InternedStr};
use gc::{Gc, GcPtr, Traverseable, DataDef, Move, WriteOnly};
use array::{Array, Str};
use compiler::{CompiledFunction, Variable, CompilerEnv};
use api::IO;
use lazy::Lazy;

use self::Value::{Int, Float, String, Function, PartialApplication, Closure};

pub use thread::{Thread, RootedThread, Status, Root, RootStr, RootedValue};

mopafy!(Userdata);
pub trait Userdata: ::mopa::Any + Traverseable + Send + Sync {}

impl PartialEq for Userdata {
    fn eq(&self, other: &Userdata) -> bool {
        self as *const _ == other as *const _
    }
}

impl<T> Userdata for T where T: Any + Traverseable + Send + Sync {}

impl fmt::Debug for Userdata {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Userdata")
    }
}

#[derive(Debug)]
pub struct ClosureData {
    pub function: GcPtr<BytecodeFunction>,
    pub upvars: Array<Value>,
}

impl PartialEq for ClosureData {
    fn eq(&self, _: &ClosureData) -> bool {
        false
    }
}

impl Traverseable for ClosureData {
    fn traverse(&self, gc: &mut Gc) {
        self.function.traverse(gc);
        self.upvars.traverse(gc);
    }
}

pub struct ClosureDataDef<'b>(pub GcPtr<BytecodeFunction>, pub &'b [Value]);
impl<'b> Traverseable for ClosureDataDef<'b> {
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc);
        self.1.traverse(gc);
    }
}

unsafe impl<'b> DataDef for ClosureDataDef<'b> {
    type Value = ClosureData;
    fn size(&self) -> usize {
        use std::mem::size_of;
        size_of::<GcPtr<BytecodeFunction>>() + Array::<Value>::size_of(self.1.len())
    }
    fn initialize<'w>(self, mut result: WriteOnly<'w, ClosureData>) -> &'w mut ClosureData {
        unsafe {
            let result = &mut *result.as_mut_ptr();
            result.function = self.0;
            result.upvars.initialize(self.1.iter().cloned());
            result
        }
    }
}

pub struct ClosureInitDef(pub GcPtr<BytecodeFunction>, pub usize);

impl Traverseable for ClosureInitDef {
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc);
    }
}

unsafe impl DataDef for ClosureInitDef {
    type Value = ClosureData;
    fn size(&self) -> usize {
        use std::mem::size_of;
        size_of::<GcPtr<BytecodeFunction>>() + Array::<Value>::size_of(self.1)
    }
    fn initialize<'w>(self, mut result: WriteOnly<'w, ClosureData>) -> &'w mut ClosureData {
        use std::ptr;
        unsafe {
            let result = &mut *result.as_mut_ptr();
            result.function = self.0;
            result.upvars.set_len(self.1);
            for var in &mut result.upvars {
                ptr::write(var, Int(0));
            }
            result
        }
    }
}


#[derive(Debug)]
pub struct BytecodeFunction {
    pub name: Symbol,
    pub args: VMIndex,
    pub instructions: Vec<Instruction>,
    pub inner_functions: Vec<GcPtr<BytecodeFunction>>,
    pub strings: Vec<InternedStr>,
    pub globals: Vec<Value>,
}

impl BytecodeFunction {
    pub fn new(gc: &mut Gc, vm: &GlobalVMState, f: CompiledFunction) -> GcPtr<BytecodeFunction> {
        let CompiledFunction { id,
                               args,
                               instructions,
                               inner_functions,
                               strings,
                               module_globals,
                               .. } = f;
        let fs = inner_functions.into_iter()
                                .map(|inner| BytecodeFunction::new(gc, vm, inner))
                                .collect();
        gc.alloc(Move(BytecodeFunction {
            name: id,
            args: args,
            instructions: instructions,
            inner_functions: fs,
            strings: strings,
            globals: module_globals.into_iter()
                                   .map(|index| {
                                       vm.env.read().unwrap().globals[index.as_ref()].value
                                   })
                                   .collect(),
        }))
    }
}

impl Traverseable for BytecodeFunction {
    fn traverse(&self, gc: &mut Gc) {
        self.inner_functions.traverse(gc);
        self.globals.traverse(gc);
    }
}

pub struct DataStruct {
    pub tag: VMTag,
    pub fields: Array<Value>,
}

impl Traverseable for DataStruct {
    fn traverse(&self, gc: &mut Gc) {
        self.fields.traverse(gc);
    }
}

impl PartialEq for DataStruct {
    fn eq(&self, other: &DataStruct) -> bool {
        self.tag == other.tag && self.fields == other.fields
    }
}

pub type VMInt = isize;

#[derive(Copy, Clone, PartialEq)]
pub enum Value {
    Int(VMInt),
    Float(f64),
    String(GcPtr<Str>),
    Data(GcPtr<DataStruct>),
    Function(GcPtr<ExternFunction>),
    Closure(GcPtr<ClosureData>),
    PartialApplication(GcPtr<PartialApplicationData>),
    Userdata(GcPtr<Box<Userdata>>),
    Thread(GcPtr<Thread>),
}

impl Value {
    pub fn generation(self) -> usize {
        match self {
            String(p) => p.generation(),
            Value::Data(p) => p.generation(),
            Function(p) => p.generation(),
            Closure(p) => p.generation(),
            PartialApplication(p) => p.generation(),
            Value::Userdata(p) => p.generation(),
            Value::Thread(p) => p.generation(),
            Int(_) | Float(_) => 0,
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Callable {
    Closure(GcPtr<ClosureData>),
    Extern(GcPtr<ExternFunction>),
}

impl Callable {
    pub fn name(&self) -> &Symbol {
        match *self {
            Callable::Closure(ref closure) => &closure.function.name,
            Callable::Extern(ref ext) => &ext.id,
        }
    }

    pub fn args(&self) -> VMIndex {
        match *self {
            Callable::Closure(ref closure) => closure.function.args,
            Callable::Extern(ref ext) => ext.args,
        }
    }
}

impl PartialEq for Callable {
    fn eq(&self, _: &Callable) -> bool {
        false
    }
}

impl Traverseable for Callable {
    fn traverse(&self, gc: &mut Gc) {
        match *self {
            Callable::Closure(ref closure) => closure.traverse(gc),
            Callable::Extern(_) => (),
        }
    }
}

#[derive(Debug)]
pub struct PartialApplicationData {
    pub function: Callable,
    pub arguments: Array<Value>,
}

impl PartialEq for PartialApplicationData {
    fn eq(&self, _: &PartialApplicationData) -> bool {
        false
    }
}

impl Traverseable for PartialApplicationData {
    fn traverse(&self, gc: &mut Gc) {
        self.function.traverse(gc);
        self.arguments.traverse(gc);
    }
}

pub struct PartialApplicationDataDef<'b>(pub Callable, pub &'b [Value]);
impl<'b> Traverseable for PartialApplicationDataDef<'b> {
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc);
        self.1.traverse(gc);
    }
}
unsafe impl<'b> DataDef for PartialApplicationDataDef<'b> {
    type Value = PartialApplicationData;
    fn size(&self) -> usize {
        use std::mem::size_of;
        size_of::<Callable>() + Array::<Value>::size_of(self.1.len())
    }
    fn initialize<'w>(self,
                      mut result: WriteOnly<'w, PartialApplicationData>)
                      -> &'w mut PartialApplicationData {
        unsafe {
            let result = &mut *result.as_mut_ptr();
            result.function = self.0;
            result.arguments.initialize(self.1.iter().cloned());
            result
        }
    }
}

impl Traverseable for Value {
    fn traverse(&self, gc: &mut Gc) {
        match *self {
            String(ref data) => data.traverse(gc),
            Value::Data(ref data) => data.traverse(gc),
            Function(ref data) => data.traverse(gc),
            Closure(ref data) => data.traverse(gc),
            Value::Userdata(ref data) => data.traverse(gc),
            PartialApplication(ref data) => data.traverse(gc),
            Value::Thread(ref thread) => thread.traverse(gc),
            Int(_) | Float(_) => (),
        }
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        struct Level<'b>(i32, &'b Value);
        struct LevelSlice<'b>(i32, &'b [Value]);
        impl<'b> fmt::Debug for LevelSlice<'b> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let level = self.0;
                if level <= 0 || self.1.is_empty() {
                    return Ok(());
                }
                try!(write!(f, "{:?}", Level(level - 1, &self.1[0])));
                for v in &self.1[1..] {
                    try!(write!(f, ", {:?}", Level(level - 1, v)));
                }
                Ok(())
            }
        }
        impl<'b> fmt::Debug for Level<'b> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let level = self.0;
                if level <= 0 {
                    return Ok(());
                }
                match *self.1 {
                    Int(i) => write!(f, "{:?}", i),
                    Float(x) => write!(f, "{:?}f", x),
                    String(x) => write!(f, "{:?}", &*x),
                    Value::Data(ref data) => {
                        write!(f,
                               "{{{:?}: {:?}}}",
                               data.tag,
                               LevelSlice(level - 1, &data.fields))
                    }
                    Function(ref func) => write!(f, "<EXTERN {:?}>", &**func),
                    Closure(ref closure) => {
                        let p: *const _ = &*closure.function;
                        write!(f, "<{:?} {:?}>", closure.function.name, p)
                    }
                    PartialApplication(ref app) => {
                        let name = match app.function {
                            Callable::Closure(_) => "<CLOSURE>",
                            Callable::Extern(_) => "<EXTERN>",
                        };
                        write!(f,
                               "<App {:?}{:?}>",
                               name,
                               LevelSlice(level - 1, &app.arguments))
                    }
                    Value::Userdata(ref data) => write!(f, "<Userdata {:p}>", &**data),
                    Value::Thread(_) => write!(f, "<thread>"),
                }
            }
        }
        write!(f, "{:?}", Level(3, self))
    }
}

pub struct ExternFunction {
    pub id: Symbol,
    pub args: VMIndex,
    pub function: Box<Fn(&Thread) -> Status + Send + Sync>,
}

impl PartialEq for ExternFunction {
    fn eq(&self, _: &ExternFunction) -> bool {
        false
    }
}

impl fmt::Debug for ExternFunction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // read the v-table pointer of the Fn(..) type and print that
        let p: *const () = unsafe { ::std::mem::transmute_copy(&&*self.function) };
        write!(f, "{:?}", p)
    }
}

impl Traverseable for ExternFunction {
    fn traverse(&self, _: &mut Gc) {}
}

#[derive(Debug)]
pub struct Global {
    pub id: Symbol,
    pub typ: TcType,
    pub metadata: Metadata,
    pub value: Value,
}

impl Traverseable for Global {
    fn traverse(&self, gc: &mut Gc) {
        self.value.traverse(gc);
    }
}

impl Typed for Global {
    type Id = Symbol;
    fn env_type_of(&self, _: &TypeEnv) -> ASTType<Symbol> {
        self.typ.clone()
    }
}

pub struct GlobalVMState {
    env: RwLock<VMEnv>,
    generics: RwLock<HashMap<StdString, TcType>>,
    typeids: RwLock<HashMap<TypeId, TcType>>,
    interner: RwLock<Interner>,
    macros: MacroEnv<Thread>,
    // FIXME These fields should not be public
    pub gc: Mutex<Gc>,
    // List of all generation 0 threads (ie, threads allocated by the global gc). when doing a
    // generation 0 sweep these threads are scanned as generation 0 values may be refered to by any
    // thread
    pub generation_0_threads: RwLock<Vec<GcPtr<Thread>>>,
}

impl Traverseable for GlobalVMState {
    fn traverse(&self, gc: &mut Gc) {
        for g in self.env.read().unwrap().globals.values() {
            g.traverse(gc);
        }
        // Also need to check the interned string table
        self.interner.read().unwrap().traverse(gc);
        self.generation_0_threads.read().unwrap().traverse(gc);
    }
}

/// Type returned from vm functions which may fail
pub type Result<T> = StdResult<T, Error>;

/// A borrowed structure which implements `CompilerEnv`, `TypeEnv` and `KindEnv` allowing the
/// typechecker and compiler to lookup things in the virtual machine.
#[derive(Debug)]
pub struct VMEnv {
    pub type_infos: TypeInfos,
    pub globals: HashMap<StdString, Global>,
}

impl CompilerEnv for VMEnv {
    fn find_var(&self, id: &Symbol) -> Option<Variable<Symbol>> {
        self.globals
            .get(id.as_ref())
            .map(|g| Variable::Global(g.id.clone()))
            .or_else(|| self.type_infos.find_var(id))
    }
}

impl KindEnv for VMEnv {
    fn find_kind(&self, type_name: &Symbol) -> Option<RcKind> {
        self.type_infos
            .find_kind(type_name)
    }
}
impl TypeEnv for VMEnv {
    fn find_type(&self, id: &Symbol) -> Option<&TcType> {
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
                                         ctors.iter().find(|ctor| ctor.0 == *id).map(|t| &t.1)
                                     }
                                     _ => None,
                                 }
                             })
                    })
                    .next()
                    .map(|ctor| ctor)
            })
    }
    fn find_type_info(&self, id: &Symbol) -> Option<&types::Alias<Symbol, TcType>> {
        self.type_infos
            .find_type_info(id)
    }
    fn find_record(&self, fields: &[Symbol]) -> Option<(&TcType, &TcType)> {
        self.type_infos.find_record(fields)
    }
}

impl PrimitiveEnv for VMEnv {
    fn get_bool(&self) -> &TcType {
        self.find_type_info("std.types.Bool")
            .ok()
            .and_then(|alias| match alias {
                Cow::Borrowed(alias) => alias.typ.as_ref(),
                Cow::Owned(_) => panic!("Expected to be able to retrieve a borrowed bool type"),
            })
            .expect("std.types.Bool")
    }
}

impl MetadataEnv for VMEnv {
    fn get_metadata(&self, id: &Symbol) -> Option<&Metadata> {
        self.globals
            .get(AsRef::<str>::as_ref(id))
            .map(|g| &g.metadata)
    }
}

fn map_cow_option<T, U, F>(cow: Cow<T>, f: F) -> Option<Cow<U>>
    where T: Clone,
          U: Clone,
          F: FnOnce(&T) -> Option<&U>
{
    match cow {
        Cow::Borrowed(b) => f(b).map(Cow::Borrowed),
        Cow::Owned(o) => f(&o).map(|u| Cow::Owned(u.clone())),
    }
}

impl VMEnv {
    pub fn find_type_info(&self, name: &str) -> Result<Cow<types::Alias<Symbol, TcType>>> {
        if let Some(alias) = self.type_infos.id_to_type.get(name) {
            return Ok(Cow::Borrowed(alias));
        }
        let name = Name::new(name);
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

    pub fn get_binding(&self, name: &str) -> Result<(Value, Cow<TcType>)> {
        use base::instantiate::{Instantiator, AliasInstantiator};
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
        let instantiator = Instantiator::new();
        let instantiator = AliasInstantiator::new(&instantiator, self);

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
                Cow::Borrowed(typ) => instantiator.remove_aliases_cow(typ),
                Cow::Owned(typ) => Cow::Owned(instantiator.remove_aliases(typ)),
            };
            // HACK Can't return the data directly due to the use of cow on the type
            let next_type = map_cow_option(typ.clone(), |typ| {
                match **typ {
                    Type::Record { ref fields, .. } => {
                        fields.iter()
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
                    }
                    _ => None,
                }
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

/// Definition for data values in the VM
pub struct Def<'b> {
    pub tag: VMTag,
    pub elems: &'b [Value],
}
unsafe impl<'b> DataDef for Def<'b> {
    type Value = DataStruct;
    fn size(&self) -> usize {
        use std::mem::size_of;
        size_of::<usize>() + Array::<Value>::size_of(self.elems.len())
    }
    fn initialize<'w>(self, mut result: WriteOnly<'w, DataStruct>) -> &'w mut DataStruct {
        unsafe {
            let result = &mut *result.as_mut_ptr();
            result.tag = self.tag;
            result.fields.initialize(self.elems.iter().cloned());
            result
        }
    }
}

impl<'b> Traverseable for Def<'b> {
    fn traverse(&self, gc: &mut Gc) {
        self.elems.traverse(gc);
    }
}

impl GlobalVMState {
    /// Creates a new virtual machine
    pub fn new() -> GlobalVMState {
        let vm = GlobalVMState {
            env: RwLock::new(VMEnv {
                globals: HashMap::new(),
                type_infos: TypeInfos::new(),
            }),
            generics: RwLock::new(HashMap::new()),
            typeids: RwLock::new(HashMap::new()),
            interner: RwLock::new(Interner::new()),
            gc: Mutex::new(Gc::new(0)),
            macros: MacroEnv::new(),
            generation_0_threads: RwLock::new(Vec::new()),
        };
        vm.add_types()
          .unwrap();
        vm
    }

    fn add_types(&self) -> StdResult<(), (TypeId, TcType)> {
        use api::generic::A;
        use api::Generic;
        {
            let mut ids = self.typeids.write().unwrap();
            ids.insert(TypeId::of::<()>(), Type::unit());
            ids.insert(TypeId::of::<VMInt>(), Type::int());
            ids.insert(TypeId::of::<i32>(), Type::int());
            ids.insert(TypeId::of::<u32>(), Type::int());
            ids.insert(TypeId::of::<f64>(), Type::float());
            ids.insert(TypeId::of::<::std::string::String>(), Type::string());
            ids.insert(TypeId::of::<char>(), Type::char());
        }
        let _ = self.register_type::<IO<Generic<A>>>("IO", &["a"]);
        let _ = self.register_type::<Lazy<Generic<A>>>("Lazy", &["a"]);
        let _ = self.register_type::<RootedThread>("Thread", &[]);
        Ok(())
    }

    pub fn new_function(&self, f: CompiledFunction) -> GcPtr<BytecodeFunction> {
        BytecodeFunction::new(&mut self.gc.lock().unwrap(), self, f)
    }

    pub fn get_type<T: ?Sized + Any>(&self) -> TcType {
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
                      typ: TcType,
                      metadata: Metadata,
                      value: Value)
                      -> Result<()> {
        let mut env = self.env.write().unwrap();
        let globals = &mut env.globals;
        if globals.contains_key(id.as_ref()) {
            return Err(Error::GlobalAlreadyExists(id));
        }
        let global = Global {
            id: id.clone(),
            typ: typ,
            metadata: metadata,
            value: value,
        };
        globals.insert(StdString::from(id.as_ref()), global);
        Ok(())
    }

    pub fn get_generic(&self, name: &str) -> TcType {
        let mut generics = self.generics.write().unwrap();
        if let Some(g) = generics.get(name) {
            return g.clone();
        }
        let g: TcType = Type::generic(types::Generic {
            id: Symbol::new(name),
            kind: types::Kind::star(),
        });
        generics.insert(name.into(), g.clone());
        g
    }

    /// Registers a new type called `name`
    pub fn register_type<T: ?Sized + Any>(&self, name: &str, args: &[&str]) -> Result<TcType> {
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
            let n = Symbol::new(name);
            let typ: TcType = Type::data(Type::id(n.clone()), arg_types);
            self.typeids
                .write()
                .unwrap()
                .insert(id, typ.clone());
            let t = self.typeids.read().unwrap().get(&id).unwrap().clone();
            type_infos.id_to_type.insert(name.into(),
                                         types::Alias::from(types::AliasData {
                                             name: n,
                                             args: args,
                                             typ: None,
                                         }));
            Ok(t)
        }
    }

    pub fn get_macros(&self) -> &MacroEnv<Thread> {
        &self.macros
    }

    pub fn intern(&self, s: &str) -> InternedStr {
        self.interner.write().unwrap().intern(&mut *self.gc.lock().unwrap(), s)
    }

    /// Returns a borrowed structure which implements `CompilerEnv`
    pub fn get_env<'b>(&'b self) -> RwLockReadGuard<'b, VMEnv> {
        self.env.read().unwrap()
    }
}

quick_error! {
    #[derive(Debug, PartialEq)]
    pub enum Error {
        Yield {
        }
        Dead {
        }
        UndefinedBinding(symbol: StdString) {
            display("Binding `{}` is not defined", symbol)
        }
        UndefinedField(typ: TcType, field: StdString) {
            display("Type `{}` does not have the field `{}`", typ, field)
        }
        TypeAlreadyExists(symbol: StdString) {
            display("Type `{}` already exists", symbol)
        }
        GlobalAlreadyExists(symbol: Symbol) {
            display("Global `{}` already exists", symbol)
        }
        MetadataDoesNotExist(symbol: StdString) {
            display("No metadata exists for `{}`", symbol)
        }
        WrongType(expected: TcType, actual: TcType) {
            display("Expected a value of type `{}` but the inferred type was `{}`",
                    expected, actual)
        }
        Message(err: StdString) {
            display("{}", err)
        }
    }
}
