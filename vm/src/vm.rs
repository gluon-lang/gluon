use std::cell::{RefCell, Ref};
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

use self::Value::{Int, Float, String, Data, Function, PartialApplication, Closure};

pub use thread::{Thread, RootedThread, Status, Root, RootStr, RootedValue};

mopafy!(Userdata);
pub trait Userdata: ::mopa::Any + Traverseable {}

impl<T> Userdata for T where T: Any + Traverseable
{}

impl fmt::Debug for Userdata {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Userdata")
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Userdata_ {
    pub data: GcPtr<Box<Userdata>>,
}

impl Userdata_ {
    pub fn new<T: Userdata>(vm: &Thread, v: T) -> Userdata_ {
        let v: Box<Userdata> = Box::new(v);
        Userdata_ { data: vm.gc.borrow_mut().alloc(Move(v)) }
    }

    fn ptr(&self) -> *const () {
        let p: *const _ = &*self.data;
        p as *const ()
    }
}
impl PartialEq for Userdata_ {
    fn eq(&self, o: &Userdata_) -> bool {
        self.ptr() == o.ptr()
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
                                   .map(|index| vm.env.borrow().globals[index.as_ref()].value)
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
    Userdata(Userdata_),
    Thread(GcPtr<Thread>),
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
            Data(ref data) => data.traverse(gc),
            Function(ref data) => data.traverse(gc),
            Closure(ref data) => data.traverse(gc),
            Value::Userdata(ref data) => data.data.traverse(gc),
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
                if level <= 0 {
                    return Ok(());
                }
                for v in self.1 {
                    try!(write!(f, "{:?}", Level(level - 1, v)));
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
                    Data(ref data) => {
                        write!(f,
                               "{{{:?} {:?}}}",
                               data.tag,
                               LevelSlice(level - 1, &data.fields))
                    }
                    Function(ref func) => write!(f, "<EXTERN {:?}>", &**func),
                    Closure(ref closure) => {
                        let p: *const _ = &*closure.function;
                        write!(f,
                               "<{:?} {:?} {:?}>",
                               closure.function.name,
                               p,
                               LevelSlice(level - 1, &closure.upvars))
                    }
                    PartialApplication(ref app) => {
                        let name = match app.function {
                            Callable::Closure(_) => "<CLOSURE>",
                            Callable::Extern(_) => "<EXTERN>",
                        };
                        write!(f,
                               "<App {:?} {:?}>",
                               name,
                               LevelSlice(level - 1, &app.arguments))
                    }
                    Value::Userdata(ref data) => write!(f, "<Userdata {:?}>", data.ptr()),
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
    pub function: Box<Fn(&Thread) -> Status + 'static>,
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
    env: RefCell<VMEnv>,
    generics: RefCell<HashMap<StdString, TcType>>,
    typeids: RefCell<HashMap<TypeId, TcType>>,
    interner: RefCell<Interner>,
    pub gc: RefCell<Gc>,
    macros: MacroEnv<Thread>,
}

impl Traverseable for GlobalVMState {
    fn traverse(&self, gc: &mut Gc) {
        for g in self.env.borrow().globals.values() {
            g.traverse(gc);
        }
        // Also need to check the interned string table
        self.interner.borrow().traverse(gc);
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
            .and_then(|alias| alias.typ.as_ref())
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

impl VMEnv {
    pub fn find_type_info(&self, name: &str) -> Result<&types::Alias<Symbol, TcType>> {
        if let Some(alias) = self.type_infos.id_to_type.get(name) {
            return Ok(alias);
        }
        let name = Name::new(name);
        let typ = try!(self.get_binding_type(name.module().as_str()));
        let maybe_type_info = match **typ {
            Type::Record { ref types, .. } => {
                let field_name = name.name();
                types.iter()
                     .find(|field| field.name.as_ref() == field_name.as_str())
                     .map(|field| &field.typ)
            }
            _ => None,
        };
        maybe_type_info.ok_or_else(|| {
            Error::Message(format!("'{}' cannot be accessed by the field '{}'",
                                   typ,
                                   name.name()))
        })
    }

    pub fn get_binding_type(&self, name: &str) -> Result<&TcType> {
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
                return Err(Error::Message(format!("Could not retrieve binding `{}`", name)));
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
            return Ok(&global.typ);
        }
        let remaining_fields = Name::new(&name[remaining_offset..]);

        let mut typ = &global.typ;
        for field_name in remaining_fields.components() {
            let next = match **typ {
                Type::Record { ref fields, .. } => {
                    fields.iter()
                          .find(|field| field.name.as_ref() == field_name)
                          .map(|field| &field.typ)
                }
                _ => None,
            };
            typ = try!(next.ok_or_else(|| {
                Error::Message(format!("'{}' cannot be accessed by the field '{}'",
                                       typ,
                                       field_name))
            }));
        }
        Ok(typ)
    }

    pub fn get_metadata(&self, name: &str) -> Result<&Metadata> {
        let globals = &self.globals;
        let name = Name::new(name);
        let mut components = name.components();
        let global = match components.next() {
            Some(comp) => {
                try!(globals.get(comp)
                            .or_else(|| {
                                components = name.name().components();
                                globals.get(name.module().as_str())
                            })
                            .ok_or_else(|| {
                                Error::Message(format!("There is no metadata for '{}'", name))
                            }))
            }
            None => return Err(Error::Message(format!("There is no metadata for '{}'", name))),
        };

        let mut metadata = &global.metadata;
        for field_name in components {
            metadata = try!(metadata.module.get(field_name).ok_or_else(|| {
                Error::Message(format!("There is no metadata for '{}'", name))
            }));
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
            env: RefCell::new(VMEnv {
                globals: HashMap::new(),
                type_infos: TypeInfos::new(),
            }),
            generics: RefCell::new(HashMap::new()),
            typeids: RefCell::new(HashMap::new()),
            interner: RefCell::new(Interner::new()),
            gc: RefCell::new(Gc::new()),
            macros: MacroEnv::new(),
        };
        vm.add_types()
          .unwrap();
        vm
    }

    fn add_types(&self) -> StdResult<(), (TypeId, TcType)> {
        use api::generic::A;
        use api::Generic;
        {
            let mut ids = self.typeids.borrow_mut();
            ids.insert(TypeId::of::<()>(), Type::unit());
            ids.insert(TypeId::of::<VMInt>(), Type::int());
            ids.insert(TypeId::of::<i32>(), Type::int());
            ids.insert(TypeId::of::<u32>(), Type::int());
            ids.insert(TypeId::of::<f64>(), Type::float());
            ids.insert(TypeId::of::<::std::string::String>(), Type::string());
            ids.insert(TypeId::of::<char>(), Type::char());
        }
        let args = vec![types::Generic {
                            id: Symbol::new("a"),
                            kind: types::Kind::star(),
                        }];
        let _ = self.register_type::<IO<Generic<A>>>("IO", args.clone());
        let _ = self.register_type::<Lazy<Generic<A>>>("Lazy", args);
        let _ = self.register_type::<RootedThread>("Thread", vec![]);
        Ok(())
    }

    pub fn new_function(&self, f: CompiledFunction) -> GcPtr<BytecodeFunction> {
        BytecodeFunction::new(&mut self.gc.borrow_mut(), self, f)
    }

    pub fn get_type<T: ?Sized + Any>(&self) -> TcType {
        let id = TypeId::of::<T>();
        self.typeids
            .borrow()
            .get(&id)
            .cloned()
            .unwrap_or_else(|| panic!("Expected type to be inserted before get_type call"))
    }

    /// Checks if a global exists called `name`
    pub fn global_exists(&self, name: &str) -> bool {
        self.env.borrow().globals.get(name).is_some()
    }

    /// TODO dont expose this directly
    pub fn set_global(&self,
                      id: Symbol,
                      typ: TcType,
                      metadata: Metadata,
                      value: Value)
                      -> Result<()> {
        let mut env = self.env.borrow_mut();
        let globals = &mut env.globals;
        if globals.contains_key(id.as_ref()) {
            return Err(Error::Message(format!("{} is already defined", id)));
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
        let mut generics = self.generics.borrow_mut();
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
    pub fn register_type<T: ?Sized + Any>(&self,
                                          name: &str,
                                          args: Vec<types::Generic<Symbol>>)
                                          -> Result<TcType> {
        let mut env = self.env.borrow_mut();
        let type_infos = &mut env.type_infos;
        if type_infos.id_to_type.contains_key(name) {
            Err(Error::Message(format!("Type '{}' has already been registered", name)))
        } else {
            let id = TypeId::of::<T>();
            let arg_types = args.iter().map(|g| Type::generic(g.clone())).collect();
            let n = Symbol::new(name);
            let typ: TcType = Type::data(Type::id(n.clone()), arg_types);
            self.typeids
                .borrow_mut()
                .insert(id, typ.clone());
            let t = self.typeids.borrow().get(&id).unwrap().clone();
            type_infos.id_to_type.insert(name.into(),
                                         types::Alias {
                                             name: n,
                                             args: args,
                                             typ: None,
                                         });
            Ok(t)
        }
    }

    pub fn get_macros(&self) -> &MacroEnv<Thread> {
        &self.macros
    }

    pub fn intern(&self, s: &str) -> InternedStr {
        self.interner.borrow_mut().intern(&mut *self.gc.borrow_mut(), s)
    }

    /// Returns a borrowed structure which implements `CompilerEnv`
    pub fn get_env<'b>(&'b self) -> Ref<'b, VMEnv> {
        self.env.borrow()
    }

    pub fn new_data(&self, tag: VMTag, fields: &[Value]) -> Value {
        Data(self.gc.borrow_mut().alloc(Def {
            tag: tag,
            elems: fields,
        }))
    }
}

quick_error! {
    #[derive(Debug, PartialEq)]
    pub enum Error {
        Yield {
        }
        Dead {
        }
        Message(err: StdString) {
            display("{}", err)
        }
    }
}
