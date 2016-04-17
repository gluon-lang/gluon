use std::cell::{RefCell, Ref};
use std::fmt;
use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::cmp::Ordering;
use std::ops::{Add, Sub, Mul, Div, Deref};
use std::result::Result as StdResult;
use std::string::String as StdString;
use std::sync::Arc;

use base::ast::{Typed, ASTType};
use base::metadata::{Metadata, MetadataEnv};
use base::symbol::{Name, Symbol};
use base::types;
use base::types::{Type, KindEnv, TypeEnv, TcType, RcKind};
use base::macros::MacroEnv;
use types::*;
use interner::{Interner, InternedStr};
use gc::{Gc, GcPtr, Traverseable, DataDef, Move, WriteOnly};
use array::{Array, Str};
use compiler::{CompiledFunction, Variable, CompilerEnv};
use api::{Getable, IO, Pushable, VMType};
use lazy::Lazy;

use self::Value::{Int, Float, String, Data, Function, PartialApplication, Closure};


use stack::{State, Stack, StackFrame};

mopafy!(Userdata);
pub trait Userdata: ::mopa::Any + Traverseable {}

impl<T> Userdata for T where T: Any + Traverseable {}

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
    pub fn new<T: Userdata>(vm: &VM, v: T) -> Userdata_ {
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
    args: VMIndex,
    instructions: Vec<Instruction>,
    inner_functions: Vec<GcPtr<BytecodeFunction>>,
    strings: Vec<InternedStr>,
    globals: Vec<Value>,
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
    function: Callable,
    arguments: Array<Value>,
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

struct PartialApplicationDataDef<'b>(Callable, &'b [Value]);
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

/// A rooted value
#[derive(Clone)]
pub struct RootedValue<'vm> {
    vm: &'vm VM,
    value: Value,
}

impl<'vm> Drop for RootedValue<'vm> {
    fn drop(&mut self) {
        // TODO not safe if the root changes order of being dropped with another root
        self.vm.rooted_values.borrow_mut().pop();
    }
}

impl<'vm> fmt::Debug for RootedValue<'vm> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.value)
    }
}

impl<'vm> Deref for RootedValue<'vm> {
    type Target = Value;
    fn deref(&self) -> &Value {
        &self.value
    }
}

impl<'vm> RootedValue<'vm> {
    pub fn vm(&self) -> &'vm VM {
        self.vm
    }
}

/// A rooted userdata value
pub struct Root<'vm, T: ?Sized + 'vm> {
    roots: &'vm RefCell<Vec<GcPtr<Traverseable + 'static>>>,
    ptr: *const T,
}

impl<'vm, T: ?Sized> Drop for Root<'vm, T> {
    fn drop(&mut self) {
        // TODO not safe if the root changes order of being dropped with another root
        self.roots.borrow_mut().pop();
    }
}

impl<'vm, T: ?Sized> Deref for Root<'vm, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.ptr }
    }
}

/// A rooted string
pub struct RootStr<'vm>(Root<'vm, Str>);

impl<'vm> Deref for RootStr<'vm> {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}


/// Enum signaling a successful or unsuccess ful call to an extern function.
/// If an error occured the error message is expected to be on the top of the stack.
#[derive(Eq, PartialEq)]
#[repr(C)]
pub enum Status {
    Ok,
    Yield,
    Error,
}

pub struct ExternFunction {
    pub id: Symbol,
    pub args: VMIndex,
    pub function: Box<Fn(&VM) -> Status + 'static>,
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
struct Global {
    id: Symbol,
    typ: TcType,
    metadata: Metadata,
    value: Value,
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
    gc: RefCell<Gc>,
    macros: MacroEnv<VM>,
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

/// Representation of the virtual machine
pub struct Thread {
    global_state: Arc<GlobalVMState>,
    roots: RefCell<Vec<GcPtr<Traverseable>>>,
    rooted_values: RefCell<Vec<Value>>,
    stack: RefCell<Stack>,
}

impl Deref for Thread {
    type Target = GlobalVMState;
    fn deref(&self) -> &GlobalVMState {
        &self.global_state
    }
}

impl Traverseable for Thread {
    fn traverse(&self, gc: &mut Gc) {
        self.traverse_fields_except_stack(gc);
        self.stack.borrow().get_values().traverse(gc);
    }
}

impl PartialEq for Thread {
    fn eq(&self, other: &Thread) -> bool {
        self as *const _ == other as *const _
    }
}

pub struct VM(GcPtr<Thread>);

impl Drop for VM {
    fn drop(&mut self) {
        let p = self.roots.borrow_mut().pop().expect("VM ptr");
        assert!(&*p as *const Traverseable as *const () == &*self.0 as *const Thread as *const ())
    }
}

impl Deref for VM {
    type Target = Thread;
    fn deref(&self) -> &Thread {
        &self.0
    }
}

impl Traverseable for VM {
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc);
    }
}

/// Type returned from vm functions which may fail
pub type Result<T> = StdResult<T, Error>;

/// A borrowed structure which implements `CompilerEnv`, `TypeEnv` and `KindEnv` allowing the
/// typechecker and compiler to lookup things in the virtual machine.
#[derive(Debug)]
pub struct VMEnv {
    type_infos: TypeInfos,
    globals: HashMap<StdString, Global>,
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

struct Roots<'b> {
    vm: &'b VM,
    stack: &'b Stack,
}
impl<'b> Traverseable for Roots<'b> {
    fn traverse(&self, gc: &mut Gc) {
        // Since this vm's stack is already borrowed in self we need to manually mark it to prevent
        // it from being traversed normally
        gc.mark(self.vm.0);
        self.stack.get_values().traverse(gc);

        // Traverse the vm's fields, avoiding the stack which is traversed above
        self.vm.traverse_fields_except_stack(gc);
    }
}

impl Thread {
    /// Pushes a value to the top of the stack
    pub fn push(&self, v: Value) {
        self.stack.borrow_mut().push(v)
    }

    /// Removes the top value from the stack
    pub fn pop(&self) -> Value {
        self.stack
            .borrow_mut()
            .pop()
    }

    /// Returns the current stackframe
    pub fn current_frame(&self) -> StackFrame {
        StackFrame::current(&self.stack)
    }

    fn traverse_fields_except_stack(&self, gc: &mut Gc) {
        self.global_state.traverse(gc);
        self.roots.borrow().traverse(gc);
        self.rooted_values.borrow().traverse(gc);
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
            ids.insert(TypeId::of::<bool>(), Type::bool());
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
        let _ = self.register_type::<Thread>("Thread", vec![]);
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
            let typ: TcType = Type::data(types::TypeConstructor::Data(n.clone()), arg_types);
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

    pub fn get_macros(&self) -> &MacroEnv<VM> {
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

impl VM {
    pub fn new() -> VM {
        let vm = Thread {
            global_state: Arc::new(GlobalVMState::new()),
            stack: RefCell::new(Stack::new()),
            roots: RefCell::new(Vec::new()),
            rooted_values: RefCell::new(Vec::new()),
        };
        let mut gc = Gc::new();
        let vm = VM::from_gc_ptr(gc.alloc(Move(vm)));
        *vm.gc.borrow_mut() = gc;
        // Enter the top level scope
        StackFrame::frame(vm.stack.borrow_mut(), 0, State::Unknown);
        vm
    }

    pub fn new_thread(&self) -> Thread {
        let vm = Thread {
            global_state: self.global_state.clone(),
            stack: RefCell::new(Stack::new()),
            roots: RefCell::new(Vec::new()),
            rooted_values: RefCell::new(Vec::new()),
        };
        // Enter the top level scope
        StackFrame::frame(vm.stack.borrow_mut(), 0, State::Unknown);
        vm
    }

    pub fn new_vm(&self) -> VM {
        let vm = self.new_thread();
        VM::from_gc_ptr(self.alloc(&self.stack.borrow(), Move(vm)))
    }

    pub fn from_gc_ptr(p: GcPtr<Thread>) -> VM {
        let vm = VM(p);
        vm.roots.borrow_mut().push(vm.0.as_traverseable());
        vm
    }

    /// Creates a new global value at `name`.
    /// Fails if a global called `name` already exists.
    pub fn define_global<'vm, T>(&'vm self, name: &str, value: T) -> Result<()>
        where T: Pushable<'vm>
    {
        let (status, value) = {
            let mut stack = self.current_frame();
            let status = value.push(self, &mut stack);
            (status, stack.pop())
        };
        if status == Status::Error {
            return Err(Error::Message(format!("{:?}", value)));
        }
        self.set_global(Symbol::new(name),
                        T::make_type(self),
                        Metadata::default(),
                        value)
    }

    /// Retrieves the global called `name`.
    /// Fails if the global does not exist or it does not have the correct type.
    pub fn get_global<'vm, T>(&'vm self, name: &str) -> Result<T>
        where T: Getable<'vm> + VMType
    {
        let mut components = Name::new(name).components();
        let env = self.env.borrow();
        let globals = &env.globals;
        let global = match components.next() {
            Some(comp) => {
                try!(globals.get(comp)
                            .or_else(|| {
                                // We access by the the full name so no components should be left
                                // to walk through
                                for _ in components.by_ref() {
                                }
                                globals.get(name)
                            })
                            .ok_or_else(|| {
                                Error::Message(format!("Could not retrieve global `{}`", name))
                            }))
            }
            None => return Err(Error::Message(format!("'{}' is not a valid name", name))),
        };
        let mut typ = &global.typ;
        let mut value = global.value;
        // If there are any remaining components iterate through them, accessing each field
        for field_name in components {
            let next = match **typ {
                Type::Record { ref fields, .. } => {
                    fields.iter()
                          .enumerate()
                          .find(|&(_, field)| field.name.as_ref() == field_name)
                          .map(|(offset, field)| (offset, &field.typ))
                }
                _ => None,
            };
            let (offset, next_type) = try!(next.ok_or_else(|| {
                Error::Message(format!("'{}' cannot be accessed by the field '{}'",
                                       typ,
                                       field_name))
            }));
            typ = next_type;
            value = match value {
                Value::Data(data) => data.fields[offset],
                _ => panic!(),
            };
        }

        // Finally check that type of the returned value is correct
        if *typ == T::make_type(self) {
            T::from_value(self, value)
                .ok_or_else(|| Error::Message(format!("Could not retrieve global `{}`", name)))
        } else {
            Err(Error::Message(format!("Could not retrieve global `{}` as the types did not \
                                        match",
                                       name)))
        }
    }

    pub fn find_type_info(&self, name: &str) -> Result<types::Alias<Symbol, TcType>> {
        let env = self.env.borrow();
        env.find_type_info(name)
           .map(|alias| alias.clone())
    }

    /// Returns the current stackframe
    pub fn release_lock<'vm>(&'vm self, lock: ::stack::Lock) -> StackFrame<'vm> {
        self.stack.borrow_mut().release_lock(lock);
        self.current_frame()
    }

    /// Returns the current stackframe
    pub fn current_frame<'vm>(&'vm self) -> StackFrame<'vm> {
        StackFrame::current(&self.stack)
    }

    /// Runs a garbage collection.
    pub fn collect(&self) {
        let stack = self.stack.borrow();
        self.with_roots(&stack, |gc, roots| {
            unsafe {
                gc.collect(roots);
            }
        })
    }

    /// Roots a userdata
    pub fn root<'vm, T: Userdata>(&'vm self, v: GcPtr<Box<Userdata>>) -> Option<Root<'vm, T>> {
        v.downcast_ref::<T>()
         .map(|ptr| {
             self.roots.borrow_mut().push(v.as_traverseable());
             Root {
                 roots: &self.roots,
                 ptr: ptr,
             }
         })
    }

    /// Roots a string
    pub fn root_string<'vm>(&'vm self, ptr: GcPtr<Str>) -> RootStr<'vm> {
        self.roots.borrow_mut().push(ptr.as_traverseable());
        RootStr(Root {
            roots: &self.roots,
            ptr: &*ptr,
        })
    }

    /// Roots a value
    pub fn root_value(&self, value: Value) -> RootedValue {
        self.rooted_values.borrow_mut().push(value);
        RootedValue {
            vm: self,
            value: value,
        }
    }

    /// Allocates a new value from a given `DataDef`.
    /// Takes the stack as it may collect if the collection limit has been reached.
    pub fn alloc<D>(&self, stack: &Stack, def: D) -> GcPtr<D::Value>
        where D: DataDef + Traverseable,
              D::Value: Sized
    {
        self.with_roots(stack,
                        |gc, roots| unsafe { gc.alloc_and_collect(roots, def) })
    }

    fn with_roots<F, R>(&self, stack: &Stack, f: F) -> R
        where F: for<'b> FnOnce(&mut Gc, Roots<'b>) -> R
    {
        // For this to be safe we require that the received stack is the same one that is in this
        // VM
        assert!(unsafe {
            stack as *const _ as usize >= &self.stack as *const _ as usize &&
            stack as *const _ as usize <= (&self.stack as *const _).offset(1) as usize
        });
        let roots = Roots {
            vm: self,
            stack: stack,
        };
        let mut gc = self.gc.borrow_mut();
        f(&mut gc, roots)
    }

    pub fn add_bytecode(&self,
                        name: &str,
                        typ: TcType,
                        args: VMIndex,
                        instructions: Vec<Instruction>)
                        -> VMIndex {
        let id = Symbol::new(name);
        let mut compiled_fn = CompiledFunction::new(args, id.clone(), typ.clone());
        compiled_fn.instructions = instructions;
        let f = self.new_function(compiled_fn);
        let closure = self.alloc(&self.stack.borrow(), ClosureDataDef(f, &[]));
        let mut env = self.env.borrow_mut();
        env.globals.insert(name.into(),
                           Global {
                               id: id,
                               typ: typ,
                               metadata: Metadata::default(),
                               value: Closure(closure),
                           });
        env.globals.len() as VMIndex - 1
    }

    /// Pushes a value to the top of the stack
    pub fn push(&self, v: Value) {
        self.stack.borrow_mut().push(v)
    }

    /// Removes the top value from the stack
    pub fn pop(&self) -> Value {
        self.stack
            .borrow_mut()
            .pop()
    }

    ///Calls a module, allowed to to run IO expressions
    pub fn call_module(&self, typ: &TcType, closure: GcPtr<ClosureData>) -> Result<Value> {
        let value = try!(self.call_bytecode(closure));
        if let Type::Data(types::TypeConstructor::Data(ref id), _) = **typ {
            let is_io = {
                let env = self.env.borrow();
                env.type_infos
                   .find_type_info(&Symbol::new("IO"))
                   .map(|alias| *id == alias.name)
                   .unwrap_or(false)
            };
            if is_io {
                debug!("Run IO {:?}", value);
                self.push(Int(0));// Dummy value to fill the place of the function for TailCall
                self.push(value);
                self.push(Int(0));
                let mut stack = StackFrame::frame(self.stack.borrow_mut(), 2, State::Unknown);
                stack = try!(self.call_function(stack, 1))
                            .expect("call_module to have the stack remaining");
                let result = stack.pop();
                while stack.len() > 0 {
                    stack.pop();
                }
                stack.exit_scope();
                return Ok(result);
            }
        }
        Ok(value)
    }

    /// Calls a function on the stack.
    /// When this function is called it is expected that the function exists at
    /// `stack.len() - args - 1` and that the arguments are of the correct type
    pub fn call_function<'b>(&'b self,
                             mut stack: StackFrame<'b>,
                             args: VMIndex)
                             -> Result<Option<StackFrame<'b>>> {
        stack = try!(self.do_call(stack, args));
        self.execute(stack)
    }

    pub fn resume(&self) -> Result<()> {
        let stack = self.current_frame();
        if stack.stack.get_frames().len() == 1 {
            // Only the top level frame left means that the thread has finished
            return Err(Error::Dead);
        }
        self.execute(stack)
            .map(|_| ())
    }

    fn call_bytecode(&self, closure: GcPtr<ClosureData>) -> Result<Value> {
        self.push(Closure(closure));
        let stack = StackFrame::frame(self.stack.borrow_mut(), 0, State::Closure(closure));
        try!(self.execute(stack));
        let mut stack = self.stack.borrow_mut();
        Ok(stack.pop())
    }

    fn execute_callable<'b>(&'b self,
                            mut stack: StackFrame<'b>,
                            function: &Callable,
                            excess: bool)
                            -> Result<StackFrame<'b>> {
        match *function {
            Callable::Closure(closure) => {
                stack = stack.enter_scope(closure.function.args, State::Closure(closure));
                stack.frame.excess = excess;
                Ok(stack)
            }
            Callable::Extern(ref ext) => {
                assert!(stack.len() >= ext.args + 1);
                let function_index = stack.len() - ext.args - 1;
                debug!("------- {} {:?}", function_index, &stack[..]);
                Ok(stack.enter_scope(ext.args, State::Extern(*ext)))
            }
        }
    }

    fn execute_function<'b>(&'b self,
                            mut stack: StackFrame<'b>,
                            function: &ExternFunction)
                            -> Result<StackFrame<'b>> {
        debug!("CALL EXTERN {}", function.id);
        // Make sure that the stack is not borrowed during the external function call
        // Necessary since we do not know what will happen during the function call
        drop(stack);
        let status = (function.function)(self);
        stack = self.current_frame();
        let result = stack.pop();
        while stack.len() > 0 {
            debug!("{} {:?}", stack.len(), &stack[..]);
            stack.pop();
        }
        stack = try!(stack.exit_scope()
                          .ok_or_else(|| {
                              Error::Message(StdString::from("Poped the last frame in \
                                                              execute_function"))
                          }));
        stack.pop();// Pop function
        stack.push(result);
        match status {
            Status::Ok => Ok(stack),
            Status::Yield => Err(Error::Yield),
            Status::Error => {
                match stack.pop() {
                    String(s) => Err(Error::Message(s.to_string())),
                    _ => Err(Error::Message("Unexpected panic in VM".to_string())),
                }
            }
        }
    }

    fn call_function_with_upvars<'b>(&'b self,
                                     mut stack: StackFrame<'b>,
                                     args: VMIndex,
                                     required_args: VMIndex,
                                     callable: Callable)
                                     -> Result<StackFrame<'b>> {
        debug!("cmp {} {} {:?} {:?}", args, required_args, callable, {
            let function_index = stack.len() - 1 - args;
            &(*stack)[(function_index + 1) as usize..]
        });
        match args.cmp(&required_args) {
            Ordering::Equal => self.execute_callable(stack, &callable, false),
            Ordering::Less => {
                let app = {
                    let fields = &stack[stack.len() - args..];
                    let def = PartialApplicationDataDef(callable, fields);
                    PartialApplication(self.alloc(&stack.stack, def))
                };
                for _ in 0..(args + 1) {
                    stack.pop();
                }
                stack.push(app);
                Ok(stack)
            }
            Ordering::Greater => {
                let excess_args = args - required_args;
                let d = {
                    let fields = &stack[stack.len() - excess_args..];
                    self.alloc(&stack.stack,
                               Def {
                                   tag: 0,
                                   elems: fields,
                               })
                };
                for _ in 0..excess_args {
                    stack.pop();
                }
                // Insert the excess args before the actual closure so it does not get
                // collected
                let offset = stack.len() - required_args - 1;
                stack.insert_slice(offset, &[Data(d)]);
                debug!("xxxxxx {:?}\n{:?}", &(*stack)[..], stack.stack.get_frames());
                self.execute_callable(stack, &callable, true)
            }
        }
    }

    fn do_call<'b>(&'b self, mut stack: StackFrame<'b>, args: VMIndex) -> Result<StackFrame<'b>> {
        let function_index = stack.len() - 1 - args;
        debug!("Do call {:?} {:?}",
               stack[function_index],
               &(*stack)[(function_index + 1) as usize..]);
        match stack[function_index].clone() {
            Function(ref f) => {
                let callable = Callable::Extern(f.clone());
                self.call_function_with_upvars(stack, args, f.args, callable)
            }
            Closure(ref closure) => {
                let callable = Callable::Closure(closure.clone());
                self.call_function_with_upvars(stack, args, closure.function.args, callable)
            }
            PartialApplication(app) => {
                let total_args = app.arguments.len() as VMIndex + args;
                let offset = stack.len() - args;
                stack.insert_slice(offset, &app.arguments);
                self.call_function_with_upvars(stack, total_args, app.function.args(), app.function)
            }
            x => return Err(Error::Message(format!("Cannot call {:?}", x))),
        }
    }

    fn execute<'b>(&'b self, stack: StackFrame<'b>) -> Result<Option<StackFrame<'b>>> {
        let mut maybe_stack = Some(stack);
        while let Some(mut stack) = maybe_stack {
            debug!("STACK\n{:?}", stack.stack.get_frames());
            maybe_stack = match stack.frame.state {
                State::Lock | State::Unknown => return Ok(Some(stack)),
                State::Excess => stack.exit_scope(),
                State::Extern(ext) => {
                    if stack.frame.instruction_index != 0 {
                        // This function was already called
                        return Ok(Some(stack));
                    } else {
                        stack.frame.instruction_index = 1;
                        Some(try!(self.execute_function(stack, &ext)))
                    }
                }
                State::Closure(closure) => {
                    // Tail calls into extern functions at the top level will drop the last
                    // stackframe so just return immedietly
                    if stack.stack.get_frames().len() == 0 {
                        return Ok(Some(stack));
                    }
                    let instruction_index = stack.frame.instruction_index;
                    debug!("Continue with {}\nAt: {}/{}",
                           closure.function.name,
                           instruction_index,
                           closure.function.instructions.len());
                    let new_stack = try!(self.execute_(stack,
                                                       instruction_index,
                                                       &closure.function.instructions,
                                                       &closure.function));
                    new_stack
                }
            };
        }
        Ok(maybe_stack)
    }

    fn execute_<'b>(&'b self,
                    mut stack: StackFrame<'b>,
                    mut index: usize,
                    instructions: &[Instruction],
                    function: &BytecodeFunction)
                    -> Result<Option<StackFrame<'b>>> {
        {
            debug!(">>>\nEnter frame {}: {:?}\n{:?}",
                   function.name,
                   &stack[..],
                   stack.frame);
        }
        while let Some(&instr) = instructions.get(index) {
            debug_instruction(&stack, index, instr);
            match instr {
                Push(i) => {
                    let v = stack[i].clone();
                    stack.push(v);
                }
                PushInt(i) => {
                    stack.push(Int(i));
                }
                PushString(string_index) => {
                    stack.push(String(function.strings[string_index as usize].inner()));
                }
                PushGlobal(i) => {
                    let x = function.globals[i as usize];
                    stack.push(x);
                }
                PushFloat(f) => stack.push(Float(f)),
                Call(args) => {
                    stack.frame.instruction_index = index + 1;
                    return self.do_call(stack, args).map(Some);
                }
                TailCall(mut args) => {
                    let mut amount = stack.len() - args;
                    if stack.frame.excess {
                        amount += 1;
                        match stack.excess_args() {
                            Some(excess) => {
                                debug!("TailCall: Push excess args {:?}", excess.fields);
                                for value in &excess.fields {
                                    stack.push(*value);
                                }
                                args += excess.fields.len() as VMIndex;
                            }
                            None => panic!("Expected excess args"),
                        }
                    }
                    stack = match stack.exit_scope() {
                        Some(stack) => stack,
                        None => {
                            StackFrame::frame(self.stack.borrow_mut(),
                                              args + amount + 1,
                                              State::Excess)
                        }
                    };
                    debug!("{} {} {:?}", stack.len(), amount, &stack[..]);
                    let end = stack.len() - args - 1;
                    stack.remove_range(end - amount, end);
                    debug!("{:?}", &stack[..]);
                    return self.do_call(stack, args).map(Some);
                }
                Construct(tag, args) => {
                    let d = {
                        let fields = &stack[stack.len() - args..];
                        self.alloc(&stack.stack,
                                   Def {
                                       tag: tag,
                                       elems: fields,
                                   })
                    };
                    for _ in 0..args {
                        stack.pop();
                    }
                    stack.push(Data(d));
                }
                GetField(i) => {
                    match stack.pop() {
                        Data(data) => {
                            let v = data.fields[i as usize];
                            stack.push(v);
                        }
                        x => return Err(Error::Message(format!("GetField on {:?}", x))),
                    }
                }
                TestTag(tag) => {
                    let data_tag = match stack.top() {
                        Data(ref data) => data.tag,
                        Int(tag) => tag as VMTag,
                        _ => {
                            return Err(Error::Message("Op TestTag called on non data type"
                                                          .to_string()))
                        }
                    };
                    stack.push(Int(if data_tag == tag {
                        1
                    } else {
                        0
                    }));
                }
                Split => {
                    match stack.pop() {
                        Data(data) => {
                            for field in &data.fields {
                                stack.push(*field);
                            }
                        }
                        // Zero argument variant
                        Int(_) => (),
                        _ => {
                            return Err(Error::Message("Op Split called on non data type"
                                                          .to_string()))
                        }
                    }
                }
                Jump(i) => {
                    index = i as usize;
                    continue;
                }
                CJump(i) => {
                    match stack.pop() {
                        Int(0) => (),
                        _ => {
                            index = i as usize;
                            continue;
                        }
                    }
                }
                Pop(n) => {
                    for _ in 0..n {
                        stack.pop();
                    }
                }
                Slide(n) => {
                    debug!("{:?}", &stack[..]);
                    let v = stack.pop();
                    for _ in 0..n {
                        stack.pop();
                    }
                    stack.push(v);
                }
                GetIndex => {
                    let index = stack.pop();
                    let array = stack.pop();
                    match (array, index) {
                        (Data(array), Int(index)) => {
                            let v = array.fields[index as usize];
                            stack.push(v);
                        }
                        (x, y) => {
                            return Err(Error::Message(format!("Op GetIndex called on invalid \
                                                               types {:?} {:?}",
                                                              x,
                                                              y)))
                        }
                    }
                }
                MakeClosure(fi, n) => {
                    let closure = {
                        let args = &stack[stack.len() - n..];
                        let func = function.inner_functions[fi as usize];
                        Closure(self.alloc(&stack.stack, ClosureDataDef(func, args)))
                    };
                    for _ in 0..n {
                        stack.pop();
                    }
                    stack.push(closure);
                }
                NewClosure(fi, n) => {
                    let closure = {
                        // Use dummy variables until it is filled
                        let args = [Int(0); 128];
                        let func = function.inner_functions[fi as usize];
                        Closure(self.alloc(&stack.stack, ClosureDataDef(func, &args[..n as usize])))
                    };
                    stack.push(closure);
                }
                CloseClosure(n) => {
                    let i = stack.len() - n - 1;
                    match stack[i] {
                        Closure(mut closure) => {
                            // Unique access should be safe as this closure should not be shared as
                            // it has just been allocated and havent even had its upvars set yet
                            // (which is done here).
                            unsafe {
                                for var in closure.as_mut().upvars.iter_mut().rev() {
                                    *var = stack.pop();
                                }
                            }
                            stack.pop();//Remove the closure
                        }
                        x => panic!("Expected closure, got {:?}", x),
                    }
                }
                PushUpVar(i) => {
                    let v = stack.get_upvar(i).clone();
                    stack.push(v);
                }
                AddInt => binop(self, &mut stack, VMInt::add),
                SubtractInt => binop(self, &mut stack, VMInt::sub),
                MultiplyInt => binop(self, &mut stack, VMInt::mul),
                DivideInt => binop(self, &mut stack, VMInt::div),
                IntLT => binop(self, &mut stack, |l: VMInt, r| l < r),
                IntEQ => binop(self, &mut stack, |l: VMInt, r| l == r),
                AddFloat => binop(self, &mut stack, f64::add),
                SubtractFloat => binop(self, &mut stack, f64::sub),
                MultiplyFloat => binop(self, &mut stack, f64::mul),
                DivideFloat => binop(self, &mut stack, f64::div),
                FloatLT => binop(self, &mut stack, |l: f64, r| l < r),
                FloatEQ => binop(self, &mut stack, |l: f64, r| l == r),
            }
            index += 1;
        }
        let result = stack.top();
        debug!("Return {:?}", result);
        let len = stack.len();
        let frame_has_excess = stack.frame.excess;
        // We might not get access to the frame above the current as it could be locked
        let stack_exists = stack.exit_scope().is_some();
        let mut stack = self.stack.borrow_mut();
        stack.pop();
        for _ in 0..len {
            stack.pop();
        }
        stack.push(result);
        if frame_has_excess {
            stack.pop();
            // If the function that just finished had extra arguments we need to call the result of
            // the call with the extra arguments
            match stack.pop() {
                Data(excess) => {
                    let mut stack = StackFrame::frame(stack,
                                                      excess.fields.len() as VMIndex,
                                                      State::Excess);
                    debug!("Push excess args {:?}", &excess.fields);
                    stack.push(result);
                    for value in &excess.fields {
                        stack.push(*value);
                    }
                    self.do_call(stack, excess.fields.len() as VMIndex).map(Some)
                }
                x => panic!("Expected excess arguments found {:?}", x),
            }
        } else {
            drop(stack);
            Ok(if stack_exists {
                Some(self.current_frame())
            } else {
                None
            })
        }
    }
}

#[inline]
fn binop<'b, F, T, R>(vm: &'b VM, stack: &mut StackFrame<'b>, f: F)
    where F: FnOnce(T, T) -> R,
          T: Getable<'b> + fmt::Debug,
          R: Pushable<'b>
{
    let r = stack.pop();
    let l = stack.pop();
    match (T::from_value(vm, l), T::from_value(vm, r)) {
        (Some(l), Some(r)) => {
            let result = f(l, r);
            result.push(vm, stack);
        }
        (l, r) => panic!("{:?} `op` {:?}", l, r),
    }
}

fn debug_instruction(stack: &StackFrame, index: usize, instr: Instruction) {
    debug!("{:?}: {:?} {:?}",
           index,
           instr,
           match instr {
               Push(i) => stack.get(i as usize).cloned(),
               NewClosure(..) => Some(Int(stack.len() as isize)),
               MakeClosure(..) => Some(Int(stack.len() as isize)),
               _ => None,
           });
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
