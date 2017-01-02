//! The thread/vm type
use std::any::Any;
use std::sync::{Mutex, RwLock, RwLockWriteGuard, RwLockReadGuard, MutexGuard};
use std::cmp::Ordering;
use std::fmt;
use std::mem;
use std::ops::{Add, Sub, Mul, Div, Deref, DerefMut};
use std::string::String as StdString;
use std::result::Result as StdResult;
use std::sync::Arc;
use std::usize;

use futures::{Async, Future, Poll};

use base::metadata::Metadata;
use base::pos::Line;
use base::symbol::Symbol;
use base::types::ArcType;
use base::types;

use {Variants, Error, Result};
use field_map::FieldMap;
use interner::InternedStr;
use macros::MacroEnv;
use api::{Getable, Pushable, VmType};
use compiler::{CompiledFunction, UpvarInfo};
use gc::{DataDef, Gc, GcPtr, Generation, Move};
use source_map::LocalIter;
use stack::{Frame, Stack, StackFrame, State};
use types::*;
use vm::{GlobalVmState, VmEnv};
use value::{Value, ClosureData, ClosureInitDef, ClosureDataDef, Def, ExternFunction, GcStr,
            BytecodeFunction, Callable, PartialApplicationDataDef, Userdata};

use value::Value::{Int, Float, String, Data, Function, PartialApplication, Closure};

pub use gc::Traverseable;

pub struct Execute<T> {
    thread: T,
}

impl<T> Execute<T>
    where T: Deref<Target = Thread>,
{
    pub fn new(thread: T) -> Execute<T> {
        Execute { thread: thread }
    }
}

impl<T> Future for Execute<T>
    where T: Deref<Target = Thread>,
{
    type Item = Value;
    type Error = Error;
    fn poll(&mut self) -> Poll<Value, Error> {
        self.thread.resume().map(|async| async.map(|mut context| context.stack.pop()))
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

/// A rooted value
#[derive(Clone, PartialEq)]
pub struct RootedValue<T>
    where T: Deref<Target = Thread>,
{
    vm: T,
    value: Value,
}

impl<T> Drop for RootedValue<T>
    where T: Deref<Target = Thread>,
{
    fn drop(&mut self) {
        // TODO not safe if the root changes order of being dropped with another root
        self.vm.rooted_values.write().unwrap().pop();
    }
}

impl<T> fmt::Debug for RootedValue<T>
    where T: Deref<Target = Thread>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.value)
    }
}

impl<T> Deref for RootedValue<T>
    where T: Deref<Target = Thread>,
{
    type Target = Value;
    fn deref(&self) -> &Value {
        &self.value
    }
}

impl<T> RootedValue<T>
    where T: Deref<Target = Thread>,
{
    pub fn vm(&self) -> &Thread {
        &self.vm
    }

    pub fn clone_vm(&self) -> T
        where T: Clone,
    {
        self.vm.clone()
    }
}

impl<'vm> RootedValue<&'vm Thread> {
    pub fn vm_(&self) -> &'vm Thread {
        self.vm
    }
}

/// A rooted userdata value
pub struct Root<'vm, T: ?Sized + 'vm> {
    roots: &'vm RwLock<Vec<GcPtr<Traverseable + Send + Sync>>>,
    ptr: *const T,
}

impl<'vm, T: ?Sized> Drop for Root<'vm, T> {
    fn drop(&mut self) {
        // TODO not safe if the root changes order of being dropped with another root
        self.roots.write().unwrap().pop();
    }
}

impl<'vm, T: ?Sized> Deref for Root<'vm, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.ptr }
    }
}

/// A rooted string
pub struct RootStr<'vm>(Root<'vm, str>);

impl<'vm> Deref for RootStr<'vm> {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}


struct Roots<'b> {
    vm: GcPtr<Thread>,
    stack: &'b Stack,
}
impl<'b> Traverseable for Roots<'b> {
    fn traverse(&self, gc: &mut Gc) {
        // Since this vm's stack is already borrowed in self we need to manually mark it to prevent
        // it from being traversed normally
        gc.mark(self.vm);
        self.stack.get_values().traverse(gc);

        // Traverse the vm's fields, avoiding the stack which is traversed above
        self.vm.traverse_fields_except_stack(gc);
    }
}

// All threads MUST be allocated in the garbage collected heap. This is necessary as a thread
// calling collect need to mark itself if it is on the garbage collected heap and it has no way of
// knowing wheter it is or not. So the only way of allowing it to mark itself is to disallow it to
// be allocated anywhere else.
/// Representation of the virtual machine
pub struct Thread {
    global_state: Arc<GlobalVmState>,
    // The parent of this thread, if it exists must live at least as long as this thread as this
    // thread can refer to any value in the parent thread
    parent: Option<RootedThread>,
    roots: RwLock<Vec<GcPtr<Traverseable + Send + Sync>>>,
    rooted_values: RwLock<Vec<Value>>,
    /// All threads which this thread have spawned in turn. Necessary as this thread needs to scan
    /// the roots of all its children as well since those may contain references to this threads
    /// garbage collected values
    child_threads: RwLock<Vec<GcPtr<Thread>>>,
    context: Mutex<Context>,
}

impl fmt::Debug for Thread {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Thread({:p})", self)
    }
}

impl Userdata for Thread {}

impl VmType for Thread {
    type Type = Self;
}

impl Traverseable for Thread {
    fn traverse(&self, gc: &mut Gc) {
        self.traverse_fields_except_stack(gc);
        self.context.lock().unwrap().stack.get_values().traverse(gc);
        self.child_threads.read().unwrap().traverse(gc);
    }
}

impl PartialEq for Thread {
    fn eq(&self, other: &Thread) -> bool {
        self as *const _ == other as *const _
    }
}

impl VmType for RootedThread {
    type Type = Thread;
}

impl<'vm> Pushable<'vm> for RootedThread {
    fn push(self, _vm: &'vm Thread, context: &mut Context) -> Result<()> {
        context.stack.push(Value::Thread(self.0));
        Ok(())
    }
}

/// An instance of `Thread` which is rooted. See the `Thread` type for documentation on interacting
/// with the type.
#[derive(Debug)]
pub struct RootedThread(GcPtr<Thread>);

impl Drop for RootedThread {
    fn drop(&mut self) {
        let is_empty = {
            let mut roots = self.parent_threads();
            let index = roots.iter()
                .position(|p| &**p as *const Thread == &*self.0 as *const Thread)
                .expect("VM ptr");
            roots.swap_remove(index);
            roots.is_empty()
        };
        if self.parent.is_none() && is_empty {
            // The last RootedThread was dropped, there is no way to refer to the global state any
            // longer so drop everything
            let mut gc_ref = self.0.global_state.gc.lock().unwrap();
            let gc_to_drop = ::std::mem::replace(&mut *gc_ref, Gc::new(Generation::default(), 0));
            // Make sure that the RefMut is dropped before the Gc itself as the RwLock is dropped
            // when the Gc is dropped
            drop(gc_ref);
            drop(gc_to_drop);
        }
    }
}

impl Deref for RootedThread {
    type Target = Thread;
    fn deref(&self) -> &Thread {
        &self.0
    }
}

impl Clone for RootedThread {
    fn clone(&self) -> RootedThread {
        self.root_thread()
    }
}

impl Traverseable for RootedThread {
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc);
    }
}

impl RootedThread {
    /// Creates a new virtual machine with an empty global environment
    pub fn new() -> RootedThread {
        let thread = Thread {
            global_state: Arc::new(GlobalVmState::new()),
            parent: None,
            context: Mutex::new(Context::new(Gc::new(Generation::default(), usize::MAX))),
            roots: RwLock::new(Vec::new()),
            rooted_values: RwLock::new(Vec::new()),
            child_threads: RwLock::new(Vec::new()),
        };
        let mut gc = Gc::new(Generation::default(), usize::MAX);
        let vm =
            gc.alloc(Move(thread)).expect("Not enough memory to allocate thread").root_thread();
        *vm.global_state.gc.lock().unwrap() = gc;
        // Enter the top level scope
        {
            let mut context = vm.context.lock().unwrap();
            StackFrame::frame(&mut context.stack, 0, State::Unknown);
        }
        vm
    }

    /// Converts a `RootedThread` into a raw pointer allowing to be passed through a C api.
    /// The reference count for the thread is not modified
    pub fn into_raw(self) -> *const Thread {
        let ptr: *const Thread = &*self.0;
        ::std::mem::forget(self);
        ptr
    }

    /// Converts a raw pointer into a `RootedThread`.
    /// The reference count for the thread is not modified so it is up to the caller to ensure that
    /// the count is correct.
    pub unsafe fn from_raw(ptr: *const Thread) -> RootedThread {
        RootedThread(GcPtr::from_raw(ptr))
    }
}

impl Thread {
    /// Spawns a new gluon thread with its own stack and heap but while still sharing the same
    /// global environment
    pub fn new_thread(&self) -> Result<RootedThread> {
        let vm = Thread {
            global_state: self.global_state.clone(),
            parent: Some(self.root_thread()),
            context: Mutex::new(Context::new(self.current_context().gc.new_child_gc())),
            roots: RwLock::new(Vec::new()),
            rooted_values: RwLock::new(Vec::new()),
            child_threads: RwLock::new(Vec::new()),
        };
        // Enter the top level scope
        {
            let mut context = vm.current_context();
            StackFrame::frame(&mut context.stack, 0, State::Unknown);
        }
        let ptr = self.context().alloc(Move(vm))?;

        Ok(ptr.root_thread())
    }

    /// Roots `self`, extending the lifetime of this thread until at least the returned
    /// `RootedThread` is droppped
    pub fn root_thread(&self) -> RootedThread {
        unsafe {
            let vm = RootedThread(GcPtr::from_raw(self));
            vm.parent_threads().push(vm.0);
            vm
        }
    }

    /// Creates a new global value at `name`.
    /// Fails if a global called `name` already exists.
    pub fn define_global<'vm, T>(&'vm self, name: &str, value: T) -> Result<()>
        where T: Pushable<'vm> + VmType,
    {
        let value = {
            let mut context = self.context();
            value.push(self, &mut context)?;
            context.stack.pop()
        };
        self.set_global(Symbol::from(name),
                        T::make_type(self),
                        Metadata::default(),
                        value)
    }

    /// Retrieves the global called `name`.
    /// Fails if the global does not exist or it does not have the correct type.
    pub fn get_global<'vm, T>(&'vm self, name: &str) -> Result<T>
        where T: Getable<'vm> + VmType,
    {
        use check::check_signature;
        let env = self.get_env();
        let (value, actual) = env.get_binding(name)?;
        // Finally check that type of the returned value is correct
        let expected = T::make_type(self);
        if check_signature(&*env, &expected, &actual) {
            T::from_value(self, Variants(&value))
                .ok_or_else(|| Error::UndefinedBinding(name.into()))
        } else {
            Err(Error::WrongType(expected, actual.into_owned()))
        }
    }

    /// Retrieves type information about the type `name`. Types inside records can be accessed
    /// using dot notation (std.prelude.Option)
    pub fn find_type_info(&self, name: &str) -> Result<types::Alias<Symbol, ArcType>> {
        let env = self.get_env();
        env.find_type_info(name)
            .map(|alias| alias.into_owned())
    }

    /// Returns the gluon type that was bound to `T`
    pub fn get_type<T: ?Sized + Any>(&self) -> ArcType {
        self.global_env().get_type::<T>()
    }

    /// Registers the type `T` as being a gluon type called `name` with generic arguments `args`
    pub fn register_type<T: ?Sized + Any>(&self, name: &str, args: &[&str]) -> Result<ArcType> {
        self.global_env().register_type::<T>(name, args)
    }

    /// Locks and retrieves the global environment of the vm
    pub fn get_env<'b>(&'b self) -> RwLockReadGuard<'b, VmEnv> {
        self.global_env().get_env()
    }

    /// Retrieves the macros defined for this vm
    pub fn get_macros(&self) -> &MacroEnv {
        self.global_env().get_macros()
    }

    /// Runs a garbage collection.
    pub fn collect(&self) {
        let mut context = self.current_context();
        self.with_roots(&mut context, |gc, roots| unsafe {
            gc.collect(roots);
        })
    }

    /// Pushes a value to the top of the stack
    pub fn push<'vm, T>(&'vm self, v: T) -> Result<()>
        where T: Pushable<'vm>,
    {
        let mut context = self.current_context();
        v.push(self, &mut context)
    }

    /// Removes the top value from the stack
    pub fn pop(&self) {
        self.current_context()
            .stack
            .pop();
    }

    pub fn set_memory_limit(&self, memory_limit: usize) {
        self.current_context().gc.set_memory_limit(memory_limit)
    }

    fn current_context(&self) -> OwnedContext {
        OwnedContext {
            thread: self,
            context: self.context.lock().unwrap(),
        }
    }

    fn traverse_fields_except_stack(&self, gc: &mut Gc) {
        self.global_state.traverse(gc);
        self.roots.read().unwrap().traverse(gc);
        self.rooted_values.read().unwrap().traverse(gc);
    }

    fn parent_threads(&self) -> RwLockWriteGuard<Vec<GcPtr<Thread>>> {
        match self.parent {
            Some(ref parent) => parent.child_threads.write().unwrap(),
            None => self.global_state.generation_0_threads.write().unwrap(),
        }
    }

    fn with_roots<F, R>(&self, context: &mut Context, f: F) -> R
        where F: for<'b> FnOnce(&mut Gc, Roots<'b>) -> R,
    {
        // For this to be safe we require that the received stack is the same one that is in this
        // VM
        assert!(unsafe {
            context as *const _ as usize >= &self.context as *const _ as usize &&
            context as *const _ as usize <= (&self.context as *const _).offset(1) as usize
        });
        let roots = Roots {
            vm: unsafe {
                // Threads must only be on the garbage collectors heap which makes this safe
                GcPtr::from_raw(self)
            },
            stack: &context.stack,
        };
        f(&mut context.gc, roots)
    }
}

/// Internal functions for interacting with threads. These functions should be considered both
/// unsafe and unstable.
pub trait ThreadInternal {
    /// Locks and retrives this threads stack
    fn context(&self) -> OwnedContext;

    /// Roots a userdata
    fn root<'vm, T: Userdata>(&'vm self, v: GcPtr<Box<Userdata>>) -> Option<Root<'vm, T>>;

    /// Roots a string
    fn root_string<'vm>(&'vm self, ptr: GcStr) -> RootStr<'vm>;

    /// Roots a value
    fn root_value(&self, value: Value) -> RootedValue<RootedThread>;

    /// Roots a value
    fn root_value_ref(&self, value: Value) -> RootedValue<&Thread>;

    fn add_bytecode(&self,
                    name: &str,
                    typ: ArcType,
                    args: VmIndex,
                    instructions: Vec<Instruction>)
                    -> Result<()>;

    /// Evaluates a zero argument function (a thunk)
    fn call_thunk(&self, closure: GcPtr<ClosureData>) -> Execute<&Self>;

    /// Executes an `IO` action
    fn execute_io(&self, value: Value) -> Result<Async<Value>>;

    /// Calls a function on the stack.
    /// When this function is called it is expected that the function exists at
    /// `stack.len() - args - 1` and that the arguments are of the correct type
    fn call_function<'b>(&'b self,
                         stack: OwnedContext<'b>,
                         args: VmIndex)
                         -> Result<Async<Option<OwnedContext<'b>>>>;

    fn resume(&self) -> Result<Async<OwnedContext>>;

    fn global_env(&self) -> &Arc<GlobalVmState>;

    fn set_global(&self,
                  name: Symbol,
                  typ: ArcType,
                  metadata: Metadata,
                  value: Value)
                  -> Result<()>;

    /// `owner` is theread that owns `value` which is not necessarily the same as `self`
    fn deep_clone_value(&self, owner: &Thread, value: Value) -> Result<Value>;

    fn can_share_values_with(&self, gc: &mut Gc, other: &Thread) -> bool;
}

impl ThreadInternal for Thread {
    fn context(&self) -> OwnedContext {
        OwnedContext {
            thread: self,
            context: self.context.lock().unwrap(),
        }
    }
    /// Roots a userdata
    fn root<'vm, T: Userdata>(&'vm self, v: GcPtr<Box<Userdata>>) -> Option<Root<'vm, T>> {
        v.downcast_ref::<T>()
            .map(|ptr| {
                self.roots.write().unwrap().push(v.as_traverseable());
                Root {
                    roots: &self.roots,
                    ptr: ptr,
                }
            })
    }

    /// Roots a string
    fn root_string<'vm>(&'vm self, ptr: GcStr) -> RootStr<'vm> {
        self.roots.write().unwrap().push(ptr.into_inner().as_traverseable());
        RootStr(Root {
            roots: &self.roots,
            ptr: &*ptr,
        })
    }

    /// Roots a value
    fn root_value(&self, value: Value) -> RootedValue<RootedThread> {
        self.rooted_values.write().unwrap().push(value);
        RootedValue {
            vm: self.root_thread(),
            value: value,
        }
    }

    /// Roots a value
    fn root_value_ref(&self, value: Value) -> RootedValue<&Thread> {
        self.rooted_values.write().unwrap().push(value);
        RootedValue {
            vm: self,
            value: value,
        }
    }

    fn add_bytecode(&self,
                    name: &str,
                    typ: ArcType,
                    args: VmIndex,
                    instructions: Vec<Instruction>)
                    -> Result<()> {
        let id = Symbol::from(name);
        let mut compiled_fn = CompiledFunction::new(args, id.clone(), typ.clone(), "".into());
        compiled_fn.instructions = instructions;
        let closure = self.global_env().new_global_thunk(compiled_fn)?;
        self.set_global(id, typ, Metadata::default(), Closure(closure)).unwrap();
        Ok(())
    }

    fn call_thunk(&self, closure: GcPtr<ClosureData>) -> Execute<&Thread> {
        let mut context = self.current_context();
        context.stack.push(Closure(closure));
        context.borrow_mut().enter_scope(0, State::Closure(closure));
        Execute { thread: self }
    }

    /// Calls a module, allowed to to run IO expressions
    fn execute_io(&self, value: Value) -> Result<Async<Value>> {
        debug!("Run IO {:?}", value);
        let mut context = OwnedContext {
            thread: self,
            context: self.context.lock().unwrap(),
        };
        // Dummy value to fill the place of the function for TailCall
        context.stack.push(Int(0));

        context.stack.push(value);
        context.stack.push(Int(0));

        context.borrow_mut().enter_scope(2, State::Unknown);
        context = try_ready!(self.call_function(context, 1))
            .expect("call_module to have the stack remaining");
        let result = context.stack.pop();
        {
            let mut context = context.borrow_mut();
            while context.stack.len() > 0 {
                context.stack.pop();
            }
        }
        let _ = context.exit_scope();
        Ok(Async::Ready(result))
    }

    /// Calls a function on the stack.
    /// When this function is called it is expected that the function exists at
    /// `stack.len() - args - 1` and that the arguments are of the correct type
    fn call_function<'b>(&'b self,
                         mut context: OwnedContext<'b>,
                         args: VmIndex)
                         -> Result<Async<Option<OwnedContext<'b>>>> {
        context.borrow_mut().do_call(args)?;
        context.execute()
    }

    fn resume(&self) -> Result<Async<OwnedContext>> {
        let mut context = self.current_context();
        if context.stack.get_frames().len() == 1 {
            // Only the top level frame left means that the thread has finished
            return Err(Error::Dead);
        }
        context = try_ready!(context.execute()).unwrap();
        Ok(Async::Ready(context))
    }

    fn global_env(&self) -> &Arc<GlobalVmState> {
        &self.global_state
    }

    fn set_global(&self,
                  name: Symbol,
                  typ: ArcType,
                  metadata: Metadata,
                  value: Value)
                  -> Result<()> {
        let value = ::value::Cloner::new(self, &mut self.global_env().gc.lock().unwrap()).deep_clone(value)?;
        self.global_env().set_global(name, typ, metadata, value)
    }

    fn deep_clone_value(&self, owner: &Thread, value: Value) -> Result<Value> {
        let mut context = self.current_context();
        let full_clone = !self.can_share_values_with(&mut context.gc, owner);
        let mut cloner = ::value::Cloner::new(self, &mut context.gc);
        if full_clone {
            cloner.force_full_clone();
        }
        cloner.deep_clone(value)
    }

    fn can_share_values_with(&self, gc: &mut Gc, other: &Thread) -> bool {
        if self as *const Thread == other as *const Thread {
            return true;
        }
        // If the threads do not share the same global state then they are disjoint and can't share
        // values
        if &*self.global_state as *const GlobalVmState !=
           &*other.global_state as *const GlobalVmState {
            return false;
        }
        // Otherwise the threads might be able to share values but only if they are on the same
        // of the generation tree (see src/gc.rs)
        // Search from the thread which MAY be a child to the parent. If `parent` could not be
        // found then the threads must be in different branches of the tree
        let self_gen = gc.generation();
        let other_gen = other.context.lock().unwrap().gc.generation();
        let (parent, mut child) = if self_gen.is_parent_of(other_gen) {
            (self, other)
        } else {
            (other, self)
        };
        while let Some(ref next) = child.parent {
            if &**next as *const Thread == parent as *const Thread {
                return true;
            }
            child = next;
        }
        false
    }
}

pub type HookFn = Box<FnMut(&Thread, DebugInfo) -> Result<()> + Send + Sync>;

pub struct DebugInfo<'a> {
    stack: &'a Stack,
    state: HookFlags,
}

pub struct StackInfo<'a> {
    info: &'a DebugInfo<'a>,
    index: usize,
}

impl<'a> DebugInfo<'a> {
    /// Returns the reason for the hook being called
    pub fn state(&self) -> HookFlags {
        self.state
    }

    /// Returns a struct which can be queried about information about the stack
    /// at a specific level where `0` is the currently executing frame.
    pub fn stack_info(&self, level: usize) -> Option<StackInfo> {
        let frames = self.stack.get_frames();
        if level < frames.len() {
            Some(StackInfo {
                info: self,
                index: frames.len() - level - 1,
            })
        } else {
            None
        }
    }

    pub fn stack_info_len(&self) -> usize {
        self.stack.get_frames().len()
    }
}

impl<'a> StackInfo<'a> {
    fn frame(&self) -> &Frame {
        &self.info.stack.get_frames()[self.index]
    }

    // For frames except the top we subtract one to account for the `Call` instruction adding one
    fn instruction_index(&self) -> usize {
        if self.info.stack.get_frames().len() - 1 == self.index {
            self.frame().instruction_index
        } else {
            self.frame().instruction_index - 1
        }
    }

    /// Returns the line which create the current instruction of this frame
    pub fn line(&self) -> Option<Line> {
        let frame = self.frame();
        match frame.state {
            State::Closure(ref closure) => {
                closure.function.debug_info.source_map.line(self.instruction_index())
            }
            _ => None,
        }
    }

    /// Returns the name of the source which defined the funtion executing at this frame
    pub fn source_name(&self) -> &str {
        match self.frame().state {
            State::Closure(ref closure) => &closure.function.debug_info.source_name,
            _ => "<unknown>",
        }
    }

    /// Returns the name of the function executing at this frame
    pub fn function_name(&self) -> Option<&str> {
        match self.frame().state {
            State::Unknown | State::Lock | State::Excess => None,
            State::Closure(ref closure) => Some(closure.function.name.declared_name()),
            State::Extern(ref function) => Some(function.id.declared_name()),
        }
    }

    /// Returns an iterator over all locals available at the current executing instruction
    pub fn locals(&self) -> LocalIter {
        let frame = self.frame();
        match frame.state {
            State::Closure(ref closure) => {
                closure.function.debug_info.local_map.locals(self.instruction_index())
            }
            _ => LocalIter::empty(),
        }
    }

    /// Returns a slice with information about the values bound to this closure
    pub fn upvars(&self) -> &[UpvarInfo] {
        match self.frame().state {
            State::Closure(ref closure) => &closure.function.debug_info.upvars,
            _ => panic!("Attempted to access upvar in non closure function"),
        }
    }
}

bitflags! {
    pub flags HookFlags: u8 {
        /// Call the hook when execution moves to a new line
        const LINE_FLAG = 0b01,
        /// Call the hook when a function is called
        const CALL_FLAG = 0b10,
    }
}

struct Hook {
    function: Option<HookFn>,
    flags: HookFlags,
    // The index of the last executed instruction
    previous_instruction_index: usize,
}

pub struct Context {
    // FIXME It is dangerous to write to gc and stack
    pub stack: Stack,
    pub gc: Gc,
    record_map: FieldMap,
    hook: Hook,
    max_stack_size: VmIndex,

    poll_fn: Option<Box<FnMut(&Thread, &mut Context) -> Result<Async<()>> + Send>>,
}

impl Context {
    fn new(gc: Gc) -> Context {
        Context {
            gc: gc,
            stack: Stack::new(),
            record_map: FieldMap::new(),
            hook: Hook {
                function: None,
                flags: HookFlags::empty(),
                previous_instruction_index: usize::max_value(),
            },
            max_stack_size: VmIndex::max_value(),
            poll_fn: None,
        }
    }

    pub fn new_data(&mut self, thread: &Thread, tag: VmTag, fields: &[Value]) -> Result<Value> {
        self.alloc_with(thread,
                        Def {
                            tag: tag,
                            elems: fields,
                        })
            .map(Value::Data)
    }

    pub fn alloc_with<D>(&mut self, thread: &Thread, data: D) -> Result<GcPtr<D::Value>>
        where D: DataDef + Traverseable,
              D::Value: Sized + Any,
    {
        alloc(&mut self.gc, thread, &self.stack, data)
    }

    pub fn alloc_ignore_limit<D>(&mut self, data: D) -> GcPtr<D::Value>
        where D: DataDef + Traverseable,
              D::Value: Sized + Any,
    {
        self.gc.alloc_ignore_limit(data)
    }

    pub fn set_hook(&mut self, hook: Option<HookFn>) -> Option<HookFn> {
        mem::replace(&mut self.hook.function, hook)
    }

    pub fn set_hook_mask(&mut self, flags: HookFlags) {
        self.hook.flags = flags;
    }

    pub fn set_max_stack_size(&mut self, limit: VmIndex) {
        self.max_stack_size = limit;
    }

    pub unsafe fn return_future<'vm, F>(&mut self, mut future: F)
        where F: Future<Error = Error> + Send + 'static,
              F::Item: Pushable<'vm>,
    {
        use std::mem::transmute;
        self.poll_fn = Some(Box::new(move |vm, context| {
            let vm = transmute::<&Thread, &'vm Thread>(vm);
            let value = try_ready!(future.poll());
            value.push(vm, context).map(Async::Ready)
        }));
    }
}

impl<'b> OwnedContext<'b> {
    pub fn alloc<D>(&mut self, data: D) -> Result<GcPtr<D::Value>>
        where D: DataDef + Traverseable,
              D::Value: Sized + Any,
    {
        let Context { ref mut gc, ref stack, .. } = **self;
        alloc(gc, self.thread, &stack, data)
    }

    pub fn debug_info(&self) -> DebugInfo {
        DebugInfo {
            stack: &self.stack,
            state: HookFlags::empty(),
        }
    }
}

pub fn alloc<D>(gc: &mut Gc, thread: &Thread, stack: &Stack, def: D) -> Result<GcPtr<D::Value>>
    where D: DataDef + Traverseable,
          D::Value: Sized + Any,
{
    let roots = Roots {
        vm: unsafe {
            // Threads must only be on the garbage collectors heap which makes this safe
            GcPtr::from_raw(thread)
        },
        stack: stack,
    };
    unsafe { gc.alloc_and_collect(roots, def) }
}

pub struct OwnedContext<'b> {
    thread: &'b Thread,
    context: MutexGuard<'b, Context>,
}

impl<'b> Deref for OwnedContext<'b> {
    type Target = Context;
    fn deref(&self) -> &Context {
        &self.context
    }
}

impl<'b> DerefMut for OwnedContext<'b> {
    fn deref_mut(&mut self) -> &mut Context {
        &mut self.context
    }
}

impl<'b> OwnedContext<'b> {
    fn exit_scope(mut self) -> StdResult<OwnedContext<'b>, ()> {
        let exists = StackFrame::current(&mut self.stack).exit_scope().is_ok();
        if exists { Ok(self) } else { Err(()) }
    }

    fn execute(self) -> Result<Async<Option<OwnedContext<'b>>>> {
        let mut maybe_context = Some(self);
        while let Some(mut context) = maybe_context {
            debug!("STACK\n{:?}", context.stack.get_frames());
            let state = context.borrow_mut().stack.frame.state;

            let instruction_index = context.borrow_mut().stack.frame.instruction_index;
            if instruction_index == 0 && context.hook.flags.contains(CALL_FLAG) {
                match state {
                    State::Extern(_) |
                    State::Closure(_) => {
                        let thread = context.thread;
                        let context = &mut *context;
                        if let Some(ref mut hook) = context.hook.function {
                            let info = DebugInfo {
                                stack: &context.stack,
                                state: CALL_FLAG,
                            };
                            hook(thread, info)?
                        }
                    }
                    _ => (),
                }
            }

            maybe_context = match state {
                State::Lock | State::Unknown => return Ok(Async::Ready(Some(context))),
                State::Excess => context.exit_scope().ok(),
                State::Extern(ext) => {
                    let instruction_index = context.borrow_mut().stack.frame.instruction_index;
                    if instruction_index != 0 {
                        // This function was already called
                        return Ok(Async::Ready(Some(context)));
                    } else {
                        let thread = context.thread;
                        context.borrow_mut().stack.frame.instruction_index = 1;
                        let result = context.execute_function(&ext);
                        match result {
                            Ok(Async::Ready(context)) => Some(context),
                            Ok(Async::NotReady) => {
                                let mut context = thread.current_context();
                                if context.poll_fn.is_some() {
                                    context.borrow_mut().stack.frame.instruction_index = 0;
                                }
                                return Ok(Async::NotReady);
                            }
                            Err(err) => return Err(err),
                        }
                    }
                }
                State::Closure(closure) => {
                    let max_stack_size = context.max_stack_size;
                    // Tail calls into extern functions at the top level will drop the last
                    // stackframe so just return immedietly
                    enum State {
                        Exists,
                        DoesNotExist,
                        ReturnContext,
                    }
                    let state = {
                        let mut context = context.borrow_mut();

                        let instruction_index = context.stack.frame.instruction_index;
                        let function_size = closure.function.max_stack_size;

                        // Before entering a function check that the stack cannot exceed `max_stack_size`
                        if instruction_index == 0 &&
                           context.stack.stack.len() + function_size > max_stack_size {
                            return Err(Error::StackOverflow(max_stack_size));
                        }

                        if context.stack.stack.get_frames().len() == 0 {
                            State::ReturnContext
                        } else {
                            debug!("Continue with {}\nAt: {}/{}",
                                   closure.function.name,
                                   instruction_index,
                                   closure.function.instructions.len());

                            let new_context = context.execute_(instruction_index,
                                          &closure.function.instructions,
                                          &closure.function)?;
                            if new_context.is_some() {
                                State::Exists
                            } else {
                                State::DoesNotExist
                            }
                        }
                    };
                    match state {
                        State::Exists => Some(context),
                        State::DoesNotExist => None,
                        State::ReturnContext => return Ok(Async::Ready(Some(context))),
                    }
                }
            };
        }
        Ok(Async::Ready(maybe_context))
    }

    fn execute_function(mut self, function: &ExternFunction) -> Result<Async<OwnedContext<'b>>> {
        debug!("CALL EXTERN {} {:?}", function.id, self.stack);
        let status = if let Some(mut poll_fn) = self.poll_fn.take() {
            let result = poll_fn(self.thread, &mut self);
            self.poll_fn = Some(poll_fn);
            try_ready!(result);
            self.poll_fn = None;
            Status::Ok
        } else {
            // Make sure that the stack is not borrowed during the external function call
            // Necessary since we do not know what will happen during the function call
            let thread = self.thread;
            drop(self);
            let status = (function.function)(thread);
            self = thread.current_context();
            if self.poll_fn.is_some() && status == Status::Yield {
                return Ok(Async::NotReady);
            }
            status
        };
        let result = self.stack.pop();
        {
            let mut stack = self.stack.current_frame();
            while stack.len() > 0 {
                debug!("{} {:?}", stack.len(), &*stack);
                stack.pop();
            }
        }
        self =
            self.exit_scope()
                .map_err(|_| {
                    Error::Message(StdString::from("Poped the last frame in execute_function"))
                })?;
        self.stack.pop();// Pop function
        self.stack.push(result);

        match status {
            Status::Ok => Ok(Async::Ready(self)),
            Status::Yield => Ok(Async::NotReady),
            Status::Error => {
                match self.stack.pop() {
                    String(s) => Err(Error::Panic(s.to_string())),
                    _ => {
                        Err(Error::Message(format!("Unexpected error calling function `{}`",
                                                   function.id)))
                    }
                }
            }
        }
    }

    fn borrow_mut(&mut self) -> ExecuteContext {
        let context = &mut **self;
        ExecuteContext {
            thread: self.thread,
            gc: &mut context.gc,
            stack: StackFrame::current(&mut context.stack),
            record_map: &mut context.record_map,
            hook: &mut context.hook,
        }
    }
}

struct ExecuteContext<'b> {
    thread: &'b Thread,
    stack: StackFrame<'b>,
    gc: &'b mut Gc,
    record_map: &'b mut FieldMap,
    hook: &'b mut Hook,
}

impl<'b> ExecuteContext<'b> {
    fn lookup_field(&self, tag: VmTag, index: InternedStr) -> Result<VmIndex> {
        self.record_map
            .get_offset(tag, index)
            .ok_or_else(|| {
                Error::Message(format!("Internal error: Undefined record field {} {}", tag, index))
            })
    }

    fn enter_scope(&mut self, args: VmIndex, state: State) {
        self.stack.enter_scope(args, state);
        self.hook.previous_instruction_index = usize::max_value();
    }

    fn exit_scope(&mut self) -> StdResult<(), ()> {
        match self.stack.exit_scope() {
            Ok(_) => {
                if self.hook.flags.bits() != 0 {
                    // Subtract 1 to compensate for the `Call` instruction adding one earlier
                    // ensuring that the line hook runs after function calls
                    self.hook.previous_instruction_index =
                        self.stack.frame.instruction_index.saturating_sub(1);
                }
                Ok(())
            }
            Err(_) => Err(()),
        }
    }

    fn execute_callable(&mut self, function: &Callable, excess: bool) -> Result<()> {
        match *function {
            Callable::Closure(closure) => {
                self.enter_scope(closure.function.args, State::Closure(closure));
                self.stack.frame.excess = excess;
                Ok(())
            }
            Callable::Extern(ref ext) => {
                assert!(self.stack.len() >= ext.args + 1);
                let function_index = self.stack.len() - ext.args - 1;
                debug!("------- {} {:?}", function_index, &self.stack[..]);
                self.enter_scope(ext.args, State::Extern(*ext));
                Ok(())
            }
        }
    }

    fn call_function_with_upvars(&mut self,
                                 args: VmIndex,
                                 required_args: VmIndex,
                                 callable: Callable)
                                 -> Result<()> {
        debug!("cmp {} {} {:?} {:?}", args, required_args, callable, {
            let function_index = self.stack.len() - 1 - args;
            &(*self.stack)[(function_index + 1) as usize..]
        });
        match args.cmp(&required_args) {
            Ordering::Equal => self.execute_callable(&callable, false),
            Ordering::Less => {
                let app = {
                    let fields = &self.stack[self.stack.len() - args..];
                    let def = PartialApplicationDataDef(callable, fields);
                    PartialApplication(alloc(&mut self.gc, self.thread, &self.stack.stack, def)?)
                };
                for _ in 0..(args + 1) {
                    self.stack.pop();
                }
                self.stack.push(app);
                Ok(())
            }
            Ordering::Greater => {
                let excess_args = args - required_args;
                let d = {
                    let fields = &self.stack[self.stack.len() - excess_args..];
                    alloc(&mut self.gc,
                          self.thread,
                          &self.stack.stack,
                          Def {
                              tag: 0,
                              elems: fields,
                          })?
                };
                for _ in 0..excess_args {
                    self.stack.pop();
                }
                // Insert the excess args before the actual closure so it does not get
                // collected
                let offset = self.stack.len() - required_args - 1;
                self.stack.insert_slice(offset, &[Data(d)]);
                debug!("xxxxxx {:?}\n{:?}",
                       &(*self.stack)[..],
                       self.stack.stack.get_frames());
                self.execute_callable(&callable, true)
            }
        }
    }

    fn do_call(&mut self, args: VmIndex) -> Result<()> {
        let function_index = self.stack.len() - 1 - args;
        debug!("Do call {:?} {:?}",
               self.stack[function_index],
               &(*self.stack)[(function_index + 1) as usize..]);
        match self.stack[function_index].clone() {
            Function(ref f) => {
                let callable = Callable::Extern(f.clone());
                self.call_function_with_upvars(args, f.args, callable)
            }
            Closure(ref closure) => {
                let callable = Callable::Closure(closure.clone());
                self.call_function_with_upvars(args, closure.function.args, callable)
            }
            PartialApplication(app) => {
                let total_args = app.args.len() as VmIndex + args;
                let offset = self.stack.len() - args;
                self.stack.insert_slice(offset, &app.args);
                self.call_function_with_upvars(total_args, app.function.args(), app.function)
            }
            x => Err(Error::Message(format!("Cannot call {:?}", x))),
        }
    }

    fn execute_(&mut self,
                mut index: usize,
                instructions: &[Instruction],
                function: &BytecodeFunction)
                -> Result<Option<()>> {
        {
            debug!(">>>\nEnter frame {}: {:?}\n{:?}",
                   function.name,
                   &self.stack[..],
                   self.stack.frame);
        }
        while let Some(&instr) = instructions.get(index) {
            debug_instruction(&self.stack, index, instr, function);

            if self.hook.flags.contains(LINE_FLAG) {
                if let Some(ref mut hook) = self.hook.function {
                    let current_line = function.debug_info.source_map.line(index);
                    let previous_line = function.debug_info
                        .source_map
                        .line(self.hook.previous_instruction_index);
                    self.hook.previous_instruction_index = index;
                    if current_line != previous_line {
                        self.stack.frame.instruction_index = index;
                        self.stack.store_frame();
                        let info = DebugInfo {
                            stack: &self.stack.stack,
                            state: LINE_FLAG,
                        };
                        hook(self.thread, info)?
                    }
                }
            }

            match instr {
                Push(i) => {
                    let v = self.stack[i].clone();
                    self.stack.push(v);
                }
                PushInt(i) => {
                    self.stack.push(Int(i));
                }
                PushByte(b) => {
                    self.stack.push(Value::Byte(b));
                }
                PushString(string_index) => {
                    self.stack.push(String(function.strings[string_index as usize].inner()));
                }
                PushGlobal(i) => {
                    let x = function.globals[i as usize];
                    self.stack.push(x);
                }
                PushFloat(f) => self.stack.push(Float(f)),
                Call(args) => {
                    self.stack.frame.instruction_index = index + 1;
                    return self.do_call(args).map(Some);
                }
                TailCall(mut args) => {
                    let mut amount = self.stack.len() - args;
                    if self.stack.frame.excess {
                        amount += 1;
                        match self.stack.excess_args() {
                            Some(excess) => {
                                debug!("TailCall: Push excess args {:?}", excess.fields);
                                for value in &excess.fields {
                                    self.stack.push(*value);
                                }
                                args += excess.fields.len() as VmIndex;
                            }
                            None => panic!("Expected excess args"),
                        }
                    }
                    match self.exit_scope() {
                        Ok(_) => (),
                        Err(_) => {
                            self.enter_scope(args + amount + 1, State::Excess);
                        }
                    };
                    debug!("{} {} {:?}", self.stack.len(), amount, &self.stack[..]);
                    let end = self.stack.len() - args - 1;
                    self.stack.remove_range(end - amount, end);
                    debug!("{:?}", &self.stack[..]);
                    return self.do_call(args).map(Some);
                }
                Construct { tag, args } => {
                    let d = {
                        if args == 0 {
                            Value::Tag(tag)
                        } else {
                            let fields = &self.stack[self.stack.len() - args..];
                            Data(alloc(&mut self.gc,
                                       self.thread,
                                       &self.stack.stack,
                                       Def {
                                           tag: tag,
                                           elems: fields,
                                       })?)
                        }
                    };
                    for _ in 0..args {
                        self.stack.pop();
                    }
                    self.stack.push(d);
                }
                ConstructRecord { record, args } => {
                    let d = {
                        if args == 0 {
                            Value::Tag(0)
                        } else {
                            let fields = &self.stack[self.stack.len() - args..];
                            unsafe {
                                let roots = Roots {
                                    vm: GcPtr::from_raw(self.thread),
                                    stack: &self.stack.stack,
                                };
                                let field_names = &function.records[record as usize];
                                let tag = self.record_map.get_map(&field_names);
                                Data(self.gc
                                    .alloc_and_collect(roots,
                                                       Def {
                                                           tag: tag,
                                                           elems: fields,
                                                       })?)
                            }
                        }
                    };
                    for _ in 0..args {
                        self.stack.pop();
                    }
                    self.stack.push(d);
                }
                ConstructArray(args) => {
                    let d = {
                        let fields = &self.stack[self.stack.len() - args..];
                        alloc(&mut self.gc,
                              self.thread,
                              &self.stack.stack,
                              ::value::ArrayDef(fields))?
                    };
                    for _ in 0..args {
                        self.stack.pop();
                    }
                    self.stack.push(Value::Array(d));
                }
                GetOffset(i) => {
                    match self.stack.pop() {
                        Data(data) => {
                            let v = data.fields[i as usize];
                            self.stack.push(v);
                        }
                        x => return Err(Error::Message(format!("GetOffset on {:?}", x))),
                    }
                }
                GetField(i) => {
                    let field = function.strings[i as usize];
                    match self.stack.pop() {
                        Data(data) => {
                            let offset = self.lookup_field(data.tag, field)?;
                            let v = data.fields[offset as usize];
                            self.stack.push(v);
                        }
                        x => return Err(Error::Message(format!("GetField on {:?}", x))),
                    }
                }
                TestTag(tag) => {
                    let data_tag = match self.stack.top() {
                        Data(ref data) => data.tag,
                        Value::Tag(tag) => tag,
                        _ => {
                            return Err(Error::Message("Op TestTag called on non data type"
                                .to_string()))
                        }
                    };
                    self.stack.push(Value::Tag(if data_tag == tag { 1 } else { 0 }));
                }
                Split => {
                    match self.stack.pop() {
                        Data(data) => {
                            for field in &data.fields {
                                self.stack.push(*field);
                            }
                        }
                        // Zero argument variant
                        Value::Tag(_) => (),
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
                    match self.stack.pop() {
                        Value::Tag(0) => (),
                        _ => {
                            index = i as usize;
                            continue;
                        }
                    }
                }
                Pop(n) => {
                    for _ in 0..n {
                        self.stack.pop();
                    }
                }
                Slide(n) => {
                    debug!("{:?}", &self.stack[..]);
                    let v = self.stack.pop();
                    for _ in 0..n {
                        self.stack.pop();
                    }
                    self.stack.push(v);
                }
                MakeClosure { function_index, upvars } => {
                    let closure = {
                        let args = &self.stack[self.stack.len() - upvars..];
                        let func = function.inner_functions[function_index as usize];
                        Closure(alloc(&mut self.gc,
                                      self.thread,
                                      &self.stack.stack,
                                      ClosureDataDef(func, args))?)
                    };
                    for _ in 0..upvars {
                        self.stack.pop();
                    }
                    self.stack.push(closure);
                }
                NewClosure { function_index, upvars } => {
                    let closure = {
                        // Use dummy variables until it is filled
                        let func = function.inner_functions[function_index as usize];
                        Closure(alloc(&mut self.gc,
                                      self.thread,
                                      &self.stack.stack,
                                      ClosureInitDef(func, upvars as usize))?)
                    };
                    self.stack.push(closure);
                }
                CloseClosure(n) => {
                    let i = self.stack.len() - n - 1;
                    match self.stack[i] {
                        Closure(mut closure) => {
                            // Unique access should be safe as this closure should not be shared as
                            // it has just been allocated and havent even had its upvars set yet
                            // (which is done here).
                            unsafe {
                                for var in closure.as_mut().upvars.iter_mut().rev() {
                                    *var = self.stack.pop();
                                }
                            }
                            self.stack.pop();//Remove the closure
                        }
                        x => panic!("Expected closure, got {:?}", x),
                    }
                }
                PushUpVar(i) => {
                    let v = self.stack.get_upvar(i).clone();
                    self.stack.push(v);
                }
                AddInt => binop_int(self.thread, &mut self.stack, VmInt::add),
                SubtractInt => binop_int(self.thread, &mut self.stack, VmInt::sub),
                MultiplyInt => binop_int(self.thread, &mut self.stack, VmInt::mul),
                DivideInt => binop_int(self.thread, &mut self.stack, VmInt::div),
                IntLT => binop_bool(self.thread, &mut self.stack, |l: VmInt, r| l < r),
                IntEQ => binop_bool(self.thread, &mut self.stack, |l: VmInt, r| l == r),

                AddByte => binop_byte(self.thread, &mut self.stack, u8::add),
                SubtractByte => binop_byte(self.thread, &mut self.stack, u8::sub),
                MultiplyByte => binop_byte(self.thread, &mut self.stack, u8::mul),
                DivideByte => binop_byte(self.thread, &mut self.stack, u8::div),
                ByteLT => binop_bool(self.thread, &mut self.stack, |l: u8, r| l < r),
                ByteEQ => binop_bool(self.thread, &mut self.stack, |l: u8, r| l == r),

                AddFloat => binop_f64(self.thread, &mut self.stack, f64::add),
                SubtractFloat => binop_f64(self.thread, &mut self.stack, f64::sub),
                MultiplyFloat => binop_f64(self.thread, &mut self.stack, f64::mul),
                DivideFloat => binop_f64(self.thread, &mut self.stack, f64::div),
                FloatLT => binop_bool(self.thread, &mut self.stack, |l: f64, r| l < r),
                FloatEQ => binop_bool(self.thread, &mut self.stack, |l: f64, r| l == r),
            }
            index += 1;
        }
        let result = self.stack.top();
        debug!("Return {:?}", result);
        let len = self.stack.len();
        let frame_has_excess = self.stack.frame.excess;
        // We might not get access to the frame above the current as it could be locked
        let stack_exists = self.exit_scope().is_ok();
        self.stack.pop();
        for _ in 0..len {
            self.stack.pop();
        }
        self.stack.push(result);
        if frame_has_excess {
            self.stack.pop();
            // If the function that just finished had extra arguments we need to call the result of
            // the call with the extra arguments
            match self.stack.pop() {
                Data(excess) => {
                    self.enter_scope(0, State::Excess);
                    debug!("Push excess args {:?}", &excess.fields);
                    self.stack.push(result);
                    for value in &excess.fields {
                        self.stack.push(*value);
                    }
                    self.do_call(excess.fields.len() as VmIndex).map(Some)
                }
                x => panic!("Expected excess arguments found {:?}", x),
            }
        } else {
            Ok(if stack_exists { Some(()) } else { None })
        }
    }
}

#[inline]
fn binop_int<'b, F, T>(vm: &'b Thread, stack: &mut StackFrame<'b>, f: F)
    where F: FnOnce(T, T) -> VmInt,
          T: Getable<'b> + fmt::Debug,
{
    binop(vm, stack, |l, r| Value::Int(f(l, r)))
}

#[inline]
fn binop_f64<'b, F, T>(vm: &'b Thread, stack: &mut StackFrame<'b>, f: F)
    where F: FnOnce(T, T) -> f64,
          T: Getable<'b> + fmt::Debug,
{
    binop(vm, stack, |l, r| Value::Float(f(l, r)))
}

#[inline]
fn binop_byte<'b, F, T>(vm: &'b Thread, stack: &mut StackFrame<'b>, f: F)
    where F: FnOnce(T, T) -> u8,
          T: Getable<'b> + fmt::Debug,
{
    binop(vm, stack, |l, r| Value::Byte(f(l, r)))
}

#[inline]
fn binop_bool<'b, F, T>(vm: &'b Thread, stack: &mut StackFrame<'b>, f: F)
    where F: FnOnce(T, T) -> bool,
          T: Getable<'b> + fmt::Debug,
{
    binop(vm, stack, |l, r| Value::Tag(if f(l, r) { 1 } else { 0 }))
}


#[inline]
fn binop<'b, F, T>(vm: &'b Thread, stack: &mut StackFrame<'b>, f: F)
    where F: FnOnce(T, T) -> Value,
          T: Getable<'b> + fmt::Debug,
{
    let r = stack.pop();
    let l = stack.pop();
    match (T::from_value(vm, Variants(&l)), T::from_value(vm, Variants(&r))) {
        (Some(l), Some(r)) => {
            let result = f(l, r);
            // pushing numbers should never return an error so unwrap
            stack.stack.push(result);
        }
        _ => panic!("{:?} `op` {:?}", l, r),
    }
}

fn debug_instruction(stack: &StackFrame,
                     index: usize,
                     instr: Instruction,
                     function: &BytecodeFunction) {
    debug!("{:?}: {:?} -> {:?} {:?}",
           index,
           instr,
           stack.len(),
           match instr {
               Push(i) => {
                   let x = stack.get(i as usize).cloned();
                   if x.is_none() {
                       debug!("{:?}", &stack[..])
                   }
                   x
               }
               PushGlobal(i) => function.globals.get(i as usize).cloned(),
               NewClosure { .. } |
               MakeClosure { .. } => Some(Int(stack.len() as isize)),
               _ => None,
           });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn send_vm() {
        fn send<T: Send>(_: T) {}
        send(RootedThread::new());
    }
}
