//! The thread/vm type
use std::any::Any;
use std::sync::{Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard};
use std::cmp::Ordering;
use std::fmt;
use std::mem;
use std::ops::{Add, Deref, DerefMut, Div, Mul, Sub};
use std::string::String as StdString;
use std::result::Result as StdResult;
use std::sync::Arc;
use std::sync::atomic::{self, AtomicBool};
use std::usize;

use futures::{Async, Future, Poll};
use future::FutureValue;

use base::metadata::Metadata;
use base::pos::Line;
use base::symbol::Symbol;
use base::types::ArcType;
use base::types;

use {Error, Result, Variants};
use macros::MacroEnv;
use api::{Getable, Pushable, ValueRef, VmType};
use compiler::UpvarInfo;
use gc::{DataDef, Gc, GcPtr, Generation, Move};
use source_map::LocalIter;
use stack::{Frame, Lock, Stack, StackFrame, State};
use types::*;
use vm::{GlobalVmState, GlobalVmStateBuilder, VmEnv};
use value::{BytecodeFunction, Callable, ClosureData, ClosureDataDef, ClosureInitDef, Def,
            ExternFunction, GcStr, PartialApplicationDataDef, RecordDef, Userdata, Value,
            ValueRepr};

use value::ValueRepr::{Closure, Data, Float, Function, Int, PartialApplication, String};

pub use gc::Traverseable;

pub struct Execute<T> {
    thread: Option<T>,
}

impl<T> Execute<T>
where
    T: Deref<Target = Thread>,
{
    pub fn new(thread: T) -> Execute<T> {
        Execute {
            thread: Some(thread),
        }
    }
}

impl<T> Future for Execute<T>
where
    T: Deref<Target = Thread>,
{
    type Item = (T, Value);
    type Error = Error;

    // Returns `T` so that it can be reused by the caller
    fn poll(&mut self) -> Poll<(T, Value), Error> {
        let value = {
            let mut context = try_ready!(
                self.thread
                    .as_ref()
                    .expect("cannot poll Execute future after it has succeded")
                    .resume()
            );
            context.stack.pop()
        };
        Ok(Async::Ready((self.thread.take().unwrap(), value)))
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
#[derive(Clone)]
pub struct RootedValue<T>
where
    T: Deref<Target = Thread>,
{
    vm: T,
    value: Value,
}

impl<T> Deref for RootedValue<T>
where
    T: Deref<Target = Thread>,
{
    type Target = Value;
    fn deref(&self) -> &Value {
        &self.value
    }
}

impl<T, U> PartialEq<RootedValue<U>> for RootedValue<T>
where
    T: Deref<Target = Thread>,
    U: Deref<Target = Thread>,
{
    fn eq(&self, other: &RootedValue<U>) -> bool {
        self.value == other.value
    }
}

impl<T> Drop for RootedValue<T>
where
    T: Deref<Target = Thread>,
{
    fn drop(&mut self) {
        // TODO not safe if the root changes order of being dropped with another root
        self.vm.rooted_values.write().unwrap().pop();
    }
}

impl<T> fmt::Debug for RootedValue<T>
where
    T: Deref<Target = Thread>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.value)
    }
}

impl<T> RootedValue<T>
where
    T: Deref<Target = Thread>,
{
    pub fn get_variant(&self) -> Variants {
        unsafe { Variants::new(&self.value) }
    }

    pub fn get_value(&self) -> Value {
        self.value.clone()
    }

    pub fn vm(&self) -> &Thread {
        &self.vm
    }

    pub fn clone_vm(&self) -> T
    where
        T: Clone,
    {
        self.vm.clone()
    }

    pub fn get<'vm>(&'vm self, index: usize) -> Option<RootedValue<T>>
    where
        T: VmRoot<'vm>,
    {
        match self.get_variant().as_ref() {
            ValueRef::Data(ref v) => v.get_variant(index)
                .map(|value| self.vm.root_value(value.get_value())),
            _ => None,
        }
    }

    pub fn as_ref(&self) -> RootedValue<&Thread> {
        self.vm.root_value(self.value.clone())
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
        self.stack.traverse(gc);

        // Traverse the vm's fields, avoiding the stack which is traversed above
        self.vm.traverse_fields_except_stack(gc);
    }
}

impl<'b> ::gc::CollectScope for Roots<'b> {
    fn scope<F>(&self, gc: &mut Gc, f: F)
    where
        F: FnOnce(&mut Gc),
    {
        // We need to pretend that the threads lives for longer than it does on the stack or we
        // can't move the RwLockGuard into the vec. This does end up safe in the end because we
        // never leak any lifetimes outside of this function
        unsafe {
            let mut stack: Vec<GcPtr<Thread>> = Vec::new();
            let mut locks: Vec<(_, _, GcPtr<Thread>)> = Vec::new();

            let child_threads = self.vm.child_threads.read().unwrap();
            for child in &*child_threads {
                Vec::push(&mut stack, *child);
            }

            while let Some(thread_ptr) = stack.pop() {
                if locks.iter().any(|&(_, _, lock_thread)| {
                    &*thread_ptr as *const Thread == &*lock_thread as *const Thread
                }) {
                    continue;
                }

                let thread = mem::transmute::<&Thread, &'static Thread>(&*thread_ptr);
                let child_threads = thread.child_threads.read().unwrap();
                for child in &*child_threads {
                    Vec::push(&mut stack, *child);
                }

                let context = thread.context.lock().unwrap();

                // Since we locked the context we need to scan the thread using `Roots` rather than
                // letting it be scanned normally
                Roots {
                    vm: thread_ptr,
                    stack: &context.stack,
                }.traverse(gc);

                Vec::push(&mut locks, (child_threads, context, thread_ptr));
            }

            // Scan `self` sweep `gc`
            f(gc);

            // `sweep` all child gcs
            for (_, mut context, _) in locks {
                context.gc.sweep();
            }
        }
    }
}

// All threads MUST be allocated in the garbage collected heap. This is necessary as a thread
// calling collect need to mark itself if it is on the garbage collected heap and it has no way of
// knowing wheter it is or not. So the only way of allowing it to mark itself is to disallow it to
// be allocated anywhere else.
/// Representation of the virtual machine
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "::serialization::DeSeed"))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "::serialization::SeSeed"))]
pub struct Thread {
    #[cfg_attr(feature = "serde_derive", serde(state_with = "::base::serialization::shared"))]
    global_state: Arc<GlobalVmState>,
    // The parent of this thread, if it exists must live at least as long as this thread as this
    // thread can refer to any value in the parent thread
    #[cfg_attr(feature = "serde_derive", serde(state))]
    parent: Option<RootedThread>,
    #[cfg_attr(feature = "serde_derive", serde(skip))]
    roots: RwLock<Vec<GcPtr<Traverseable + Send + Sync>>>,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    rooted_values: RwLock<Vec<Value>>,
    /// All threads which this thread have spawned in turn. Necessary as this thread needs to scan
    /// the roots of all its children as well since those may contain references to this threads
    /// garbage collected values
    #[cfg_attr(feature = "serde_derive", serde(state))]
    child_threads: RwLock<Vec<GcPtr<Thread>>>,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    context: Mutex<Context>,
    #[cfg_attr(feature = "serde_derive", serde(skip))]
    interrupt: AtomicBool,
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
        self.context.lock().unwrap().stack.traverse(gc);
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
        context.stack.push(ValueRepr::Thread(self.0));
        Ok(())
    }
}

impl<'vm> Getable<'vm> for RootedThread {
    fn from_value(_: &'vm Thread, value: Variants) -> Self {
        match value.as_ref() {
            ValueRef::Thread(thread) => thread.root_thread(),
            _ => ice!("ValueRef is not a Thread"),
        }
    }
}

/// An instance of `Thread` which is rooted. See the `Thread` type for documentation on interacting
/// with the type.
#[derive(Debug)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "::serialization::DeSeed"))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "::serialization::SeSeed"))]
pub struct RootedThread(#[cfg_attr(feature = "serde_derive", serde(state))] GcPtr<Thread>);

impl Drop for RootedThread {
    fn drop(&mut self) {
        let is_empty = {
            let mut roots = self.parent_threads();
            let index = roots
                .iter()
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
        RootedThread::with_global_state(GlobalVmStateBuilder::default().build())
    }

    pub fn with_global_state(mut global_state: GlobalVmState) -> RootedThread {
        let thread = Thread {
            parent: None,
            context: Mutex::new(Context::new(
                global_state.gc.get_mut().unwrap().new_child_gc(),
            )),
            global_state: Arc::new(global_state),
            roots: RwLock::new(Vec::new()),
            rooted_values: RwLock::new(Vec::new()),
            child_threads: RwLock::new(Vec::new()),
            interrupt: AtomicBool::new(false),
        };
        let mut gc = Gc::new(Generation::default(), usize::MAX);
        let vm = gc.alloc(Move(thread))
            .expect("Not enough memory to allocate thread")
            .root_thread();
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
            interrupt: AtomicBool::new(false),
        };
        // Enter the top level scope
        {
            let mut context = vm.current_context();
            StackFrame::frame(&mut context.stack, 0, State::Unknown);
        }
        let ptr = self.context().gc.alloc(Move(vm))?;

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
    ///
    /// # Examples
    ///
    /// Load the `factorial` rust function into gluon and evaluate `factorial 5`
    ///
    /// ```
    /// # extern crate gluon;
    /// # #[macro_use] extern crate gluon_vm;
    /// # use gluon::{new_vm,Compiler};
    /// # use gluon::base::types::Type;
    /// fn factorial(x: i32) -> i32 {
    ///     if x <= 1 { 1 } else { x * factorial(x - 1) }
    /// }
    /// # fn main() {
    ///
    /// # if ::std::env::var("GLUON_PATH").is_err() {
    /// #     ::std::env::set_var("GLUON_PATH", "..");
    /// # }
    ///
    /// let vm = new_vm();
    ///
    /// vm.define_global("factorial", primitive!(1 factorial)).unwrap();
    ///
    /// let result = Compiler::new()
    ///     .run_expr_async::<i32>(&vm, "example", "factorial 5")
    ///     .sync_or_error()
    ///     .unwrap_or_else(|err| panic!("{}", err));
    /// let expected = (120, Type::int());
    ///
    /// assert_eq!(result, expected);
    /// # }
    /// ```
    ///
    #[deprecated(since = "0.7.0", note = "Use `gluon::import::add_extern_module` instead")]
    pub fn define_global<'vm, T>(&'vm self, name: &str, value: T) -> Result<()>
    where
        T: Pushable<'vm> + VmType,
    {
        let value = {
            let mut context = self.context();
            value.push(self, &mut context)?;
            context.stack.pop()
        };
        self.set_global(
            Symbol::from(format!("@{}", name)),
            T::make_forall_type(self),
            Metadata::default(),
            value,
        )
    }

    /// Retrieves the global called `name`.
    ///
    /// # Examples
    ///
    /// Bind the `(+)` function in gluon's prelude standard library
    /// to an `add` function in rust
    ///
    /// ```rust
    /// # extern crate gluon;
    /// # use gluon::{new_vm, Compiler, Thread};
    /// # use gluon::vm::api::{FunctionRef, Hole, OpaqueValue};
    /// # fn main() {
    ///
    /// # if ::std::env::var("GLUON_PATH").is_err() {
    /// #     ::std::env::set_var("GLUON_PATH", "..");
    /// # }
    ///
    /// let vm = new_vm();
    ///
    /// Compiler::new()
    ///     .run_expr_async::<OpaqueValue<&Thread, Hole>>(&vm, "example",
    ///         r#" import! std.int "#)
    ///     .sync_or_error()
    ///     .unwrap_or_else(|err| panic!("{}", err));
    /// let mut add: FunctionRef<fn(i32, i32) -> i32> =
    ///     vm.get_global("std.int.num.(+)").unwrap();
    /// let result = add.call(1, 2);
    /// assert_eq!(result, Ok(3));
    /// # }
    /// ```
    ///
    /// # Errors
    ///
    /// if the global does not exist or it does not have the correct type.
    ///
    pub fn get_global<'vm, T>(&'vm self, name: &str) -> Result<T>
    where
        T: Getable<'vm> + VmType,
    {
        use check::check_signature;
        let env = self.get_env();
        let (value, actual) = env.get_binding(name)?;
        // Finally check that type of the returned value is correct
        let expected = T::make_type(self);
        if check_signature(&*env, &expected, &actual) {
            unsafe { Ok(T::from_value(self, Variants::new(&value))) }
        } else {
            Err(Error::WrongType(expected, actual.into_owned()))
        }
    }

    /// Retrieves type information about the type `name`. Types inside records can be accessed
    /// using dot notation (std.prelude.Option)
    pub fn find_type_info(&self, name: &str) -> Result<types::Alias<Symbol, ArcType>> {
        let env = self.get_env();
        env.find_type_info(name).map(|alias| alias.into_owned())
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
    where
        T: Pushable<'vm>,
    {
        let mut context = self.current_context();
        v.push(self, &mut context)
    }

    /// Removes the top value from the stack
    pub fn pop(&self) {
        self.current_context().stack.pop();
    }

    pub fn set_memory_limit(&self, memory_limit: usize) {
        self.current_context().gc.set_memory_limit(memory_limit)
    }

    pub fn interrupt(&self) {
        self.interrupt.store(true, atomic::Ordering::Relaxed)
    }

    pub fn interrupted(&self) -> bool {
        self.interrupt.load(atomic::Ordering::Relaxed)
    }

    fn current_context(&self) -> OwnedContext {
        self.context()
    }

    fn traverse_fields_except_stack(&self, gc: &mut Gc) {
        self.global_state.traverse(gc);
        self.roots.read().unwrap().traverse(gc);
        self.rooted_values.read().unwrap().traverse(gc);
        self.child_threads.read().unwrap().traverse(gc);
    }

    fn parent_threads(&self) -> RwLockWriteGuard<Vec<GcPtr<Thread>>> {
        match self.parent {
            Some(ref parent) => parent.child_threads.write().unwrap(),
            None => self.global_state.generation_0_threads.write().unwrap(),
        }
    }

    fn with_roots<F, R>(&self, context: &mut Context, f: F) -> R
    where
        F: for<'b> FnOnce(&mut Gc, Roots<'b>) -> R,
    {
        // For this to be safe we require that the received stack is the same one that is in this
        // VM
        {
            let self_context: *const _ = &self.context;
            let context: *const _ = context;
            assert!(unsafe {
                context as usize >= self_context as usize
                    && context as usize <= self_context.offset(1) as usize
            });
        }
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

pub trait VmRoot<'a>: Deref<Target = Thread> + Clone + 'a {
    fn root(thread: &'a Thread) -> Self;

    /// Roots a value
    fn root_value_with_self(self, value: Value) -> RootedValue<Self> {
        self.rooted_values.write().unwrap().push(value.clone());
        RootedValue {
            vm: self,
            value: value,
        }
    }
}

impl<'a> VmRoot<'a> for &'a Thread {
    fn root(thread: &'a Thread) -> Self {
        thread
    }
}

impl<'a> VmRoot<'a> for RootedThread {
    fn root(thread: &'a Thread) -> Self {
        thread.root_thread()
    }
}

/// Internal functions for interacting with threads. These functions should be considered both
/// unsafe and unstable.
pub trait ThreadInternal
where
    for<'a> &'a Self: Deref<Target = Thread>,
{
    /// Locks and retrives this threads stack
    fn context(&self) -> OwnedContext;

    /// Roots a userdata
    fn root<'vm, T: Userdata>(&'vm self, v: GcPtr<Box<Userdata>>) -> Option<Root<'vm, T>>;

    /// Roots a string
    fn root_string<'vm>(&'vm self, ptr: GcStr) -> RootStr<'vm>;

    /// Roots a value
    fn root_value<'vm, T>(&'vm self, value: Value) -> RootedValue<T>
    where
        T: VmRoot<'vm>;

    /// Evaluates a zero argument function (a thunk)
    fn call_thunk(&self, closure: GcPtr<ClosureData>) -> FutureValue<Execute<&Self>>;

    /// Executes an `IO` action
    fn execute_io(&self, value: Value) -> FutureValue<Execute<&Self>>;

    /// Calls a function on the stack.
    /// When this function is called it is expected that the function exists at
    /// `stack.len() - args - 1` and that the arguments are of the correct type
    fn call_function<'b>(
        &'b self,
        stack: OwnedContext<'b>,
        args: VmIndex,
    ) -> Result<Async<Option<OwnedContext<'b>>>>;

    fn resume(&self) -> Result<Async<OwnedContext>>;

    fn global_env(&self) -> &Arc<GlobalVmState>;

    fn set_global(
        &self,
        name: Symbol,
        typ: ArcType,
        metadata: Metadata,
        value: Value,
    ) -> Result<()>;

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
        v.downcast_ref::<T>().map(|ptr| {
            self.roots.write().unwrap().push(v.as_traverseable());
            Root {
                roots: &self.roots,
                ptr: ptr,
            }
        })
    }

    /// Roots a string
    fn root_string<'vm>(&'vm self, ptr: GcStr) -> RootStr<'vm> {
        self.roots
            .write()
            .unwrap()
            .push(ptr.into_inner().as_traverseable());
        RootStr(Root {
            roots: &self.roots,
            ptr: &*ptr,
        })
    }

    /// Roots a value
    fn root_value<'vm, T>(&'vm self, value: Value) -> RootedValue<T>
    where
        T: VmRoot<'vm>,
    {
        self.rooted_values.write().unwrap().push(value.clone());
        RootedValue {
            vm: T::root(self),
            value: value,
        }
    }

    fn call_thunk(&self, closure: GcPtr<ClosureData>) -> FutureValue<Execute<&Thread>> {
        let mut context = self.current_context();
        context.stack.push(Closure(closure));
        context.borrow_mut().enter_scope(0, State::Closure(closure));
        let async = try_future!(context.execute(false));
        match async {
            Async::Ready(context) => FutureValue::Value(Ok((self, context.unwrap().stack.pop()))),
            Async::NotReady => FutureValue::Future(Execute::new(self)),
        }
    }

    /// Calls a module, allowed to to run IO expressions
    fn execute_io(&self, value: Value) -> FutureValue<Execute<&Self>> {
        debug!("Run IO {:?}", value);
        let mut context = self.context();
        // Dummy value to fill the place of the function for TailCall
        context.stack.push(Int(0));

        context.stack.push(value);
        context.stack.push(Int(0));

        context.borrow_mut().enter_scope(2, State::Unknown);
        context = match try_future!(self.call_function(context, 1)) {
            Async::Ready(context) => context.expect("call_module to have the stack remaining"),
            Async::NotReady => return FutureValue::Future(Execute::new(self)),
        };
        let result = context.stack.pop();
        {
            let mut context = context.borrow_mut();
            while context.stack.len() > 0 {
                context.stack.pop();
            }
        }
        let _ = context.exit_scope();
        FutureValue::Value(Ok((self, result)))
    }

    /// Calls a function on the stack.
    /// When this function is called it is expected that the function exists at
    /// `stack.len() - args - 1` and that the arguments are of the correct type
    fn call_function<'b>(
        &'b self,
        mut context: OwnedContext<'b>,
        args: VmIndex,
    ) -> Result<Async<Option<OwnedContext<'b>>>> {
        context.borrow_mut().do_call(args)?;
        context.execute(false)
    }

    fn resume(&self) -> Result<Async<OwnedContext>> {
        let mut context = self.current_context();
        if context.stack.get_frames().len() == 1 {
            // Only the top level frame left means that the thread has finished
            return Err(Error::Dead);
        }
        context = try_ready!(context.execute(true)).unwrap();
        Ok(Async::Ready(context))
    }

    fn global_env(&self) -> &Arc<GlobalVmState> {
        &self.global_state
    }

    fn set_global(
        &self,
        name: Symbol,
        typ: ArcType,
        metadata: Metadata,
        value: Value,
    ) -> Result<()> {
        let value = ::value::Cloner::new(self, &mut self.global_env().gc.lock().unwrap())
            .deep_clone(&value)?;
        self.global_env().set_global(name, typ, metadata, value)
    }

    fn deep_clone_value(&self, owner: &Thread, value: Value) -> Result<Value> {
        let mut context = self.current_context();
        let full_clone = !self.can_share_values_with(&mut context.gc, owner);
        let mut cloner = ::value::Cloner::new(self, &mut context.gc);
        if full_clone {
            cloner.force_full_clone();
        }
        cloner.deep_clone(&value)
    }

    fn can_share_values_with(&self, gc: &mut Gc, other: &Thread) -> bool {
        if self as *const Thread == other as *const Thread {
            return true;
        }
        // If the threads do not share the same global state then they are disjoint and can't share
        // values
        if &*self.global_state as *const GlobalVmState
            != &*other.global_state as *const GlobalVmState
        {
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

pub type HookFn = Box<FnMut(&Thread, DebugInfo) -> Result<Async<()>> + Send + Sync>;

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
            State::Closure(ref closure) => closure
                .function
                .debug_info
                .source_map
                .line(self.instruction_index()),
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
            State::Closure(ref closure) => closure
                .function
                .debug_info
                .local_map
                .locals(self.instruction_index()),
            _ => LocalIter::empty(),
        }
    }

    /// Returns a slice with information about the values bound to this closure
    pub fn upvars(&self) -> &[UpvarInfo] {
        match self.frame().state {
            State::Closure(ref closure) => &closure.function.debug_info.upvars,
            _ => ice!("Attempted to access upvar in non closure function"),
        }
    }
}

bitflags! {
    #[derive(Default)]
    pub struct HookFlags: u8 {
        /// Call the hook when execution moves to a new line
        const LINE_FLAG = 0b01;
        /// Call the hook when a function is called
        const CALL_FLAG = 0b10;
    }
}

#[derive(Default)]
struct Hook {
    function: Option<HookFn>,
    flags: HookFlags,
    // The index of the last executed instruction
    previous_instruction_index: usize,
}

#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(feature = "serde_derive", serde(deserialize_state = "::serialization::DeSeed"))]
#[cfg_attr(feature = "serde_derive", serde(serialize_state = "::serialization::SeSeed"))]
pub struct Context {
    // FIXME It is dangerous to write to gc and stack
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub stack: Stack,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub gc: Gc,
    #[cfg_attr(feature = "serde_derive", serde(skip))]
    hook: Hook,
    max_stack_size: VmIndex,

    /// Stack of polling functions used for extern functions returning futures
    #[cfg_attr(feature = "serde_derive", serde(skip))]
    poll_fns: Vec<
        (
            Option<Lock>,
            Box<for<'vm> FnMut(&'vm Thread) -> Result<Async<OwnedContext<'vm>>> + Send>,
        ),
    >,
}

impl Context {
    fn new(gc: Gc) -> Context {
        Context {
            gc: gc,
            stack: Stack::new(),
            hook: Hook {
                function: None,
                flags: HookFlags::empty(),
                previous_instruction_index: usize::max_value(),
            },
            max_stack_size: VmIndex::max_value(),
            poll_fns: Vec::new(),
        }
    }

    pub fn new_data(&mut self, thread: &Thread, tag: VmTag, fields: &[Value]) -> Result<Value> {
        self.alloc_with(
            thread,
            Def {
                tag: tag,
                elems: fields,
            },
        ).map(ValueRepr::Data)
            .map(Value::from)
    }

    pub fn alloc_with<D>(&mut self, thread: &Thread, data: D) -> Result<GcPtr<D::Value>>
    where
        D: DataDef + Traverseable,
        D::Value: Sized + Any,
    {
        alloc(&mut self.gc, thread, &self.stack, data)
    }

    pub fn alloc_ignore_limit<D>(&mut self, data: D) -> GcPtr<D::Value>
    where
        D: DataDef + Traverseable,
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

    /// "Returns a future", letting the virtual machine know that `future` must be resolved to
    /// produce the actual value.
    ///
    /// # Safety
    ///
    /// This function is unsafe because the `vm` lifetime must not outlive the lifetime of the
    /// `Thread`
    pub unsafe fn return_future<'vm, F>(&mut self, mut future: F, lock: Lock)
    where
        F: Future<Error = Error> + Send + 'static,
        F::Item: Pushable<'vm>,
    {
        use std::mem::transmute;

        let lock = if self.poll_fns.is_empty() {
            self.stack.release_lock(lock);
            None
        } else {
            Some(lock)
        };

        self.poll_fns.push((
            lock,
            Box::new(move |vm| {
                let value = try_ready!(future.poll());

                let mut context = vm.current_context();
                let vm = transmute::<&Thread, &'vm Thread>(vm);
                value.push(vm, &mut context).map(|()| Async::Ready(context))
            }),
        ));
    }
}

impl<'b> OwnedContext<'b> {
    pub fn alloc<D>(&mut self, data: D) -> Result<GcPtr<D::Value>>
    where
        D: DataDef + Traverseable,
        D::Value: Sized + Any,
    {
        let Context {
            ref mut gc,
            ref stack,
            ..
        } = **self;
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
where
    D: DataDef + Traverseable,
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

const INITIAL_CALL: usize = 0;
const POLL_CALL: usize = 1;
const IN_POLL: usize = 2;

impl<'b> OwnedContext<'b> {
    fn exit_scope(mut self) -> StdResult<OwnedContext<'b>, ()> {
        let exists = StackFrame::current(&mut self.stack).exit_scope().is_ok();
        if exists {
            Ok(self)
        } else {
            Err(())
        }
    }

    fn execute(self, polled: bool) -> Result<Async<Option<OwnedContext<'b>>>> {
        let mut maybe_context = Some(self);
        while let Some(mut context) = maybe_context {
            if context.thread.interrupted() {
                return Err(Error::Interrupted);
            }
            debug!("STACK\n{:?}", context.stack.get_frames());
            let state = context.borrow_mut().stack.frame.state;

            let instruction_index = context.borrow_mut().stack.frame.instruction_index;
            if instruction_index == 0 && context.hook.flags.contains(HookFlags::CALL_FLAG) {
                match state {
                    State::Extern(_) | State::Closure(_) => {
                        let thread = context.thread;
                        let context = &mut *context;
                        if let Some(ref mut hook) = context.hook.function {
                            let info = DebugInfo {
                                stack: &context.stack,
                                state: HookFlags::CALL_FLAG,
                            };
                            try_ready!(hook(thread, info))
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
                    if instruction_index == IN_POLL {
                        return Ok(Async::Ready(Some(context)));
                    }
                    context.borrow_mut().stack.frame.instruction_index = POLL_CALL;
                    Some(try_ready!(context.execute_function(
                        instruction_index == INITIAL_CALL,
                        &ext,
                        polled,
                    )))
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
                        if instruction_index == 0
                            && context.stack.stack.len() + function_size > max_stack_size
                        {
                            return Err(Error::StackOverflow(max_stack_size));
                        }

                        if context.stack.stack.get_frames().len() == 0 {
                            State::ReturnContext
                        } else {
                            info!(
                                "Continue with {}\nAt: {}/{}\n{:?}",
                                closure.function.name,
                                instruction_index,
                                closure.function.instructions.len(),
                                &context.stack[..]
                            );

                            let new_context = try_ready!(context.execute_(
                                instruction_index,
                                &closure.function.instructions,
                                &closure.function,
                            ));
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

    fn execute_function(
        mut self,
        initial_call: bool,
        function: &ExternFunction,
        polled: bool,
    ) -> Result<Async<OwnedContext<'b>>> {
        info!(
            "CALL EXTERN {} {:?}",
            function.id,
            &self.stack.current_frame()[..],
        );

        let mut status = Status::Ok;
        if initial_call {
            // Make sure that the stack is not borrowed during the external function call
            // Necessary since we do not know what will happen during the function call
            let thread = self.thread;
            drop(self);
            status = (function.function)(thread);

            if status == Status::Yield {
                return Ok(Async::NotReady);
            }

            self = thread.current_context();

            if status == Status::Error {
                return match self.stack.pop().get_repr() {
                    String(s) => Err(Error::Panic(s.to_string())),
                    _ => Err(Error::Message(format!(
                        "Unexpected error calling function `{}`",
                        function.id
                    ))),
                };
            }

            // The `poll_fn` at the top may be for a stack frame at a lower level, return to the
            // state loop to ensure that we are executing the frame at the top of the stack
            if !self.poll_fns.is_empty() {
                return Ok(Async::Ready(self));
            }
        }
        while let Some((lock, mut poll_fn)) = self.poll_fns.pop() {
            // We can only poll the future if the code is currently executing in a future
            if !polled {
                self.poll_fns.push((lock, poll_fn));
                return Ok(Async::NotReady);
            }

            let frame_offset = self.stack.get_frames().len() - 1;
            if self.poll_fns.is_empty() {
                self.stack.get_frames_mut()[frame_offset].instruction_index = IN_POLL;
            }
            let thread = self.thread;
            drop(self);
            // Poll the future that was returned from the initial call to this extern function
            match poll_fn(thread)? {
                Async::Ready(context) => {
                    self = context;
                    if let Some(lock) = lock {
                        self.stack.release_lock(lock);
                    }
                    self.borrow_mut().stack.frame.instruction_index = POLL_CALL;
                    return Ok(Async::Ready(self));
                }
                Async::NotReady => {
                    self = thread.current_context();
                    self.stack.get_frames_mut()[frame_offset].instruction_index = POLL_CALL;
                    // Restore `poll_fn` so it can be polled again
                    self.poll_fns.push((lock, poll_fn));
                    return Ok(Async::NotReady);
                }
            }
        }

        // The function call is done at this point so remove any extra values from the frame and
        // return the value at the top of the stack
        let result = self.stack.pop();
        {
            let mut stack = self.stack.current_frame();
            while stack.len() > 0 {
                debug!("{} {:?}", stack.len(), &*stack);
                stack.pop();
            }
            if !(match stack.frame.state {
                State::Extern(ref e) => e.id == function.id,
                _ => false,
            }) {
                "asd".to_string();
            }
            debug_assert!(
                match stack.frame.state {
                    State::Extern(ref e) => e.id == function.id,
                    _ => false,
                },
                "Attempted to pop {:?} but {} was expected",
                stack.frame,
                function.id
            )
        }
        self = self.exit_scope().map_err(|_| {
            Error::Message(StdString::from("Poped the last frame in execute_function"))
        })?;
        self.stack.pop(); // Pop function
        self.stack.push(result);

        info!(
            "EXIT EXTERN {} {:?}",
            function.id,
            &self.stack.current_frame()[..]
        );

        match status {
            Status::Ok => Ok(Async::Ready(self)),
            Status::Yield => Ok(Async::NotReady),
            Status::Error => match self.stack.pop().get_repr() {
                String(s) => Err(Error::Panic(s.to_string())),
                _ => Err(Error::Message(format!(
                    "Unexpected error calling function `{}`",
                    function.id
                ))),
            },
        }
    }

    fn borrow_mut(&mut self) -> ExecuteContext {
        let context = &mut **self;
        ExecuteContext {
            thread: self.thread,
            gc: &mut context.gc,
            stack: StackFrame::current(&mut context.stack),
            hook: &mut context.hook,
        }
    }
}

struct ExecuteContext<'b> {
    thread: &'b Thread,
    stack: StackFrame<'b>,
    gc: &'b mut Gc,
    hook: &'b mut Hook,
}

impl<'b> ExecuteContext<'b> {
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

    fn call_function_with_upvars(
        &mut self,
        args: VmIndex,
        required_args: VmIndex,
        callable: Callable,
    ) -> Result<()> {
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
                    alloc(
                        &mut self.gc,
                        self.thread,
                        &self.stack.stack,
                        Def {
                            tag: 0,
                            elems: fields,
                        },
                    )?
                };
                for _ in 0..excess_args {
                    self.stack.pop();
                }
                // Insert the excess args before the actual closure so it does not get
                // collected
                let offset = self.stack.len() - required_args - 1;
                self.stack.insert_slice(offset, &[Value::from(Data(d))]);
                debug!(
                    "xxxxxx {:?}\n{:?}",
                    &(*self.stack)[..],
                    self.stack.stack.get_frames()
                );
                self.execute_callable(&callable, true)
            }
        }
    }

    fn do_call(&mut self, args: VmIndex) -> Result<()> {
        let function_index = self.stack.len() - 1 - args;
        info!(
            "Do call {:?} {:?}",
            self.stack[function_index],
            &(*self.stack)[(function_index + 1) as usize..]
        );
        match self.stack[function_index].clone().get_repr() {
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

    fn execute_(
        &mut self,
        mut index: usize,
        instructions: &[Instruction],
        function: &BytecodeFunction,
    ) -> Result<Async<Option<()>>> {
        {
            debug!(
                ">>>\nEnter frame {}: {:?}\n{:?}",
                function.name,
                &self.stack[..],
                self.stack.frame
            );
        }
        while let Some(&instr) = instructions.get(index) {
            debug_instruction(&self.stack, index, instr);

            if self.hook.flags.contains(HookFlags::LINE_FLAG) {
                if let Some(ref mut hook) = self.hook.function {
                    let current_line = function.debug_info.source_map.line(index);
                    let previous_line = function
                        .debug_info
                        .source_map
                        .line(self.hook.previous_instruction_index);
                    self.hook.previous_instruction_index = index;
                    if current_line != previous_line {
                        self.stack.frame.instruction_index = index;
                        self.stack.store_frame();
                        let info = DebugInfo {
                            stack: &self.stack.stack,
                            state: HookFlags::LINE_FLAG,
                        };
                        try_ready!(hook(self.thread, info))
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
                    self.stack.push(ValueRepr::Byte(b));
                }
                PushString(string_index) => {
                    self.stack
                        .push(String(function.strings[string_index as usize].inner()));
                }
                PushFloat(f) => self.stack.push(Float(f)),
                Call(args) => {
                    self.stack.frame.instruction_index = index + 1;
                    return self.do_call(args).map(|x| Async::Ready(Some(x)));
                }
                TailCall(mut args) => {
                    let mut amount = self.stack.len() - args;
                    if self.stack.frame.excess {
                        amount += 1;
                        match self.stack.excess_args() {
                            Some(excess) => {
                                debug!("TailCall: Push excess args {:?}", excess.fields);
                                for value in &excess.fields {
                                    self.stack.push(value);
                                }
                                args += excess.fields.len() as VmIndex;
                            }
                            None => ice!("Expected excess args"),
                        }
                    }
                    debug_assert!(
                        match self.stack.frame.state {
                            State::Closure(ref c) => c.function.name == function.name,
                            _ => false,
                        },
                        "Attempted to pop {:?} but `{}` was expected",
                        self.stack.frame.state,
                        function.name
                    );
                    match self.exit_scope() {
                        Ok(_) => (),
                        Err(_) => {
                            self.enter_scope(args + amount + 1, State::Excess);
                        }
                    };
                    info!(
                        "Clearing {} {} {:?}",
                        self.stack.len(),
                        amount,
                        &self.stack[..]
                    );
                    let end = self.stack.len() - args - 1;
                    self.stack.remove_range(end - amount, end);
                    debug!("{:?}", &self.stack[..]);
                    return self.do_call(args).map(|x| Async::Ready(Some(x)));
                }
                Construct { tag, args } => {
                    let d = {
                        if args == 0 {
                            ValueRepr::Tag(tag)
                        } else {
                            let fields = &self.stack[self.stack.len() - args..];
                            Data(alloc(
                                &mut self.gc,
                                self.thread,
                                &self.stack.stack,
                                Def {
                                    tag: tag,
                                    elems: fields,
                                },
                            )?)
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
                            ValueRepr::Tag(0)
                        } else {
                            let fields = &self.stack[self.stack.len() - args..];
                            unsafe {
                                let roots = Roots {
                                    vm: GcPtr::from_raw(self.thread),
                                    stack: &self.stack.stack,
                                };
                                let field_names = &function.records[record as usize];
                                Data(self.gc.alloc_and_collect(
                                    roots,
                                    RecordDef {
                                        elems: fields,
                                        fields: field_names,
                                    },
                                )?)
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
                        alloc(
                            &mut self.gc,
                            self.thread,
                            &self.stack.stack,
                            ::value::ArrayDef(fields),
                        )?
                    };
                    for _ in 0..args {
                        self.stack.pop();
                    }
                    self.stack.push(ValueRepr::Array(d));
                }
                GetOffset(i) => match self.stack.pop().get_repr() {
                    Data(data) => {
                        let v = &data.fields[i as usize];
                        self.stack.push(v);
                    }
                    x => return Err(Error::Message(format!("GetOffset on {:?}", x))),
                },
                GetField(i) => {
                    let field = function.strings[i as usize];
                    match self.stack.pop().get_repr() {
                        Data(data) => {
                            let v = data.get_field(field).expect("ICE: Field does not exist");
                            self.stack.push(v);
                        }
                        x => return Err(Error::Message(format!("GetField on {:?}", x))),
                    }
                }
                TestTag(tag) => {
                    let data_tag = match self.stack.top().get_repr() {
                        Data(ref data) => data.tag(),
                        ValueRepr::Tag(tag) => tag,
                        _ => {
                            return Err(Error::Message(
                                "Op TestTag called on non data type".to_string(),
                            ))
                        }
                    };
                    self.stack
                        .push(ValueRepr::Tag(if data_tag == tag { 1 } else { 0 }));
                }
                Split => {
                    match self.stack.pop().get_repr() {
                        Data(data) => for field in &data.fields {
                            self.stack.push(field);
                        },
                        // Zero argument variant
                        ValueRepr::Tag(_) => (),
                        _ => {
                            return Err(Error::Message(
                                "Op Split called on non data type".to_string(),
                            ))
                        }
                    }
                }
                Jump(i) => {
                    index = i as usize;
                    continue;
                }
                CJump(i) => match self.stack.pop().get_repr() {
                    ValueRepr::Tag(0) => (),
                    _ => {
                        index = i as usize;
                        continue;
                    }
                },
                Pop(n) => for _ in 0..n {
                    self.stack.pop();
                },
                Slide(n) => {
                    debug!("{:?}", &self.stack[..]);
                    let v = self.stack.pop();
                    for _ in 0..n {
                        self.stack.pop();
                    }
                    self.stack.push(v);
                }
                MakeClosure {
                    function_index,
                    upvars,
                } => {
                    let closure = {
                        let args = &self.stack[self.stack.len() - upvars..];
                        let func = function.inner_functions[function_index as usize];
                        Closure(alloc(
                            &mut self.gc,
                            self.thread,
                            &self.stack.stack,
                            ClosureDataDef(func, args),
                        )?)
                    };
                    for _ in 0..upvars {
                        self.stack.pop();
                    }
                    self.stack.push(closure);
                }
                NewClosure {
                    function_index,
                    upvars,
                } => {
                    let closure = {
                        // Use dummy variables until it is filled
                        let func = function.inner_functions[function_index as usize];
                        Closure(alloc(
                            &mut self.gc,
                            self.thread,
                            &self.stack.stack,
                            ClosureInitDef(func, upvars as usize),
                        )?)
                    };
                    self.stack.push(closure);
                }
                CloseClosure(n) => {
                    let i = self.stack.len() - n - 1;
                    match self.stack[i].get_repr() {
                        Closure(mut closure) => {
                            // Unique access should be safe as this closure should not be shared as
                            // it has just been allocated and havent even had its upvars set yet
                            // (which is done here).
                            unsafe {
                                for var in closure.as_mut().upvars.iter_mut().rev() {
                                    *var = self.stack.pop();
                                }
                            }
                            self.stack.pop(); //Remove the closure
                        }
                        x => ice!("Expected closure, got {:?}", x),
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
        let result = self.stack.top().clone();
        debug!("Return {:?}", result);
        let len = self.stack.len();
        let frame_has_excess = self.stack.frame.excess;

        // We might not get access to the frame above the current as it could be locked
        debug_assert!(
            match self.stack.frame.state {
                State::Closure(ref c) => c.function.name == function.name,
                _ => false,
            },
            "Attempted to pop {:?} but `{}` was expected",
            self.stack.frame.state,
            function.name
        );
        let stack_exists = self.exit_scope().is_ok();

        self.stack.pop();
        for _ in 0..len {
            self.stack.pop();
        }
        if frame_has_excess {
            // If the function that just finished had extra arguments we need to call the result of
            // the call with the extra arguments
            match self.stack.pop().get_repr() {
                Data(excess) => {
                    self.enter_scope(0, State::Excess);
                    debug!("Push excess args {:?}", &excess.fields);
                    self.stack.push(result);
                    for value in &excess.fields {
                        self.stack.push(value);
                    }
                    self.do_call(excess.fields.len() as VmIndex)
                        .map(|x| Async::Ready(Some(x)))
                }
                x => ice!("Expected excess arguments found {:?}", x),
            }
        } else {
            self.stack.push(result);
            Ok(Async::Ready(if stack_exists { Some(()) } else { None }))
        }
    }
}

#[inline]
fn binop_int<'b, F, T>(vm: &'b Thread, stack: &mut StackFrame<'b>, f: F)
where
    F: FnOnce(T, T) -> VmInt,
    T: Getable<'b> + fmt::Debug,
{
    binop(vm, stack, |l, r| ValueRepr::Int(f(l, r)))
}

#[inline]
fn binop_f64<'b, F, T>(vm: &'b Thread, stack: &mut StackFrame<'b>, f: F)
where
    F: FnOnce(T, T) -> f64,
    T: Getable<'b> + fmt::Debug,
{
    binop(vm, stack, |l, r| ValueRepr::Float(f(l, r)))
}

#[inline]
fn binop_byte<'b, F, T>(vm: &'b Thread, stack: &mut StackFrame<'b>, f: F)
where
    F: FnOnce(T, T) -> u8,
    T: Getable<'b> + fmt::Debug,
{
    binop(vm, stack, |l, r| ValueRepr::Byte(f(l, r)))
}

#[inline]
fn binop_bool<'b, F, T>(vm: &'b Thread, stack: &mut StackFrame<'b>, f: F)
where
    F: FnOnce(T, T) -> bool,
    T: Getable<'b> + fmt::Debug,
{
    binop(vm, stack, |l, r| {
        ValueRepr::Tag(if f(l, r) { 1 } else { 0 })
    })
}

#[inline]
fn binop<'b, F, T>(vm: &'b Thread, stack: &mut StackFrame<'b>, f: F)
where
    F: FnOnce(T, T) -> ValueRepr,
    T: Getable<'b> + fmt::Debug,
{
    let (l, r) = {
        let r = stack.get_variant(stack.len() - 1).unwrap();
        let l = stack.get_variant(stack.len() - 2).unwrap();
        (T::from_value(vm, l), T::from_value(vm, r))
    };
    let result = f(l, r);
    stack.pop();
    stack.pop();
    stack.stack.push(result);
}

fn debug_instruction(stack: &StackFrame, index: usize, instr: Instruction) {
    debug!(
        "{:?}: {:?} -> {:?} {:?}",
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
            NewClosure { .. } | MakeClosure { .. } => Some(Value::from(Int(stack.len() as isize))),
            _ => None,
        }
    );
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
