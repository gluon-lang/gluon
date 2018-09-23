//! The thread/vm type
use std::any::{Any, TypeId};
use std::cmp::Ordering;
use std::fmt;
use std::mem;
use std::ops::{Add, Deref, DerefMut, Div, Mul, Sub};
use std::result::Result as StdResult;
use std::string::String as StdString;
use std::sync::atomic::{self, AtomicBool};
use std::sync::Arc;
use std::sync::{Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard};
use std::usize;

use futures::future::{self, Either, FutureResult};
use futures::{Async, Future, Poll};

use base::metadata::Metadata;
use base::pos::Line;
use base::symbol::Symbol;
use base::types::{self, Alias, ArcType};

use api::{Getable, Pushable, ValueRef, VmType};
use compiler::UpvarInfo;
use gc::{DataDef, Gc, GcPtr, Generation, Move};
use interner::InternedStr;
use macros::MacroEnv;
use source_map::LocalIter;
use stack::{
    ClosureState, ExternCallState, ExternState, Frame, Lock, Stack, StackFrame, StackState, State,
};
use types::*;
use value::{
    BytecodeFunction, Callable, ClosureData, ClosureDataDef, ClosureInitDef, Def, ExternFunction,
    PartialApplicationDataDef, RecordDef, UninitializedRecord, UninitializedVariantDef, Userdata,
    Value, ValueRepr,
};
use vm::{GlobalVmState, GlobalVmStateBuilder, VmEnv};
use {BoxFuture, Error, Result, Variants};

use value::ValueRepr::{Closure, Data, Float, Function, Int, PartialApplication, String};

pub use gc::Traverseable;

pub type FutureValue<F> = Either<FutureResult<<F as Future>::Item, <F as Future>::Error>, F>;

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

    pub fn root(&self) -> Execute<RootedThread> {
        Execute {
            thread: self.thread.as_ref().map(|t| t.root_thread()),
        }
    }
}

impl<'vm, T> Future for Execute<T>
where
    T: Deref<Target = Thread>,
    T: VmRoot<'vm>,
{
    type Item = RootedValue<T>;
    type Error = Error;

    // Returns `T` so that it can be reused by the caller
    fn poll(&mut self) -> Poll<Self::Item, Error> {
        let value = {
            let thread = self
                .thread
                .as_ref()
                .expect("cannot poll Execute future after it has succeded");
            let mut context = try_ready!(thread.resume());
            context.stack.pop()
        };

        unsafe {
            Ok(Async::Ready(
                self.thread
                    .take()
                    .unwrap()
                    .root_value_with_self(Variants::new(&value)),
            ))
        }
    }
}

pub struct ExecuteTop<T>(pub Execute<T>);

impl<'vm, T> Future for ExecuteTop<T>
where
    T: Deref<Target = Thread>,
    T: VmRoot<'vm>,
{
    type Item = RootedValue<T>;
    type Error = Error;

    // Returns `T` so that it can be reused by the caller
    fn poll(&mut self) -> Poll<Self::Item, Error> {
        let thread = self
            .0
            .thread
            .as_ref()
            .expect("cannot poll Execute future after it has succeded")
            .clone();
        match self.0.poll() {
            Ok(Async::Ready(x)) => Ok(Async::Ready(x)),
            Ok(Async::NotReady) => Ok(Async::NotReady),
            Err(mut err) => {
                let mut context = thread.context();
                let stack = StackFrame::<State>::current(&mut context.stack);
                let new_trace = reset_stack(stack, 1)?;
                if let Error::Panic(_, ref mut trace) = err {
                    *trace = Some(new_trace);
                }
                Err(err)
            }
        }
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
pub struct RootedValue<T>
where
    T: Deref<Target = Thread>,
{
    vm: T,
    value: Value,
}

impl<T> Clone for RootedValue<T>
where
    T: Deref<Target = Thread> + Clone,
{
    fn clone(&self) -> Self {
        self.vm
            .rooted_values
            .write()
            .unwrap()
            .push(self.value.clone());
        RootedValue {
            vm: self.vm.clone(),
            value: self.value.clone(),
        }
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
        let mut rooted_values = self.vm.rooted_values.write().unwrap();
        let i = rooted_values
            .iter()
            .position(|p| p.obj_eq(&self.value))
            .unwrap_or_else(|| ice!("Rooted value has already been dropped"));
        rooted_values.swap_remove(i);
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
    pub fn re_root<'vm, U>(self, vm: U) -> RootedValue<U>
    where
        U: VmRoot<'vm>,
    {
        vm.rooted_values.write().unwrap().push(self.value.clone());
        RootedValue {
            vm,
            value: self.value.clone(),
        }
    }

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

    /// looks up the field at the given offset
    pub fn get<'vm>(&'vm self, index: usize) -> Option<RootedValue<T>>
    where
        T: VmRoot<'vm>,
    {
        match self.get_variant().as_ref() {
            ValueRef::Data(ref v) => v.get_variant(index).map(|value| self.vm.root_value(value)),
            _ => None,
        }
    }

    /// looks up the record field with the given name
    pub fn get_field<'vm>(&'vm self, name: &str) -> Option<RootedValue<T>>
    where
        T: VmRoot<'vm>,
    {
        match self.get_variant().as_ref() {
            ValueRef::Data(ref v) => v
                .lookup_field(&*self.vm, name)
                .map(|value| self.vm.root_value(value)),
            _ => None,
        }
    }

    pub fn as_ref(&self) -> RootedValue<&Thread> {
        self.vm.root_value(self.get_variant())
    }
}

impl<'vm> RootedValue<&'vm Thread> {
    pub fn vm_(&self) -> &'vm Thread {
        self.vm
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
            let locks = self.mark_child_roots(gc);
            // Scan `self` sweep `gc`
            f(gc);

            // `sweep` all child gcs
            for (_, mut context, _) in locks {
                context.gc.sweep();
            }
        }
    }
}

impl<'b> Roots<'b> {
    unsafe fn mark_child_roots(
        &self,
        gc: &mut Gc,
    ) -> Vec<(
        RwLockReadGuard<Vec<GcPtr<Thread>>>,
        MutexGuard<Context>,
        GcPtr<Thread>,
    )> {
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
        locks
    }
}

// All threads MUST be allocated in the garbage collected heap. This is necessary as a thread
// calling collect need to mark itself if it is on the garbage collected heap and it has no way of
// knowing wheter it is or not. So the only way of allowing it to mark itself is to disallow it to
// be allocated anywhere else.
/// Representation of the virtual machine
#[cfg_attr(
    feature = "serde_derive",
    derive(DeserializeState, SerializeState)
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(deserialize_state = "::serialization::DeSeed")
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(serialize_state = "::serialization::SeSeed")
)]
pub struct Thread {
    #[cfg_attr(
        feature = "serde_derive",
        serde(state_with = "::base::serialization::shared")
    )]
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
    fn push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.push(ValueRepr::Thread(self.0));
        Ok(())
    }
}

impl<'vm, 'value> Getable<'vm, 'value> for RootedThread {
    fn from_value(_: &'vm Thread, value: Variants<'value>) -> Self {
        match value.as_ref() {
            ValueRef::Thread(thread) => thread.root_thread(),
            _ => ice!("ValueRef is not a Thread"),
        }
    }
}

/// An instance of `Thread` which is rooted. See the `Thread` type for documentation on interacting
/// with the type.
#[derive(Debug)]
#[cfg_attr(
    feature = "serde_derive",
    derive(DeserializeState, SerializeState)
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(deserialize_state = "::serialization::DeSeed")
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(serialize_state = "::serialization::SeSeed")
)]
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
        let vm = gc
            .alloc(Move(thread))
            .expect("Not enough memory to allocate thread")
            .root_thread();
        *vm.global_state.gc.lock().unwrap() = gc;
        // Enter the top level scope
        {
            let mut context = vm.context.lock().unwrap();
            StackFrame::<State>::frame(&mut context.stack, 0, State::Unknown);
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
            context: Mutex::new(Context::new(self.owned_context().gc.new_child_gc())),
            roots: RwLock::new(Vec::new()),
            rooted_values: RwLock::new(Vec::new()),
            child_threads: RwLock::new(Vec::new()),
            interrupt: AtomicBool::new(false),
        };
        // Enter the top level scope
        {
            let mut context = vm.owned_context();
            StackFrame::<State>::frame(&mut context.stack, 0, State::Unknown);
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
    /// vm.define_global("factorial", primitive!(1, factorial)).unwrap();
    ///
    /// let result = Compiler::new()
    ///     .run_expr::<i32>(&vm, "example", "factorial 5")
    ///     .unwrap_or_else(|err| panic!("{}", err));
    /// let expected = (120, Type::int());
    ///
    /// assert_eq!(result, expected);
    /// # }
    /// ```
    ///
    #[deprecated(
        since = "0.7.0",
        note = "Use `gluon::import::add_extern_module` instead"
    )]
    pub fn define_global<'vm, T>(&'vm self, name: &str, value: T) -> Result<()>
    where
        T: Pushable<'vm> + VmType,
    {
        // Value gets rooted by set_global
        unsafe {
            let value = value.marshal_unrooted(self)?;
            self.set_global(
                Symbol::from(format!("@{}", name)),
                T::make_forall_type(self),
                Metadata::default(),
                value,
            )
        }
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
    ///     .run_expr::<OpaqueValue<&Thread, Hole>>(&vm, "example",
    ///         r#" import! std.int "#)
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
        T: for<'value> Getable<'vm, 'value> + VmType,
    {
        use check::check_signature;

        let expected = T::make_type(self);

        let env = self.get_env();
        let (value, actual) = env.get_binding(name)?;

        // Finally check that type of the returned value is correct
        if check_signature(&*env, &expected, &actual) {
            Ok(T::from_value(self, value))
        } else {
            Err(Error::WrongType(expected, actual.into_owned()))
        }
    }

    pub fn get_global_type(&self, name: &str) -> Result<ArcType> {
        let env = self.get_env();
        let (_value, actual) = env.get_binding(name)?;
        Ok(actual.into_owned())
    }

    /// Retrieves type information about the type `name`. Types inside records can be accessed
    /// using dot notation (std.prelude.Option)
    pub fn find_type_info(&self, name: &str) -> Result<types::Alias<Symbol, ArcType>> {
        let env = self.get_env();
        env.find_type_info(name).map(|alias| alias.into_owned())
    }

    /// Returns the gluon type that was bound to `T`
    pub fn get_type<T: ?Sized + Any>(&self) -> Option<ArcType> {
        self.global_env().get_type::<T>()
    }

    /// Registers the type `T` as being a gluon type called `name` with generic arguments `args`
    pub fn register_type<T: ?Sized + Any>(&self, name: &str, args: &[&str]) -> Result<ArcType> {
        self.global_env().register_type::<T>(name, args)
    }
    pub fn register_type_as(
        &self,
        name: Symbol,
        alias: Alias<Symbol, ArcType>,
        id: TypeId,
    ) -> Result<ArcType> {
        self.global_env().register_type_as(name, alias, id)
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
        let mut context = self.owned_context();
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
        v.push(&mut context)
    }

    /// Removes the top value from the stack
    pub fn pop(&self) {
        self.owned_context().stack.pop();
    }

    pub fn allocated_memory(&self) -> usize {
        self.owned_context().gc.allocated_memory()
    }

    pub fn set_memory_limit(&self, memory_limit: usize) {
        self.owned_context().gc.set_memory_limit(memory_limit)
    }

    pub fn interrupt(&self) {
        self.interrupt.store(true, atomic::Ordering::Relaxed)
    }

    pub fn interrupted(&self) -> bool {
        self.interrupt.load(atomic::Ordering::Relaxed)
    }

    #[doc(hidden)]
    pub fn global_env(&self) -> &Arc<GlobalVmState> {
        &self.global_state
    }

    pub fn current_context(&self) -> ActiveThread {
        ActiveThread {
            thread: self,
            context: Some(self.context().context),
        }
    }

    fn owned_context(&self) -> OwnedContext {
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
    fn root_value_with_self(self, value: Variants) -> RootedValue<Self> {
        let value = value.get_value();
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
pub trait ThreadInternal: Sized
where
    Self: ::std::borrow::Borrow<Thread>,
{
    /// Locks and retrives this threads stack
    fn context(&self) -> OwnedContext;

    /// Roots a value
    fn root_value<'vm, T>(&'vm self, value: Variants) -> RootedValue<T>
    where
        T: VmRoot<'vm>;

    /// Evaluates a zero argument function (a thunk)
    fn call_thunk<'vm>(
        &'vm self,
        closure: GcPtr<ClosureData>,
    ) -> FutureValue<Execute<RootedThread>>;

    fn call_thunk_top<'vm>(
        &'vm self,
        closure: GcPtr<ClosureData>,
    ) -> BoxFuture<'static, RootedValue<RootedThread>, Error>
    where
        Self: Send + Sync,
    {
        let self_ = RootedThread::root(self.borrow());
        let level = self_.context().stack.get_frames().len();

        Box::new(self.call_thunk(closure).or_else(move |mut err| {
            let mut context = self_.context();
            let stack = StackFrame::<State>::current(&mut context.stack);
            let new_trace = reset_stack(stack, level)?;
            if let Error::Panic(_, ref mut trace) = err {
                *trace = Some(new_trace);
            }
            Err(err)
        }))
    }

    /// Executes an `IO` action
    fn execute_io<'vm>(&'vm self, value: Variants) -> FutureValue<Execute<RootedThread>>;

    fn execute_io_top<'vm>(
        &'vm self,
        value: Variants,
    ) -> BoxFuture<'static, RootedValue<RootedThread>, Error>
    where
        Self: Send + Sync,
    {
        let self_ = RootedThread::root(self.borrow());
        let level = self_.context().stack.get_frames().len();
        Box::new(self.execute_io(value).or_else(move |mut err| {
            let mut context = self_.context();
            let stack = StackFrame::<State>::current(&mut context.stack);
            let new_trace = reset_stack(stack, level)?;
            if let Error::Panic(_, ref mut trace) = err {
                *trace = Some(new_trace);
            }
            Err(err)
        }))
    }

    /// Calls a function on the stack.
    /// When this function is called it is expected that the function exists at
    /// `stack.len() - args - 1` and that the arguments are of the correct type
    fn call_function<'b>(
        &'b self,
        stack: OwnedContext<'b>,
        args: VmIndex,
    ) -> Result<Async<Option<OwnedContext<'b>>>>;

    fn resume(&self) -> Result<Async<OwnedContext>>;

    fn set_global(
        &self,
        name: Symbol,
        typ: ArcType,
        metadata: Metadata,
        value: Value,
    ) -> Result<()>;

    /// `owner` is theread that owns `value` which is not necessarily the same as `self`
    fn deep_clone_value(&self, owner: &Thread, value: Variants) -> Result<Value>;

    fn can_share_values_with(&self, gc: &mut Gc, other: &Thread) -> bool;
}

impl ThreadInternal for Thread {
    fn context(&self) -> OwnedContext {
        OwnedContext {
            thread: self,
            context: self.context.lock().unwrap(),
        }
    }

    /// Roots a value
    fn root_value<'vm, T>(&'vm self, value: Variants) -> RootedValue<T>
    where
        T: VmRoot<'vm>,
    {
        let value = value.get_value();
        self.rooted_values.write().unwrap().push(value.clone());
        RootedValue {
            vm: T::root(self),
            value: value,
        }
    }

    fn call_thunk<'vm>(
        &'vm self,
        closure: GcPtr<ClosureData>,
    ) -> FutureValue<Execute<RootedThread>> {
        let mut context = self.owned_context();
        context.stack.push(Closure(closure));
        StackFrame::<State>::current(&mut context.stack).enter_scope(
            0,
            ClosureState {
                closure,
                instruction_index: 0,
            },
        );
        match try_future!(context.execute(false), Either::A) {
            Async::Ready(context) => {
                let mut context = context.unwrap();
                let value = self.root_value(context.stack.last().unwrap());
                context.stack.pop();
                Either::A(future::ok(value))
            }
            Async::NotReady => Either::B(Execute::new(self.root_thread())),
        }
    }

    /// Calls a module, allowed to to run IO expressions
    fn execute_io<'vm>(&'vm self, value: Variants) -> FutureValue<Execute<RootedThread>> {
        debug!("Run IO {:?}", value);
        let mut context = self.context();
        // Dummy value to fill the place of the function for TailCall
        context.stack.push(Int(0));

        context.stack.push(value);
        context.stack.push(Int(0));

        context.borrow_mut().enter_scope(2, State::Unknown);
        context = match try_future!(self.call_function(context, 1), Either::A) {
            Async::Ready(context) => context.expect("call_module to have the stack remaining"),
            Async::NotReady => return Either::B(Execute::new(self.root_thread())),
        };
        let result = self.root_value(context.stack.last().unwrap());
        context.stack.pop();
        {
            let mut context = context.borrow_mut();
            while context.stack.len() > 0 {
                context.stack.pop();
            }
        }
        let _ = context.exit_scope();
        Either::A(future::ok(result))
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
        let mut context = self.owned_context();
        if context.stack.get_frames().len() == 1 {
            // Only the top level frame left means that the thread has finished
            return Err(Error::Dead);
        }
        context = try_ready!(context.execute(true)).unwrap();
        Ok(Async::Ready(context))
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

    fn deep_clone_value(&self, owner: &Thread, value: Variants) -> Result<Value> {
        let mut context = self.owned_context();
        let full_clone = !self.can_share_values_with(&mut context.gc, owner);
        let mut cloner = ::value::Cloner::new(self, &mut context.gc);
        if full_clone {
            cloner.force_full_clone();
        }
        cloner.deep_clone(&value.get_value())
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
    fn instruction_index(&self, instruction_index: usize) -> usize {
        if self.info.stack.get_frames().len() - 1 == self.index {
            instruction_index
        } else {
            instruction_index - 1
        }
    }

    /// Returns the line which create the current instruction of this frame
    pub fn line(&self) -> Option<Line> {
        let frame = self.frame();
        match frame.state {
            State::Closure(ClosureState {
                ref closure,
                instruction_index,
            }) => closure
                .function
                .debug_info
                .source_map
                .line(self.instruction_index(instruction_index)),
            _ => None,
        }
    }

    /// Returns the name of the source which defined the funtion executing at this frame
    pub fn source_name(&self) -> &str {
        match self.frame().state {
            State::Closure(ClosureState { ref closure, .. }) => {
                &closure.function.debug_info.source_name
            }
            _ => "<unknown>",
        }
    }

    /// Returns the name of the function executing at this frame
    pub fn function_name(&self) -> Option<&str> {
        match self.frame().state {
            State::Unknown | State::Lock => None,
            State::Closure(ClosureState { ref closure, .. }) => {
                Some(closure.function.name.declared_name())
            }
            State::Extern(ref function) => Some(function.function.id.declared_name()),
        }
    }

    /// Returns an iterator over all locals available at the current executing instruction
    pub fn locals(&self) -> LocalIter {
        let frame = self.frame();
        match frame.state {
            State::Closure(ClosureState {
                ref closure,
                instruction_index,
            }) => closure
                .function
                .debug_info
                .local_map
                .locals(self.instruction_index(instruction_index)),
            _ => LocalIter::empty(),
        }
    }

    /// Returns a slice with information about the values bound to this closure
    pub fn upvars(&self) -> &[UpvarInfo] {
        match self.frame().state {
            State::Closure(ClosureState { ref closure, .. }) => &closure.function.debug_info.upvars,
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

#[cfg_attr(
    feature = "serde_derive",
    derive(DeserializeState, SerializeState)
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(deserialize_state = "::serialization::DeSeed")
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(serialize_state = "::serialization::SeSeed")
)]
pub struct Context {
    // FIXME It is dangerous to write to gc and stack
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub(crate) stack: Stack,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub(crate) gc: Gc,
    #[cfg_attr(feature = "serde_derive", serde(skip))]
    hook: Hook,
    max_stack_size: VmIndex,

    /// Stack of polling functions used for extern functions returning futures
    #[cfg_attr(feature = "serde_derive", serde(skip))]
    poll_fns: Vec<(
        Option<Lock>,
        Box<for<'vm> FnMut(&'vm Thread) -> Result<Async<OwnedContext<'vm>>> + Send>,
    )>,
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

    pub(crate) fn new_data(
        &mut self,
        thread: &Thread,
        tag: VmTag,
        fields: &[Value],
    ) -> Result<Value> {
        self.alloc_with(
            thread,
            Def {
                tag: tag,
                elems: fields,
            },
        ).map(ValueRepr::Data)
        .map(Value::from)
    }

    pub fn push_new_data(
        &mut self,
        thread: &Thread,
        tag: VmTag,
        fields: usize,
    ) -> Result<Variants> {
        let value = {
            let fields = &self.stack[self.stack.len() - fields as VmIndex..];
            alloc(
                &mut self.gc,
                thread,
                &self.stack,
                Def {
                    tag: tag,
                    elems: fields,
                },
            ).map(ValueRepr::Data)
            .map(Value::from)?
        };
        self.stack.push(value);
        Ok(self.stack.last().unwrap())
    }

    pub fn push_new_record(
        &mut self,
        thread: &Thread,
        fields: usize,
        field_names: &[InternedStr],
    ) -> Result<Variants> {
        let value = {
            let fields = &self.stack[self.stack.len() - fields as VmIndex..];
            Data(alloc(
                &mut self.gc,
                thread,
                &self.stack,
                RecordDef {
                    elems: fields,
                    fields: field_names,
                },
            )?)
        };
        self.stack.push(value);
        Ok(self.stack.last().unwrap())
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

    pub fn stacktrace(&self, frame_level: usize) -> ::stack::Stacktrace {
        self.stack.stacktrace(frame_level)
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
                let result = {
                    let context =
                        mem::transmute::<&mut ActiveThread, &mut ActiveThread<'vm>>(&mut context);
                    value.push(context)
                };
                result.map(|()| Async::Ready(context.into_owned()))
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

    pub fn frame_level(&self) -> usize {
        self.stack.get_frames().len()
    }

    pub fn stack_frame<T>(&mut self) -> StackFrame<T>
    where
        T: StackState,
    {
        StackFrame::current(&mut self.stack)
    }
}

pub(crate) fn alloc<D>(
    gc: &mut Gc,
    thread: &Thread,
    stack: &Stack,
    def: D,
) -> Result<GcPtr<D::Value>>
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

impl<'b> OwnedContext<'b> {
    fn exit_scope(mut self) -> StdResult<OwnedContext<'b>, ()> {
        let exists = StackFrame::<State>::current(&mut self.stack)
            .exit_scope()
            .is_ok();
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
            let state = StackFrame::<State>::current(&mut context.stack).frame.state;

            if context.hook.flags.contains(HookFlags::CALL_FLAG) {
                match state {
                    State::Extern(ExternState {
                        call_state: ExternCallState::Start,
                        ..
                    })
                    | State::Closure(ClosureState {
                        instruction_index: 0,
                        ..
                    }) => {
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
                State::Extern(ext) => {
                    // We are currently in the poll call of this extern function.
                    // Return control to the caller.
                    if ext.call_state == ExternCallState::InPoll {
                        return Ok(Async::Ready(Some(context)));
                    }
                    StackFrame::<ExternState>::current(&mut context.stack)
                        .frame
                        .state
                        .call_state = ExternCallState::Poll;
                    Some(try_ready!(context.execute_function(
                        ext.call_state,
                        &ext.function,
                        polled,
                    )))
                }
                State::Closure(ClosureState {
                    closure,
                    instruction_index,
                }) => {
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

                            let new_context = try_ready!(context.from_state().execute_(
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
        call_state: ExternCallState,
        function: &ExternFunction,
        polled: bool,
    ) -> Result<Async<OwnedContext<'b>>> {
        info!(
            "CALL EXTERN {} {:?}",
            function.id,
            &self.stack.current_frame::<ExternState>()[..],
        );

        let mut status = Status::Ok;
        match call_state {
            ExternCallState::Start => {
                // Make sure that the stack is not borrowed during the external function call
                // Necessary since we do not know what will happen during the function call
                let thread = self.thread;
                drop(self);
                status = (function.function)(thread);

                if status == Status::Yield {
                    return Ok(Async::NotReady);
                }

                self = thread.owned_context();

                if status == Status::Error {
                    return match self.stack.pop().get_repr() {
                        String(s) => {
                            Err(Error::Panic(s.to_string(), Some(self.stack.stacktrace(0))))
                        }
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

            ExternCallState::Poll => {
                while let Some((lock, mut poll_fn)) = self.poll_fns.pop() {
                    // We can only poll the future if the code is currently executing in a future
                    if !polled {
                        self.poll_fns.push((lock, poll_fn));
                        return Ok(Async::NotReady);
                    }

                    let frame_offset = self.stack.get_frames().len() - 1;
                    if self.poll_fns.is_empty() {
                        match self.stack.get_frames_mut()[frame_offset].state {
                            State::Extern(ref mut e) => e.call_state = ExternCallState::InPoll,
                            _ => unreachable!(),
                        }
                    }
                    let thread = self.thread;
                    drop(self);
                    // Poll the future that was returned from the initial call to this extern function
                    match poll_fn(thread) {
                        Ok(Async::Ready(context)) => {
                            self = context;
                            if let Some(lock) = lock {
                                self.stack.release_lock(lock);
                            }
                            StackFrame::<ExternState>::current(&mut self.stack)
                                .frame
                                .state
                                .call_state = ExternCallState::Poll;
                            return Ok(Async::Ready(self));
                        }
                        Ok(Async::NotReady) => {
                            self = thread.owned_context();
                            match self.stack.get_frames_mut()[frame_offset].state {
                                State::Extern(ref mut e) => e.call_state = ExternCallState::Poll,
                                _ => unreachable!(),
                            }
                            // Restore `poll_fn` so it can be polled again
                            self.poll_fns.push((lock, poll_fn));
                            return Ok(Async::NotReady);
                        }
                        Err(err) => {
                            self = thread.owned_context();
                            if let Some(lock) = lock {
                                self.stack.release_lock(lock);
                            }
                            return Err(err);
                        }
                    }
                }
            }
            // Handled outside of this function
            ExternCallState::InPoll => unreachable!(),
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
            debug_assert!(
                match stack.frame.state {
                    State::Extern(ref e) => e.function.id == function.id,
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
            &self.stack.current_frame::<State>()[..]
        );

        match status {
            Status::Ok => Ok(Async::Ready(self)),
            Status::Yield => Ok(Async::NotReady),
            Status::Error => match self.stack.pop().get_repr() {
                String(s) => Err(Error::Panic(s.to_string(), Some(self.stack.stacktrace(0)))),
                _ => Err(Error::Message(format!(
                    "Unexpected error calling function `{}`",
                    function.id
                ))),
            },
        }
    }

    fn borrow_mut(&mut self) -> ExecuteContext<State> {
        let context = &mut **self;
        ExecuteContext {
            thread: self.thread,
            gc: &mut context.gc,
            stack: StackFrame::current(&mut context.stack),
            hook: &mut context.hook,
        }
    }
}

struct ExecuteContext<'b, S: StackState = ClosureState> {
    thread: &'b Thread,
    stack: StackFrame<'b, S>,
    gc: &'b mut Gc,
    hook: &'b mut Hook,
}

impl<'b> ExecuteContext<'b> {
    fn execute_(
        mut self,
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
                        self.stack.frame.state.instruction_index = index;
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
                    self.stack.frame.state.instruction_index = index + 1;
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
                        self.stack.frame.state.closure.function.name == function.name,
                        "Attempted to pop {:?} but `{}` was expected",
                        self.stack.frame.state,
                        function.name
                    );
                    let mut context = self.exit_scope().unwrap_or_else(|x| x);
                    info!(
                        "Clearing {} {} {:?}",
                        context.stack.len(),
                        amount,
                        &context.stack[..]
                    );
                    let end = context.stack.len() - args - 1;
                    context.stack.remove_range(end - amount, end);
                    debug!("{:?}", &context.stack[..]);
                    return context.do_call(args).map(|x| Async::Ready(Some(x)));
                }
                ConstructVariant { tag, args } => {
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
                NewVariant { tag, args } => {
                    let d = {
                        if args == 0 {
                            ValueRepr::Tag(tag)
                        } else {
                            Data(alloc(
                                &mut self.gc,
                                self.thread,
                                &self.stack.stack,
                                UninitializedVariantDef {
                                    tag: tag,
                                    elems: args as usize,
                                },
                            )?)
                        }
                    };
                    self.stack.push(d);
                }
                NewRecord { record, args } => {
                    let d = {
                        if args == 0 {
                            ValueRepr::Tag(0)
                        } else {
                            unsafe {
                                let roots = Roots {
                                    vm: GcPtr::from_raw(self.thread),
                                    stack: &self.stack.stack,
                                };
                                let field_names = &function.records[record as usize];
                                Data(self.gc.alloc_and_collect(
                                    roots,
                                    UninitializedRecord {
                                        elems: args as usize,
                                        fields: field_names,
                                    },
                                )?)
                            }
                        }
                    };
                    self.stack.push(d);
                }
                CloseData { index } => {
                    match self.stack[index].get_repr() {
                        Data(mut data) => {
                            // Unique access is safe as the record is only reachable from this
                            // thread and none of those places will use it until after we have
                            // closed it
                            unsafe {
                                for var in data.as_mut().fields.iter_mut().rev() {
                                    *var = self.stack.pop();
                                }
                            }
                        }
                        x => ice!("Expected closure, got {:?}", x),
                    }
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
                            let v = data.get_field(field).unwrap_or_else(|| {
                                error!("{}", self.stack.stack.stacktrace(0));
                                ice!("Field `{}` does not exist", field)
                            });
                            self.stack.push(v);
                        }
                        x => {
                            return Err(Error::Message(format!("GetField on {:?}", x)));
                        }
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
            self.stack.frame.state.closure.function.name == function.name,
            "Attempted to pop {:?} but `{}` was expected",
            self.stack.frame.state,
            function.name
        );
        let (stack_exists, mut context) = {
            let r = self.exit_scope();
            (
                r.is_ok(),
                match r {
                    Ok(context) => context,
                    Err(context) => context,
                },
            )
        };

        context.stack.pop_many(len + 1);
        if frame_has_excess {
            // If the function that just finished had extra arguments we need to call the result of
            // the call with the extra arguments
            match context.stack.pop().get_repr() {
                Data(excess) => {
                    debug!("Push excess args {:?}", &excess.fields);
                    context.stack.push(result);
                    for value in &excess.fields {
                        context.stack.push(value);
                    }
                    context
                        .do_call(excess.fields.len() as VmIndex)
                        .map(|x| Async::Ready(Some(x)))
                }
                x => ice!("Expected excess arguments found {:?}", x),
            }
        } else {
            context.stack.push(result);
            Ok(Async::Ready(if stack_exists { Some(()) } else { None }))
        }
    }
}
impl<'b> ExecuteContext<'b, State> {
    fn from_state<T>(self) -> ExecuteContext<'b, T>
    where
        T: StackState,
    {
        ExecuteContext {
            thread: self.thread,
            stack: self.stack.from_state(),
            gc: self.gc,
            hook: self.hook,
        }
    }
}

impl<'b, S> ExecuteContext<'b, S>
where
    S: StackState,
{
    fn enter_scope<T>(self, args: VmIndex, state: T) -> ExecuteContext<'b, T>
    where
        T: StackState,
    {
        let stack = self.stack.enter_scope(args, state);
        self.hook.previous_instruction_index = usize::max_value();
        ExecuteContext {
            thread: self.thread,
            stack,
            gc: self.gc,
            hook: self.hook,
        }
    }

    fn exit_scope(self) -> StdResult<ExecuteContext<'b, State>, ExecuteContext<'b, State>> {
        match self.stack.exit_scope() {
            Ok(stack) => {
                if self.hook.flags.bits() != 0 {
                    // Subtract 1 to compensate for the `Call` instruction adding one earlier
                    // ensuring that the line hook runs after function calls
                    if let State::Closure(ref state) = stack.frame.state {
                        self.hook.previous_instruction_index =
                            state.instruction_index.saturating_sub(1);
                    }
                }
                Ok(ExecuteContext {
                    thread: self.thread,
                    stack,
                    gc: self.gc,
                    hook: self.hook,
                })
            }
            Err(stack) => Err(ExecuteContext {
                thread: self.thread,
                stack: StackFrame::current(stack),
                gc: self.gc,
                hook: self.hook,
            }),
        }
    }

    fn execute_callable(self, function: &Callable, excess: bool) -> Result<()> {
        match *function {
            Callable::Closure(closure) => {
                let mut next = self.enter_scope(
                    closure.function.args,
                    ClosureState {
                        closure,
                        instruction_index: 0,
                    },
                );
                next.stack.frame.excess = excess;
                Ok(())
            }
            Callable::Extern(ref ext) => {
                assert!(self.stack.len() >= ext.args + 1);
                let function_index = self.stack.len() - ext.args - 1;
                debug!("------- {} {:?}", function_index, &self.stack[..]);
                self.enter_scope(ext.args, ExternState::new(*ext));
                Ok(())
            }
        }
    }

    fn call_function_with_upvars(
        mut self,
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
                self.stack.pop_many(args + 1);
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
                self.stack.pop_many(excess_args);
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

    fn do_call(mut self, args: VmIndex) -> Result<()> {
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
}

#[inline]
fn binop_int<'b, 'c, F, T>(vm: &'b Thread, stack: &'b mut StackFrame<'c, ClosureState>, f: F)
where
    F: FnOnce(T, T) -> VmInt,
    T: for<'d, 'e> Getable<'d, 'e> + fmt::Debug,
{
    binop(vm, stack, |l, r| ValueRepr::Int(f(l, r)))
}

#[inline]
fn binop_f64<'b, 'c, F, T>(vm: &'b Thread, stack: &'b mut StackFrame<'c, ClosureState>, f: F)
where
    F: FnOnce(T, T) -> f64,
    T: for<'d, 'e> Getable<'d, 'e> + fmt::Debug,
{
    binop(vm, stack, |l, r| ValueRepr::Float(f(l, r)))
}

#[inline]
fn binop_byte<'b, 'c, F, T>(vm: &'b Thread, stack: &'b mut StackFrame<'c, ClosureState>, f: F)
where
    F: FnOnce(T, T) -> u8,
    T: for<'d, 'e> Getable<'d, 'e> + fmt::Debug,
{
    binop(vm, stack, |l, r| ValueRepr::Byte(f(l, r)))
}

#[inline]
fn binop_bool<'b, 'c, F, T>(vm: &'b Thread, stack: &'b mut StackFrame<'c, ClosureState>, f: F)
where
    F: FnOnce(T, T) -> bool,
    T: for<'d, 'e> Getable<'d, 'e> + fmt::Debug,
{
    binop(vm, stack, |l, r| {
        ValueRepr::Tag(if f(l, r) { 1 } else { 0 })
    })
}

#[inline]
fn binop<'b, 'c, F, T>(vm: &'b Thread, stack: &'b mut StackFrame<'c, ClosureState>, f: F)
where
    F: FnOnce(T, T) -> ValueRepr,
    T: for<'d, 'e> Getable<'d, 'e> + fmt::Debug,
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

fn debug_instruction(stack: &StackFrame<ClosureState>, index: usize, instr: Instruction) {
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
            PushUpVar(i) => Some(stack.get_upvar(i).clone()),
            NewClosure { .. } | MakeClosure { .. } => Some(Value::from(Int(stack.len() as isize))),
            _ => None,
        }
    );
}

pub struct ActiveThread<'vm> {
    thread: &'vm Thread,
    context: Option<MutexGuard<'vm, Context>>,
}

pub struct PopValue<'a, 'vm: 'a>(&'a mut ActiveThread<'vm>, Variants<'a>);

impl<'a, 'vm> Drop for PopValue<'a, 'vm> {
    fn drop(&mut self) {
        self.0.stack().pop();
    }
}

impl<'a, 'vm> Deref for PopValue<'a, 'vm> {
    type Target = Variants<'a>;
    fn deref(&self) -> &Self::Target {
        &self.1
    }
}

impl<'vm> ActiveThread<'vm> {
    pub fn drop(&mut self) {
        self.context = None;
    }

    pub fn restore(&mut self) {
        *self = self.thread.current_context();
    }

    pub fn thread(&self) -> &'vm Thread {
        self.thread
    }

    pub fn push<'a, T>(&mut self, v: T)
    where
        T: ::stack::StackPrimitive,
    {
        self.context.as_mut().unwrap().stack.push(v);
    }

    pub(crate) fn into_owned(self) -> OwnedContext<'vm> {
        OwnedContext {
            thread: self.thread,
            context: self.context.expect("context"),
        }
    }

    pub fn pop<'a>(&'a mut self) -> PopValue<'a, 'vm> {
        let value = {
            let stack = &self.context.as_ref().unwrap().stack;
            let last = stack.len() - 1;
            stack.get_variant(last).unwrap().get_value()
        };
        PopValue(self, Variants(value.get_repr(), ::std::marker::PhantomData))
    }

    // For gluon_codegen
    #[doc(hidden)]
    pub fn context(&mut self) -> &mut Context {
        self.context.as_mut().unwrap()
    }

    // For gluon_codegen
    #[doc(hidden)]
    pub(crate) fn stack(&mut self) -> &mut Stack {
        &mut self.context.as_mut().unwrap().stack
    }

    pub(crate) fn gc(&mut self) -> &mut Gc {
        &mut self.context.as_mut().unwrap().gc
    }
}
#[doc(hidden)]
pub fn reset_stack(mut stack: StackFrame<State>, level: usize) -> Result<::stack::Stacktrace> {
    let frame_level = stack
        .stack
        .get_frames()
        .iter()
        .rposition(|frame| frame.state == State::Lock)
        .unwrap_or(0);

    let trace = stack.stack.stacktrace(frame_level);
    while stack.stack.get_frames().len() > level {
        stack = match stack.exit_scope() {
            Ok(s) => s,
            Err(_) => return Err(format!("Attempted to exit scope above current").into()),
        };
    }
    Ok(trace)
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
