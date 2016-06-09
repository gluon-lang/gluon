use std::any::Any;
use std::sync::{Mutex, RwLock, RwLockWriteGuard, MutexGuard};
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Sub, Mul, Div, Deref};
use std::string::String as StdString;
use std::result::Result as StdResult;
use std::sync::Arc;

use base::metadata::Metadata;
use base::symbol::Symbol;
use base::types::TcType;
use base::types;

use Variants;
use api::{Getable, Pushable, VMType};
use array::Str;
use compiler::CompiledFunction;
use gc::{DataDef, Gc, GcPtr, Move, Traverseable};
use stack::{Stack, StackFrame, State};
use types::*;
use vm::{Error, Result, GlobalVMState, Value, VMInt, ClosureData, ClosureInitDef, ClosureDataDef,
         Def, ExternFunction, BytecodeFunction, Callable, PartialApplicationDataDef, Userdata};

use vm::Value::{Int, Float, String, Data, Function, PartialApplication, Closure};

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
    where T: Deref<Target = Thread>
{
    vm: T,
    value: Value,
}

impl<T> Drop for RootedValue<T>
    where T: Deref<Target = Thread>
{
    fn drop(&mut self) {
        // TODO not safe if the root changes order of being dropped with another root
        self.vm.rooted_values.write().unwrap().pop();
    }
}

impl<T> fmt::Debug for RootedValue<T>
    where T: Deref<Target = Thread>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.value)
    }
}

impl<T> Deref for RootedValue<T>
    where T: Deref<Target = Thread>
{
    type Target = Value;
    fn deref(&self) -> &Value {
        &self.value
    }
}

impl<T> RootedValue<T>
    where T: Deref<Target = Thread>
{
    pub fn vm(&self) -> &Thread {
        &self.vm
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
pub struct RootStr<'vm>(Root<'vm, Str>);

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

struct Context<'b> {
    thread: &'b Thread,
    stack: StackFrame<'b>,
    gc: MutexGuard<'b, Gc>,
}

impl<'b> Context<'b> {
    fn enter_scope(self, args: VMIndex, state: State) -> Context<'b> {
        Context {
            thread: self.thread,
            gc: self.gc,
            stack: self.stack.enter_scope(args, state),
        }
    }

    fn exit_scope(self) -> Option<Context<'b>> {
        let Context { thread, stack, gc } = self;
        stack.exit_scope()
             .map(move |stack| {
                 Context {
                     thread: thread,
                     stack: stack,
                     gc: gc,
                 }
             })
    }
}
fn alloc<D>(gc: &mut Gc, thread: &Thread, stack: &Stack, def: D) -> GcPtr<D::Value>
    where D: DataDef + Traverseable,
          D::Value: Sized + Any
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

// All threads MUST be allocated in the garbage collected heap. This is necessary as a thread
// calling collect need to mark itself if it is on the garbage collected heap and it has no way of
// knowing wheter it is or not. So the only way of allowing it to mark itself is to disallow it to
// be allocated anywhere else.
/// Representation of the virtual machine
pub struct Thread {
    global_state: Arc<GlobalVMState>,
    // The parent of this thread, if it exists must live at least as long as this thread as this
    // thread can refer to any value in the parent thread
    parent: Option<RootedThread>,
    local_gc: Mutex<Gc>,
    roots: RwLock<Vec<GcPtr<Traverseable + Send + Sync>>>,
    rooted_values: RwLock<Vec<Value>>,
    /// All threads which this thread have spawned in turn. Necessary as this thread needs to scan
    /// the roots of all its children as well since those may contain references to this threads
    /// garbage collected values
    child_threads: RwLock<Vec<GcPtr<Thread>>>,
    stack: Mutex<Stack>,
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
        self.stack.lock().unwrap().get_values().traverse(gc);
        self.child_threads.read().unwrap().traverse(gc);
    }
}

impl PartialEq for Thread {
    fn eq(&self, other: &Thread) -> bool {
        self as *const _ == other as *const _
    }
}

impl VMType for RootedThread {
    type Type = Self;
}

impl<'vm> Pushable<'vm> for RootedThread {
    fn push(self, _vm: &'vm Thread, stack: &mut Stack) -> Status {
        stack.push(Value::Thread(self.0));
        Status::Ok
    }
}


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
            let mut gc_ref = self.0.gc.lock().unwrap();
            let gc_to_drop = ::std::mem::replace(&mut *gc_ref, Gc::new(0));
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
        RootedThread::from_gc_ptr(self.0)
    }
}

impl Traverseable for RootedThread {
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc);
    }
}

impl RootedThread {
    pub fn new() -> RootedThread {
        let thread = Thread {
            global_state: Arc::new(GlobalVMState::new()),
            parent: None,
            local_gc: Mutex::new(Gc::new(1)),
            stack: Mutex::new(Stack::new()),
            roots: RwLock::new(Vec::new()),
            rooted_values: RwLock::new(Vec::new()),
            child_threads: RwLock::new(Vec::new()),
        };
        let mut gc = Gc::new(0);
        let vm = RootedThread::from_gc_ptr(gc.alloc(Move(thread)));
        *vm.gc.lock().unwrap() = gc;
        // Enter the top level scope
        StackFrame::frame(vm.stack.lock().unwrap(), 0, State::Unknown);
        vm
    }

    pub fn from_gc_ptr(p: GcPtr<Thread>) -> RootedThread {
        let vm = RootedThread(p);
        vm.parent_threads().push(vm.0);
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

    pub fn new_thread(&self) -> RootedThread {
        let vm = Thread {
            global_state: self.global_state.clone(),
            parent: unsafe { Some(RootedThread::from_gc_ptr(GcPtr::from_raw(self))) },
            local_gc: Mutex::new(self.local_gc.lock().unwrap().new_child_gc()),
            stack: Mutex::new(Stack::new()),
            roots: RwLock::new(Vec::new()),
            rooted_values: RwLock::new(Vec::new()),
            child_threads: RwLock::new(Vec::new()),
        };
        // Enter the top level scope
        StackFrame::frame(vm.stack.lock().unwrap(), 0, State::Unknown);
        RootedThread::from_gc_ptr(self.alloc(&self.stack.lock().unwrap(), Move(vm)))
    }

    /// Creates a new global value at `name`.
    /// Fails if a global called `name` already exists.
    pub fn define_global<'vm, T>(&'vm self, name: &str, value: T) -> Result<()>
        where T: Pushable<'vm>
    {
        let (status, value) = {
            let mut stack = self.get_stack();
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
        let env = self.get_env();
        let (value, actual) = try!(env.get_binding(name));
        // Finally check that type of the returned value is correct
        let expected = T::make_type(self);
        if expected == *actual {
            T::from_value(self, Variants(&value))
                .ok_or_else(|| Error::UndefinedBinding(name.into()))
        } else {
            Err(Error::WrongType(expected, actual.into_owned()))
        }
    }

    pub fn find_type_info(&self, name: &str) -> Result<types::Alias<Symbol, TcType>> {
        let env = self.get_env();
        env.find_type_info(name)
           .map(|alias| alias.into_owned())
    }

    /// Returns the current stackframe
    pub fn release_lock<'vm>(&'vm self, lock: ::stack::Lock) -> StackFrame<'vm> {
        self.stack.lock().unwrap().release_lock(lock);
        StackFrame::current(self.get_stack())
    }

    /// Returns the current stackframe
    pub fn get_stack(&self) -> MutexGuard<Stack> {
        self.stack.lock().unwrap()
    }

    pub fn current_frame(&self) -> StackFrame {
        StackFrame::current(self.get_stack())
    }

    fn current_context(&self) -> Context {
        Context {
            thread: self,
            gc: self.local_gc.lock().unwrap(),
            stack: StackFrame::current(self.stack.lock().unwrap()),
        }
    }

    /// Runs a garbage collection.
    pub fn collect(&self) {
        let stack = self.stack.lock().unwrap();
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
             self.roots.write().unwrap().push(v.as_traverseable());
             Root {
                 roots: &self.roots,
                 ptr: ptr,
             }
         })
    }

    /// Roots a string
    pub fn root_string<'vm>(&'vm self, ptr: GcPtr<Str>) -> RootStr<'vm> {
        self.roots.write().unwrap().push(ptr.as_traverseable());
        RootStr(Root {
            roots: &self.roots,
            ptr: &*ptr,
        })
    }

    /// Roots a value
    pub fn root_value(&self, value: Value) -> RootedValue<RootedThread> {
        self.rooted_values.write().unwrap().push(value);
        RootedValue {
            vm: unsafe { RootedThread::from_gc_ptr(GcPtr::from_raw(self)) },
            value: value,
        }
    }

    /// Roots a value
    pub fn root_value_ref(&self, value: Value) -> RootedValue<&Thread> {
        self.rooted_values.write().unwrap().push(value);
        RootedValue {
            vm: self,
            value: value,
        }
    }

    /// Allocates a new value from a given `DataDef`.
    /// Takes the stack as it may collect if the collection limit has been reached.
    pub fn alloc<D>(&self, stack: &Stack, def: D) -> GcPtr<D::Value>
        where D: DataDef + Traverseable,
              D::Value: Sized + Any
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
            vm: unsafe {
                // Threads must only be on the garbage collectors heap which makes this safe
                GcPtr::from_raw(self)
            },
            stack: stack,
        };
        let mut gc = self.local_gc.lock().unwrap();
        f(&mut gc, roots)
    }

    pub fn new_data(&self, tag: VMTag, fields: &[Value]) -> Value {
        Value::Data(self.local_gc.lock().unwrap().alloc(Def {
            tag: tag,
            elems: fields,
        }))
    }

    pub fn add_bytecode(&self,
                        name: &str,
                        typ: TcType,
                        args: VMIndex,
                        instructions: Vec<Instruction>) {
        let id = Symbol::new(name);
        let mut compiled_fn = CompiledFunction::new(args, id.clone(), typ.clone());
        compiled_fn.instructions = instructions;
        let f = self.new_function(compiled_fn);
        let closure = self.alloc(&self.stack.lock().unwrap(), ClosureDataDef(f, &[]));
        self.set_global(id, typ, Metadata::default(), Closure(closure)).unwrap();
    }

    /// Pushes a value to the top of the stack
    pub fn push(&self, v: Value) {
        self.stack.lock().unwrap().push(v)
    }

    /// Removes the top value from the stack
    pub fn pop(&self) -> Value {
        self.stack
            .lock()
            .unwrap()
            .pop()
    }

    ///Calls a module, allowed to to run IO expressions
    pub fn call_module(&self, typ: &TcType, closure: GcPtr<ClosureData>) -> Result<Value> {
        let value = try!(self.call_bytecode(closure));
        if let Some((id, _)) = typ.as_alias() {
            let is_io = {
                let env = self.get_env();
                env.find_type_info("IO")
                   .map(|alias| *id == alias.name)
                   .unwrap_or(false)
            };
            if is_io {
                debug!("Run IO {:?}", value);
                self.push(Int(0));// Dummy value to fill the place of the function for TailCall
                self.push(value);
                self.push(Int(0));
                let mut context = Context {
                    thread: self,
                    gc: self.local_gc.lock().unwrap(),
                    stack: StackFrame::frame(self.stack.lock().unwrap(), 2, State::Unknown),
                };
                context = try!(self.call_context(context, 1))
                              .expect("call_module to have the stack remaining");
                let result = context.stack.pop();
                while context.stack.len() > 0 {
                    context.stack.pop();
                }
                context.exit_scope();
                return Ok(result);
            }
        }
        Ok(value)
    }

    /// Calls a function on the stack.
    /// When this function is called it is expected that the function exists at
    /// `stack.len() - args - 1` and that the arguments are of the correct type
    pub fn call_function<'b>(&'b self,
                             stack: StackFrame<'b>,
                             args: VMIndex)
                             -> Result<Option<StackFrame<'b>>> {
        let context = Context {
            thread: self,
            gc: self.local_gc.lock().unwrap(),
            stack: stack,
        };
        self.call_context(context, args)
            .map(|context| context.map(|context| context.stack))
    }

    fn call_context<'b>(&'b self,
                        mut context: Context<'b>,
                        args: VMIndex)
                        -> Result<Option<Context<'b>>> {
        context = try!(context.do_call(args));
        context.execute()
    }

    pub fn resume(&self) -> Result<()> {
        let context = self.current_context();
        if context.stack.stack.get_frames().len() == 1 {
            // Only the top level frame left means that the thread has finished
            return Err(Error::Dead);
        }
        context.execute()
               .map(|_| ())
    }

    pub fn deep_clone(&self, value: Value) -> Result<Value> {
        let mut visited = HashMap::new();
        deep_clone(&value, &mut visited, &mut self.local_gc.lock().unwrap())
    }

    fn call_bytecode(&self, closure: GcPtr<ClosureData>) -> Result<Value> {
        self.push(Closure(closure));
        let context = Context {
            thread: self,
            gc: self.local_gc.lock().unwrap(),
            stack: StackFrame::frame(self.stack.lock().unwrap(), 0, State::Closure(closure)),
        };
        try!(context.execute());
        let mut stack = self.stack.lock().unwrap();
        Ok(stack.pop())
    }
}

impl<'b> Context<'b> {
    fn execute_callable(mut self, function: &Callable, excess: bool) -> Result<Context<'b>> {
        match *function {
            Callable::Closure(closure) => {
                self = self.enter_scope(closure.function.args, State::Closure(closure));
                self.stack.frame.excess = excess;
                Ok(self)
            }
            Callable::Extern(ref ext) => {
                assert!(self.stack.len() >= ext.args + 1);
                let function_index = self.stack.len() - ext.args - 1;
                debug!("------- {} {:?}", function_index, &self.stack[..]);
                Ok(self.enter_scope(ext.args, State::Extern(*ext)))
            }
        }
    }

    fn execute_function(mut self, function: &ExternFunction) -> Result<Context<'b>> {
        debug!("CALL EXTERN {}", function.id);
        // Make sure that the stack is not borrowed during the external function call
        // Necessary since we do not know what will happen during the function call
        let thread = self.thread;
        drop(self);
        let status = (function.function)(thread);
        self = thread.current_context();
        let result = self.stack.pop();
        while self.stack.len() > 0 {
            debug!("{} {:?}", self.stack.len(), &self.stack[..]);
            self.stack.pop();
        }
        self = try!(self.exit_scope()
                        .ok_or_else(|| {
                            Error::Message(StdString::from("Poped the last frame in \
                                                            execute_function"))
                        }));
        self.stack.pop();// Pop function
        self.stack.push(result);
        match status {
            Status::Ok => Ok(self),
            Status::Yield => Err(Error::Yield),
            Status::Error => {
                match self.stack.pop() {
                    String(s) => Err(Error::Message(s.to_string())),
                    _ => Err(Error::Message("Unexpected panic in VM".to_string())),
                }
            }
        }
    }

    fn call_function_with_upvars(mut self,
                                 args: VMIndex,
                                 required_args: VMIndex,
                                 callable: Callable)
                                 -> Result<Context<'b>> {
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
                    PartialApplication(alloc(&mut self.gc, self.thread, &self.stack.stack, def))
                };
                for _ in 0..(args + 1) {
                    self.stack.pop();
                }
                self.stack.push(app);
                Ok(self)
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
                          })
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

    fn do_call(mut self, args: VMIndex) -> Result<Context<'b>> {
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
                let total_args = app.arguments.len() as VMIndex + args;
                let offset = self.stack.len() - args;
                self.stack.insert_slice(offset, &app.arguments);
                self.call_function_with_upvars(total_args, app.function.args(), app.function)
            }
            x => return Err(Error::Message(format!("Cannot call {:?}", x))),
        }
    }

    fn execute(self) -> Result<Option<Context<'b>>> {
        let mut maybe_context = Some(self);
        while let Some(mut context) = maybe_context {
            debug!("STACK\n{:?}", context.stack.stack.get_frames());
            maybe_context = match context.stack.frame.state {
                State::Lock | State::Unknown => return Ok(Some(context)),
                State::Excess => context.exit_scope(),
                State::Extern(ext) => {
                    if context.stack.frame.instruction_index != 0 {
                        // This function was already called
                        return Ok(Some(context));
                    } else {
                        context.stack.frame.instruction_index = 1;
                        Some(try!(context.execute_function(&ext)))
                    }
                }
                State::Closure(closure) => {
                    // Tail calls into extern functions at the top level will drop the last
                    // stackframe so just return immedietly
                    if context.stack.stack.get_frames().len() == 0 {
                        return Ok(Some(context));
                    }
                    let instruction_index = context.stack.frame.instruction_index;
                    debug!("Continue with {}\nAt: {}/{}",
                           closure.function.name,
                           instruction_index,
                           closure.function.instructions.len());
                    let new_context = try!(context.execute_(instruction_index,
                                                            &closure.function.instructions,
                                                            &closure.function));
                    new_context
                }
            };
        }
        Ok(maybe_context)
    }

    fn execute_(mut self,
                mut index: usize,
                instructions: &[Instruction],
                function: &BytecodeFunction)
                -> Result<Option<Context<'b>>> {
        {
            debug!(">>>\nEnter frame {}: {:?}\n{:?}",
                   function.name,
                   &self.stack[..],
                   self.stack.frame);
        }
        while let Some(&instr) = instructions.get(index) {
            debug_instruction(&self.stack, index, instr, function);
            match instr {
                Push(i) => {
                    let v = self.stack[i].clone();
                    self.stack.push(v);
                }
                PushInt(i) => {
                    self.stack.push(Int(i));
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
                                args += excess.fields.len() as VMIndex;
                            }
                            None => panic!("Expected excess args"),
                        }
                    }
                    let thread = self.thread;
                    self = match self.exit_scope() {
                        Some(context) => context,
                        None => {
                            Context {
                                thread: thread,
                                gc: thread.local_gc.lock().unwrap(),
                                stack: StackFrame::frame(thread.stack.lock().unwrap(),
                                                         args + amount + 1,
                                                         State::Excess),
                            }
                        }
                    };
                    debug!("{} {} {:?}", self.stack.len(), amount, &self.stack[..]);
                    let end = self.stack.len() - args - 1;
                    self.stack.remove_range(end - amount, end);
                    debug!("{:?}", &self.stack[..]);
                    return self.do_call(args).map(Some);
                }
                Construct(tag, args) => {
                    let d = {
                        let fields = &self.stack[self.stack.len() - args..];
                        alloc(&mut self.gc,
                              self.thread,
                              &self.stack.stack,
                              Def {
                                  tag: tag,
                                  elems: fields,
                              })
                    };
                    for _ in 0..args {
                        self.stack.pop();
                    }
                    self.stack.push(Data(d));
                }
                GetField(i) => {
                    match self.stack.pop() {
                        Data(data) => {
                            let v = data.fields[i as usize];
                            self.stack.push(v);
                        }
                        x => return Err(Error::Message(format!("GetField on {:?}", x))),
                    }
                }
                TestTag(tag) => {
                    let data_tag = match self.stack.top() {
                        Data(ref data) => data.tag,
                        Int(tag) => tag as VMTag,
                        _ => {
                            return Err(Error::Message("Op TestTag called on non data type"
                                                          .to_string()))
                        }
                    };
                    self.stack.push(Int(if data_tag == tag {
                        1
                    } else {
                        0
                    }));
                }
                Split => {
                    match self.stack.pop() {
                        Data(data) => {
                            for field in &data.fields {
                                self.stack.push(*field);
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
                    match self.stack.pop() {
                        Int(0) => (),
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
                GetIndex => {
                    let index = self.stack.pop();
                    let array = self.stack.pop();
                    match (array, index) {
                        (Data(array), Int(index)) => {
                            let v = array.fields[index as usize];
                            self.stack.push(v);
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
                        let args = &self.stack[self.stack.len() - n..];
                        let func = function.inner_functions[fi as usize];
                        Closure(alloc(&mut self.gc,
                                      self.thread,
                                      &self.stack.stack,
                                      ClosureDataDef(func, args)))
                    };
                    for _ in 0..n {
                        self.stack.pop();
                    }
                    self.stack.push(closure);
                }
                NewClosure(fi, n) => {
                    let closure = {
                        // Use dummy variables until it is filled
                        let func = function.inner_functions[fi as usize];
                        Closure(alloc(&mut self.gc,
                                      self.thread,
                                      &self.stack.stack,
                                      ClosureInitDef(func, n as usize)))
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
                AddInt => binop(self.thread, &mut self.stack, VMInt::add),
                SubtractInt => binop(self.thread, &mut self.stack, VMInt::sub),
                MultiplyInt => binop(self.thread, &mut self.stack, VMInt::mul),
                DivideInt => binop(self.thread, &mut self.stack, VMInt::div),
                IntLT => binop(self.thread, &mut self.stack, |l: VMInt, r| l < r),
                IntEQ => binop(self.thread, &mut self.stack, |l: VMInt, r| l == r),
                AddFloat => binop(self.thread, &mut self.stack, f64::add),
                SubtractFloat => binop(self.thread, &mut self.stack, f64::sub),
                MultiplyFloat => binop(self.thread, &mut self.stack, f64::mul),
                DivideFloat => binop(self.thread, &mut self.stack, f64::div),
                FloatLT => binop(self.thread, &mut self.stack, |l: f64, r| l < r),
                FloatEQ => binop(self.thread, &mut self.stack, |l: f64, r| l == r),
            }
            index += 1;
        }
        let result = self.stack.top();
        debug!("Return {:?}", result);
        let len = self.stack.len();
        let frame_has_excess = self.stack.frame.excess;
        // We might not get access to the frame above the current as it could be locked
        let thread = self.thread;
        let stack_exists = self.exit_scope().is_some();
        let mut stack = thread.stack.lock().unwrap();
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
                    self = Context {
                        thread: thread,
                        gc: thread.local_gc.lock().unwrap(),
                        stack: StackFrame::frame(stack, 0, State::Excess),
                    };
                    debug!("Push excess args {:?}", &excess.fields);
                    self.stack.push(result);
                    for value in &excess.fields {
                        self.stack.push(*value);
                    }
                    self.do_call(excess.fields.len() as VMIndex).map(Some)
                }
                x => panic!("Expected excess arguments found {:?}", x),
            }
        } else {
            drop(stack);
            Ok(if stack_exists {
                Some(thread.current_context())
            } else {
                None
            })
        }
    }
}

#[inline]
fn binop<'b, F, T, R>(vm: &'b Thread, stack: &mut StackFrame<'b>, f: F)
    where F: FnOnce(T, T) -> R,
          T: Getable<'b> + fmt::Debug,
          R: Pushable<'b>
{
    let r = stack.pop();
    let l = stack.pop();
    match (T::from_value(vm, Variants(&l)), T::from_value(vm, Variants(&r))) {
        (Some(l), Some(r)) => {
            let result = f(l, r);
            result.push(vm, &mut stack.stack);
        }
        (l, r) => panic!("{:?} `op` {:?}", l, r),
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
               NewClosure(..) => Some(Int(stack.len() as isize)),
               MakeClosure(..) => Some(Int(stack.len() as isize)),
               _ => None,
           });
}

use std::collections::HashMap;
use std::collections::hash_map::Entry;

fn deep_clone_ptr<T, A>(value: GcPtr<T>,
                        visited: &mut HashMap<*const (), Value>,
                        alloc: A)
                        -> StdResult<Value, GcPtr<T>>
    where A: FnOnce(&T) -> (Value, GcPtr<T>)
{
    let key = &*value as *const T as *const ();
    let new_ptr = match visited.entry(key) {
        Entry::Occupied(entry) => return Ok(*entry.get()),
        Entry::Vacant(entry) => {
            // FIXME Should allocate the real `Value` and possibly fill it later
            let (value, new_ptr) = alloc(&value);
            entry.insert(value);
            new_ptr
        }
    };
    Err(new_ptr)
}

fn deep_clone(value: &Value,
              visited: &mut HashMap<*const (), Value>,
              gc: &mut Gc)
              -> Result<Value> {
    // Only need to clone values which belong to a younger generation than the gc that the new
    // value will live in
    if value.generation() <= gc.generation() {
        return Ok(*value);
    }
    match *value {
        String(data) => {
            Ok(deep_clone_ptr(data, visited, |data| {
                   let ptr = gc.alloc(&data[..]);
                   (String(ptr), ptr)
               })
                   .unwrap_or_else(String))
        }
        Value::Data(data) => {
            let result = deep_clone_ptr(data, visited, |data| {
                let ptr = gc.alloc(Def {
                    tag: data.tag,
                    elems: &data.fields,
                });
                (Value::Data(ptr), ptr)
            });
            match result {
                Ok(x) => Ok(x),
                Err(mut new_data) => {
                    {
                        let new_fields = unsafe { &mut new_data.as_mut().fields };
                        for (new, old) in new_fields.iter_mut().zip(&data.fields) {
                            *new = try!(deep_clone(old, visited, gc));
                        }
                    }
                    Ok(Value::Data(new_data))
                }
            }
        }
        Closure(data) => {
            // Closures may be mutually recursive with other closures so allocate it first and then
            // fill in the real values
            let result = deep_clone_ptr(data, visited, |data| {
                let ptr = gc.alloc(ClosureDataDef(data.function, &data.upvars));
                (Closure(ptr), ptr)
            });
            match result {
                Ok(x) => Ok(x),
                Err(mut new_data) => {
                    {
                        let new_upvars = unsafe { &mut new_data.as_mut().upvars };
                        for (new, old) in new_upvars.iter_mut().zip(&data.upvars) {
                            *new = try!(deep_clone(old, visited, gc));
                        }
                    }
                    Ok(Closure(new_data))
                }
            }
        }
        PartialApplication(data) => {
            let result = deep_clone_ptr(data, visited, |data| {
                let ptr = gc.alloc(PartialApplicationDataDef(data.function, &data.arguments));
                (PartialApplication(ptr), ptr)
            });
            match result {
                Ok(x) => Ok(x),
                Err(mut new_data) => {
                    {
                        let new_arguments = unsafe { &mut new_data.as_mut().arguments };
                        for (new, old) in new_arguments.iter_mut()
                                                       .zip(&data.arguments) {
                            *new = try!(deep_clone(old, visited, gc));
                        }
                    }
                    Ok(PartialApplication(new_data))
                }
            }
        }
        Function(_) |
        Value::Userdata(_) |
        Value::Thread(_) => {
            return Err(Error::Message("Threads, Userdata and Extern functions cannot be deep \
                                       cloned yet"
                                          .into()))
        }
        Int(i) => Ok(Int(i)),
        Float(f) => Ok(Float(f)),
    }
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
