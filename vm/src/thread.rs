use std::any::Any;
use std::cell::RefCell;
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
use vm::{Error, Result, GlobalVMState, Value, VMInt, ClosureData, ClosureDataDef, Def,
         ExternFunction, BytecodeFunction, Callable, PartialApplicationDataDef, Userdata};

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
pub struct RootedValue<'vm> {
    vm: &'vm Thread,
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
    pub fn vm(&self) -> &'vm Thread {
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
    global_state: Arc<GlobalVMState>,
    local_gc: RefCell<Gc>,
    roots: RefCell<Vec<GcPtr<Traverseable>>>,
    rooted_values: RefCell<Vec<Value>>,
    rooted_threads: RefCell<Vec<GcPtr<Thread>>>,
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
        self.rooted_threads.borrow().traverse(gc);
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
    fn push<'b>(self, _vm: &'vm Thread, stack: &mut StackFrame<'b>) -> Status {
        stack.push(Value::Thread(self.0));
        Status::Ok
    }
}


pub struct RootedThread(GcPtr<Thread>);

impl Drop for RootedThread {
    fn drop(&mut self) {
        let is_empty = {
            let mut roots = self.allocated_threads.borrow_mut();
            let index = roots.iter()
                             .position(|p| &**p as *const Thread == &*self.0 as *const Thread)
                             .expect("VM ptr");
            roots.swap_remove(index);
            roots.is_empty()
        };
        if is_empty {
            // The last RootedThread was dropped, there is no way to refer to the global state any
            // longer so drop everything
            let mut gc_ref = self.0.gc.borrow_mut();
            let gc_to_drop = ::std::mem::replace(&mut *gc_ref, Gc::new(0));
            // Make sure that the RefMut is dropped before the Gc itself as the RefCell is dropped
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

impl Traverseable for RootedThread {
    fn traverse(&self, gc: &mut Gc) {
        self.0.traverse(gc);
    }
}

impl RootedThread {
    pub fn new() -> RootedThread {
        let thread = Thread {
            global_state: Arc::new(GlobalVMState::new()),
            local_gc: RefCell::new(Gc::new(1)),
            stack: RefCell::new(Stack::new()),
            roots: RefCell::new(Vec::new()),
            rooted_values: RefCell::new(Vec::new()),
            rooted_threads: RefCell::new(Vec::new()),
        };
        let mut gc = Gc::new(0);
        let vm = RootedThread::from_gc_ptr(gc.alloc(Move(thread)));
        *vm.gc.borrow_mut() = gc;
        // Enter the top level scope
        StackFrame::frame(vm.stack.borrow_mut(), 0, State::Unknown);
        vm
    }

    pub fn from_gc_ptr(p: GcPtr<Thread>) -> RootedThread {
        let vm = RootedThread(p);
        vm.allocated_threads.borrow_mut().push(vm.0);
        vm
    }

    pub fn into_raw(self) -> *const Thread {
        let ptr: *const Thread = &*self.0;
        ::std::mem::forget(self);
        ptr
    }

    pub unsafe fn from_raw(ptr: *const Thread) -> RootedThread {
        RootedThread(GcPtr::from_raw(ptr))
    }
}

impl Thread {
    fn traverse_fields_except_stack(&self, gc: &mut Gc) {
        self.global_state.traverse(gc);
        self.roots.borrow().traverse(gc);
        self.rooted_values.borrow().traverse(gc);
    }

    pub fn new_thread(&self) -> RootedThread {
        let vm = Thread {
            global_state: self.global_state.clone(),
            local_gc: RefCell::new(self.local_gc.borrow().new_child_gc()),
            stack: RefCell::new(Stack::new()),
            roots: RefCell::new(Vec::new()),
            rooted_values: RefCell::new(Vec::new()),
            rooted_threads: RefCell::new(Vec::new()),
        };
        // Enter the top level scope
        StackFrame::frame(vm.stack.borrow_mut(), 0, State::Unknown);
        RootedThread::from_gc_ptr(self.alloc(&self.stack.borrow(), Move(vm)))
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
        let env = self.get_env();
        let (value, typ) = try!(env.get_binding(name));
        // Finally check that type of the returned value is correct
        if *typ == T::make_type(self) {
            T::from_value(self, Variants(&value))
                .ok_or_else(|| Error::Message(format!("Could not retrieve global `{}`", name)))
        } else {
            Err(Error::Message(format!("Could not retrieve global `{}` as the types did not \
                                        match",
                                       name)))
        }
    }

    pub fn find_type_info(&self, name: &str) -> Result<types::Alias<Symbol, TcType>> {
        let env = self.get_env();
        env.find_type_info(name)
           .map(|alias| alias.into_owned())
    }

    /// Returns the current stackframe
    pub fn release_lock<'vm>(&'vm self, lock: ::stack::Lock) -> StackFrame<'vm> {
        self.stack.borrow_mut().release_lock(lock);
        self.current_frame()
    }

    /// Returns the current stackframe
    pub fn current_frame(&self) -> StackFrame {
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
        let mut gc = self.local_gc.borrow_mut();
        f(&mut gc, roots)
    }

    pub fn new_data(&self, tag: VMTag, fields: &[Value]) -> Value {
        Value::Data(self.local_gc.borrow_mut().alloc(Def {
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
        let closure = self.alloc(&self.stack.borrow(), ClosureDataDef(f, &[]));
        self.set_global(id, typ, Metadata::default(), Closure(closure)).unwrap();
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

    pub fn deep_clone(&self, value: Value) -> Result<Value> {
        let mut visited = HashMap::new();
        deep_clone(&value, &mut visited, &mut self.local_gc.borrow_mut())
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
            debug_instruction(&stack, index, instr, function);
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
                    let mut stack = StackFrame::frame(stack, 0, State::Excess);
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
            result.push(vm, stack);
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
