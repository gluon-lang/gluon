use std::any::Any;
use std::marker::PhantomData;

#[cfg(feature = "serde")]
use crate::serde::{Deserialize, Deserializer};

use futures::{
    prelude::*,
    ready,
    task::{self, Poll},
};

use crate::base::symbol::Symbol;
use crate::base::types::ArcType;

use crate::api::{ActiveThread, AsyncPushable, Getable, Pushable, RootedValue, VmType};
use crate::compiler::{CompiledFunction, CompiledModule};
use crate::gc::{Move, Trace};
use crate::stack::{ExternState, StackFrame};
use crate::thread::{RootedThread, Status, Thread, ThreadInternal, VmRoot, VmRootInternal};
use crate::types::{Instruction, VmIndex};
use crate::value::ExternFunction;
use crate::{Error, Result, Variants};

pub type GluonFunction = extern "C" fn(&Thread) -> Status;

pub struct Primitive<F> {
    /// Exposed for macros
    #[doc(hidden)]
    pub name: &'static str,
    /// Exposed for macros
    #[doc(hidden)]
    pub function: GluonFunction,
    /// Exposed for macros
    #[doc(hidden)]
    pub _typ: PhantomData<F>,
}

#[inline]
pub fn primitive<F>(
    name: &'static str,
    function: extern "C" fn(&Thread) -> Status,
) -> Primitive<F>
where
{
    Primitive {
        name: name,
        function: function,
        _typ: PhantomData,
    }
}

#[inline]
pub fn primitive_f<F>(
    name: &'static str,
    function: extern "C" fn(&Thread) -> Status,
    _: F,
) -> Primitive<F>
where
    for<'vm> F: VmFunction<'vm> + VmType,
{
    Primitive {
        name: name,
        function: function,
        _typ: PhantomData,
    }
}

impl<'vm, F: VmType> VmType for Primitive<F> {
    type Type = F::Type;
    fn make_type(vm: &Thread) -> ArcType {
        F::make_type(vm)
    }
}

impl<'vm, F> Pushable<'vm> for Primitive<F>
where
    F: FunctionType + VmType,
{
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        // Map rust modules into gluon modules
        let name = if let Some(i) = self.name.rfind("::<") {
            &self.name[..i]
        } else {
            self.name
        };
        let id = Symbol::from(name.replace("::", "."));
        context.context().push_new_alloc(Move(ExternFunction {
            id: id,
            args: F::arguments(),
            function: self.function,
        }))?;
        Ok(())
    }
}

pub struct CPrimitive {
    function: GluonFunction,
    args: VmIndex,
    id: Symbol,
}

impl CPrimitive {
    pub unsafe fn new(function: GluonFunction, args: VmIndex, id: &str) -> CPrimitive {
        CPrimitive {
            id: Symbol::from(id),
            function: function,
            args: args,
        }
    }
}

impl<'vm> Pushable<'vm> for CPrimitive {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.context().push_new_alloc(Move(ExternFunction {
            id: self.id,
            args: self.args,
            function: self.function,
        }))?;
        Ok(())
    }
}

fn make_type<T: ?Sized + VmType>(vm: &Thread) -> ArcType {
    <T as VmType>::make_type(vm)
}

/// Type which represents a function reference in gluon
pub type FunctionRef<'vm, F> = Function<&'vm Thread, F>;
pub type OwnedFunction<F> = Function<RootedThread, F>;

/// Type which represents an function in gluon
#[derive(Clone, Debug)]
pub struct Function<T, F>
where
    T: VmRootInternal,
{
    value: RootedValue<T>,
    _marker: PhantomData<F>,
}

unsafe impl<T: VmRootInternal + Trace, F> Trace for Function<T, F> {
    impl_trace_fields! { self, gc; value }
}

#[cfg(feature = "serde")]
impl<'de, V> Deserialize<'de> for Function<RootedThread, V> {
    fn deserialize<D>(deserializer: D) -> ::std::result::Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let value = crate::api::de::deserialize_raw_value(deserializer)?;
        Ok(Function {
            value,
            _marker: PhantomData,
        })
    }
}

impl<T, F> Function<T, F>
where
    T: VmRootInternal,
{
    pub fn get_variant(&self) -> Variants {
        self.value.get_variant()
    }

    pub fn vm(&self) -> &Thread {
        self.value.vm()
    }

    pub fn re_root<'vm, U>(&self, vm: U) -> Result<Function<U, F>>
    where
        U: VmRoot<'vm>,
    {
        Ok(Function {
            value: self.value.re_root(vm)?,
            _marker: self._marker,
        })
    }
}

impl<T, F> VmType for Function<T, F>
where
    T: VmRootInternal,
    F: VmType,
{
    type Type = F::Type;
    fn make_type(vm: &Thread) -> ArcType {
        F::make_type(vm)
    }
}

impl<'vm, T, F: Any> Pushable<'vm> for Function<T, F>
where
    T: VmRootInternal,
    F: VmType,
{
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        context.push(self.value.get_variant());
        Ok(())
    }
}

impl<'vm, 'value, F> Getable<'vm, 'value> for Function<&'vm Thread, F> {
    impl_getable_simple!();

    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Function<&'vm Thread, F> {
        Function {
            value: vm.root_value(value),
            _marker: PhantomData,
        } //TODO not type safe
    }
}

impl<'vm, 'value, F> Getable<'vm, 'value> for Function<RootedThread, F> {
    impl_getable_simple!();

    fn from_value(vm: &'vm Thread, value: Variants<'value>) -> Self {
        Function {
            value: vm.root_value(value),
            _marker: PhantomData,
        } //TODO not type safe
    }
}

/// Trait which represents a function
pub trait FunctionType {
    /// Returns how many arguments the function needs to be provided to call it
    fn arguments() -> VmIndex;
}

/// Trait which abstracts over types which can be called by being pulling the arguments it needs
/// from the virtual machine's stack
pub trait VmFunction<'vm> {
    fn unpack_and_call(&self, vm: &'vm Thread) -> Status;
}

impl<'s, T: FunctionType> FunctionType for &'s T {
    fn arguments() -> VmIndex {
        T::arguments()
    }
}

impl<'vm, 's, T: ?Sized> VmFunction<'vm> for &'s T
where
    T: VmFunction<'vm>,
{
    fn unpack_and_call(&self, vm: &'vm Thread) -> Status {
        (**self).unpack_and_call(vm)
    }
}

impl<F> FunctionType for Box<F>
where
    F: FunctionType,
{
    fn arguments() -> VmIndex {
        F::arguments()
    }
}

impl<'vm, F: ?Sized> VmFunction<'vm> for Box<F>
where
    F: VmFunction<'vm>,
{
    fn unpack_and_call(&self, vm: &'vm Thread) -> Status {
        (**self).unpack_and_call(vm)
    }
}

macro_rules! vm_function_impl {
    ([$($f:tt)*] $($args:ident),* -> $ret: ident, $ret_ty: ty) => {

impl <'vm, $($args,)* $ret> VmFunction<'vm> for $($f)* ($($args),*) -> $ret_ty
where $($args: Getable<'vm, 'vm> + 'vm,)*
      $ret: AsyncPushable<'vm> + VmType + 'vm,
      $ret_ty: AsyncPushable<'vm> + VmType + 'vm,
      $ret::Type: Sized,
      <$ret_ty as VmType>::Type: Sized,
{
    #[allow(non_snake_case, unused_mut, unused_assignments, unused_variables, unused_unsafe)]
    fn unpack_and_call(&self, vm: &'vm Thread) -> Status {
        let n_args = Self::arguments();
        let mut context = vm.current_context();
        let frame_index = context.stack().get_frames().len() as VmIndex - 1;
        let mut i = 0;
        let lock;
        let r = unsafe {

            let stack = StackFrame::<ExternState>::current(context.stack());
            $(
                let variants = Variants::with_root(&stack[i], vm);
                let mut proxy = match $args::to_proxy(vm, variants) {
                    Ok(x) => x,
                    Err(err) => {
                        drop(stack);
                        err.to_string().vm_push(&mut context).unwrap();
                        return Status::Error;
                    }
                };
                // The proxy will live as along as the 'value lifetime we just created
                let $args = $args::from_proxy(vm, &mut *(&mut proxy as *mut _));
                i += 1;
            )*
            // Lock the frame to ensure that any references to the stack stay rooted
            lock = stack.into_lock();

            drop(context);
            let r = (*self)($($args),*);
            context = vm.current_context();
            r
        };

        r.async_status_push(&mut context, lock, frame_index)
    }
}

    }
}

fn block_on_sync<F, T>(f: F) -> F::Output
where
    F: Future<Output = Result<T>>,
{
    use std::task::{Context, RawWaker, RawWakerVTable, Waker};

    static VTABLE: RawWakerVTable = RawWakerVTable::new(
        |p| RawWaker::new(p, &VTABLE),
        |_| unreachable!(),
        |_| unreachable!(),
        |_| (),
    );

    let waker_state = ();
    let waker = unsafe { Waker::from_raw(RawWaker::new(&waker_state, &VTABLE)) };
    let mut context = Context::from_waker(&waker);

    futures::pin_mut!(f);
    match f.poll(&mut context) {
        Poll::Ready(value) => value,
        Poll::Pending => Err(Error::Message("Unexpected async".into())).into(),
    }
}

macro_rules! make_vm_function {
    ($($args:ident),*) => {
        make_vm_function_inner!($($args),* -> R, R);
    }
}
macro_rules! make_vm_function_inner {
    ($($args:ident),* -> $ret: ident, $ret_ty: ty) => (
impl <$($args: VmType,)* $ret: VmType> VmType for fn ($($args),*) -> $ret_ty
where
    <$ret_ty as VmType>::Type: Sized,
    <$ret as VmType>::Type: Sized,
{
    #[allow(non_snake_case)]
    type Type = fn ($($args::Type),*) -> <$ret_ty as VmType>::Type;

    #[allow(non_snake_case)]
    fn make_type(vm: &Thread) -> ArcType {
        let args = vec![$(make_type::<$args>(vm)),*];
        vm.global_env().type_cache().function(args, make_type::<$ret_ty>(vm))
    }
}

vm_function_impl!([fn] $($args),* -> $ret, $ret_ty);
vm_function_impl!([dyn Fn] $($args),* -> $ret, $ret_ty);

impl <'vm, $($args,)* $ret: VmType> FunctionType for fn ($($args),*) -> $ret_ty
where
    $ret_ty: VmType,
    <$ret_ty as VmType>::Type: Sized,
    $ret::Type: Sized,
{
    fn arguments() -> VmIndex {
        count!($($args),*) + <$ret_ty as VmType>::EXTRA_ARGS
    }
}

impl <'s, $($args,)* $ret: VmType> FunctionType for dyn Fn($($args),*) -> $ret_ty + 's
where
    $ret_ty: VmType,
    <$ret_ty as VmType>::Type: Sized,
    $ret::Type: Sized,
{
    fn arguments() -> VmIndex {
        count!($($args),*) + <$ret_ty as VmType>::EXTRA_ARGS
    }
}

impl <'s, $($args: VmType,)* $ret: VmType> VmType for dyn Fn($($args),*) -> $ret_ty + 's
where
    $ret_ty: VmType,
    <$ret_ty as VmType>::Type: Sized,
    $ret::Type: Sized,
{
    type Type = fn ($($args::Type),*) -> <$ret_ty as VmType>::Type;

    #[allow(non_snake_case)]
    fn make_type(vm: &Thread) -> ArcType {
        <fn ($($args),*) -> $ret_ty>::make_type(vm)
    }
}

impl<T, $($args,)* $ret> Function<T, fn($($args),*) -> $ret_ty>
where
    $($args: for<'vm> Pushable<'vm>,)*
    T: VmRootInternal,
    $ret: VmType + for<'x, 'value> Getable<'x, 'value>,
    <$ret_ty as VmType>::Type: Sized,
    $ret::Type: Sized,
{
    #[allow(non_snake_case)]
    pub fn call(&mut self $(, $args: $args)*) -> Result<$ret_ty> {
        block_on_sync(future::lazy(|cx| {
            match self.call_first(cx, $($args),*) {
                Poll::Ready(r) => r,
                Poll::Pending => Err(Error::Message("Unexpected async".into())).into(),
            }
        }))
    }

    #[allow(non_snake_case)]
    fn call_first(&self, cx: &mut task::Context<'_> $(, $args: $args)*) -> Poll<Result<$ret_ty>> {
        let vm = self.value.vm();
        let mut context = vm.current_context();
        context.push(self.value.get_variant());
        $(
            $args.vm_push(&mut context)?;
        )*
        for _ in 0..<$ret_ty as VmType>::EXTRA_ARGS {
            0.vm_push(&mut context).unwrap();
        }
        let args = count!($($args),*) + <$ret_ty as VmType>::EXTRA_ARGS;
        let context =  ready!(vm.call_function(cx, context.into_owned(), args))?;
        let mut context = context.unwrap();
        let result = {
            let value = context.stack.last().unwrap();
            Self::return_value(vm, value)
        };
        context.stack.pop();
        Poll::Ready(result)
    }

    fn return_value(vm: &Thread, value: Variants) -> Result<$ret_ty> {
        Ok(<$ret_ty>::from_value(vm, value))
    }
}

impl<T, $($args,)* $ret> Function<T, fn($($args),*) -> $ret_ty>
where
    $($args: for<'vm> Pushable<'vm>,)*
    T: VmRootInternal + Clone + Send,
    $ret: VmType + for<'x, 'value> Getable<'x, 'value> + Send + Sync + 'static,
    <$ret_ty as VmType>::Type: Sized,
    $ret::Type: Sized,
{
    #[allow(non_snake_case)]
    pub async fn call_async(
        &mut self
        $(, $args: $args)*
        ) -> Result<$ret_ty>
    {
        use crate::thread::Execute;
        match future::lazy(|cx| self.call_first(cx, $($args),*)).await {
            Poll::Ready(result) => result,
            Poll::Pending => {
                let vm = self.value.vm().root_thread();
                let value = Execute::new(vm).await?;
                Self::return_value(value.vm(), value.get_variant())
            }
        }
    }
}
    )
}

make_vm_function_inner!( -> R, crate::api::IO<R>);
make_vm_function!(A);
make_vm_function!(A, B);
make_vm_function!(A, B, C);
make_vm_function!(A, B, C, D);
make_vm_function!(A, B, C, D, E);
make_vm_function!(A, B, C, D, E, F);
make_vm_function!(A, B, C, D, E, F, G);

impl<'vm, T, F> Function<T, F>
where
    T: VmRootInternal + 'vm,
    F: VmType,
{
    pub fn cast<F2>(self) -> Result<Function<T, F2>>
    where
        F2: VmType,
    {
        let vm = self.value.vm();
        if F::make_type(vm) == F2::make_type(vm) {
            Ok(Function {
                value: self.value,
                _marker: PhantomData,
            })
        } else {
            Err(Error::Message("Function cast is not compatible".into()))
        }
    }

    /// Calls `self` with a number of arguments that is only known at runtime.
    ///
    /// WARNING: No check is done that the number of arguments is correct. The VM may return an
    /// error or panic if an incorrect number of arguments is passed.
    pub fn call_any<A, R>(&'vm self, args: impl IntoIterator<Item = A>) -> Result<R>
    where
        A: Pushable<'vm>,
        R: for<'value> Getable<'vm, 'value> + VmType,
    {
        block_on_sync(self.call_any_async(args))
    }

    async fn call_any_async<A, R>(&'vm self, args: impl IntoIterator<Item = A>) -> Result<R>
    where
        A: Pushable<'vm>,
        R: for<'value> Getable<'vm, 'value> + VmType,
    {
        let mut args = Some(args);
        future::poll_fn(move |cx| self.call_any_first(cx, args.take().unwrap())).await
    }

    fn call_any_first<A, R>(
        &'vm self,
        cx: &mut task::Context<'_>,
        args: impl IntoIterator<Item = A>,
    ) -> Poll<Result<R>>
    where
        A: Pushable<'vm>,
        R: for<'value> Getable<'vm, 'value> + VmType,
    {
        let vm = self.value.vm();
        let mut context = vm.current_context();
        context.push(self.value.get_variant());

        let mut arg_count = R::EXTRA_ARGS;
        for arg in args {
            arg_count += 1;
            arg.vm_push(&mut context)?;
        }
        for _ in 0..R::EXTRA_ARGS {
            0.vm_push(&mut context).unwrap();
        }
        let context = ready!(vm.call_function(cx, context.into_owned(), arg_count))?;
        let mut context = context.unwrap();
        let result = {
            let value = context.stack.last().unwrap();
            Ok(R::from_value(vm, value))
        };
        context.stack.pop();
        result.into()
    }
}

pub struct TypedBytecode<T> {
    id: Symbol,
    args: VmIndex,
    instructions: Vec<Instruction>,
    _marker: PhantomData<T>,
}

impl<T> TypedBytecode<T> {
    pub fn new(name: &str, args: VmIndex, instructions: Vec<Instruction>) -> TypedBytecode<T>
    where
        T: VmType,
    {
        TypedBytecode {
            id: Symbol::from(name),
            args,
            instructions,
            _marker: PhantomData,
        }
    }
}

impl<T: VmType> VmType for TypedBytecode<T> {
    type Type = T::Type;

    fn make_type(vm: &Thread) -> ArcType {
        T::make_type(vm)
    }

    fn make_forall_type(vm: &Thread) -> ArcType {
        T::make_forall_type(vm)
    }

    const EXTRA_ARGS: VmIndex = T::EXTRA_ARGS;
}

impl<'vm, T: VmType> Pushable<'vm> for TypedBytecode<T> {
    fn vm_push(self, context: &mut ActiveThread<'vm>) -> Result<()> {
        let closure = {
            let thread = context.thread();
            let mut compiled_module = CompiledModule::from(CompiledFunction::new(
                self.args,
                self.id,
                T::make_forall_type(thread),
                "".into(),
            ));
            compiled_module.function.instructions = self.instructions;
            thread
                .global_env()
                .new_global_thunk(thread, compiled_module)?
        };
        closure.vm_push(context)
    }
}
