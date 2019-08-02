use std::{
    fmt,
    marker::PhantomData,
    ops::{Deref, DerefMut, Index, IndexMut, Range, RangeFrom, RangeFull, RangeTo},
};

use crate::base::{pos::Line, symbol::Symbol};

use crate::{
    gc::{self, CloneUnrooted, CopyUnrooted, GcPtr, Trace},
    types::VmIndex,
    value::{ClosureData, DataStruct, ExternFunction, Value, ValueRepr},
    Variants,
};

pub trait StackPrimitive {
    fn push_to(&self, stack: &mut Stack);

    fn extend_to<'b, I>(iter: I, stack: &mut Stack)
    where
        I: IntoIterator<Item = &'b Self>,
        Self: 'b,
    {
        for item in iter {
            item.push_to(stack);
        }
    }
}

impl<'a, T: StackPrimitive + 'a> StackPrimitive for &'a T {
    #[inline(always)]
    fn push_to(&self, stack: &mut Stack) {
        (**self).push_to(stack)
    }

    fn extend_to<'b, I>(iter: I, stack: &mut Stack)
    where
        I: IntoIterator<Item = &'b Self>,
        Self: 'b,
    {
        StackPrimitive::extend_to(iter.into_iter().map(|i| *i), stack)
    }
}

impl<'a, T: StackPrimitive + 'a> StackPrimitive for gc::Borrow<'a, T> {
    #[inline(always)]
    fn push_to(&self, stack: &mut Stack) {
        (**self).push_to(stack)
    }

    fn extend_to<'b, I>(iter: I, stack: &mut Stack)
    where
        I: IntoIterator<Item = &'b Self>,
        Self: 'b,
    {
        StackPrimitive::extend_to(iter.into_iter().map(|i| &**i), stack)
    }
}

impl<'a> StackPrimitive for Variants<'a> {
    #[inline(always)]
    fn push_to(&self, stack: &mut Stack) {
        self.0.push_to(stack)
    }

    fn extend_to<'b, I>(iter: I, stack: &mut Stack)
    where
        I: IntoIterator<Item = &'b Self>,
        Self: 'b,
    {
        Value::extend_to(iter.into_iter().map(|i| i.get_value()), stack)
    }
}

impl StackPrimitive for ValueRepr {
    #[inline(always)]
    fn push_to(&self, stack: &mut Stack) {
        Value::from_ref(self).push_to(stack)
    }

    fn extend_to<'b, I>(iter: I, stack: &mut Stack)
    where
        I: IntoIterator<Item = &'b Self>,
    {
        Value::extend_to(iter.into_iter().map(Value::from_ref), stack)
    }
}

impl StackPrimitive for Value {
    #[inline(always)]
    fn push_to(&self, stack: &mut Stack) {
        // SAFETY The value is rooted by pushing it on the stack
        unsafe {
            stack.values.push(self.clone_unrooted());
        }
    }

    #[inline(always)]
    fn extend_to<'b, I>(iter: I, stack: &mut Stack)
    where
        I: IntoIterator<Item = &'b Self>,
    {
        // SAFETY The value is rooted by pushing it on the stack
        unsafe {
            stack
                .values
                .extend(iter.into_iter().map(|i| i.clone_unrooted()));
        }
    }
}

#[derive(Debug, PartialEq)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive",
    serde(
        deserialize_state = "crate::serialization::DeSeed<'gc>",
        de_parameters = "'gc"
    )
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(serialize_state = "crate::serialization::SeSeed")
)]
pub struct ClosureState {
    #[cfg_attr(
        feature = "serde_derive",
        serde(state_with = "crate::serialization::closure")
    )]
    pub(crate) closure: GcPtr<ClosureData>,
    pub(crate) instruction_index: usize,
}

unsafe impl CopyUnrooted for ClosureState {}
impl CloneUnrooted for ClosureState {
    type Value = Self;
    #[inline]
    unsafe fn clone_unrooted(&self) -> Self {
        self.copy_unrooted()
    }
}

#[derive(Debug, PartialEq)]
#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
pub(crate) enum ExternCallState {
    Start,
    InPoll,
    Poll,
}

#[derive(Debug, PartialEq)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive",
    serde(
        deserialize_state = "crate::serialization::DeSeed<'gc>",
        de_parameters = "'gc"
    )
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(serialize_state = "crate::serialization::SeSeed")
)]
pub struct ExternState {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub(crate) function: GcPtr<ExternFunction>,
    pub(crate) call_state: ExternCallState,
    /// The number of arguments that are locked in this frame
    locked: Option<VmIndex>,
}

unsafe impl CopyUnrooted for ExternState {}
impl CloneUnrooted for ExternState {
    type Value = Self;
    #[inline]
    unsafe fn clone_unrooted(&self) -> Self {
        self.copy_unrooted()
    }
}

impl ExternState {
    pub fn new(function: &GcPtr<ExternFunction>) -> gc::Borrow<Self> {
        construct_gc! {
            ExternState {
                @ function,
                call_state: ExternCallState::Start,
                locked: None,
            }
        }
    }

    pub fn is_locked(&self) -> bool {
        self.locked.is_some()
    }
}

pub trait StackState: CopyUnrooted + Sized {
    fn from_state(state: &State) -> &Self;
    fn from_state_mut(state: &mut State) -> &mut Self;
    fn to_state(&self) -> gc::Borrow<State>;
}

impl StackState for State {
    fn from_state(state: &State) -> &Self {
        state
    }
    fn from_state_mut(state: &mut State) -> &mut Self {
        state
    }
    fn to_state(&self) -> gc::Borrow<State> {
        gc::Borrow::new(self)
    }
}

impl StackState for ClosureState {
    fn from_state(state: &State) -> &Self {
        match state {
            State::Closure(state) => state,
            _ => ice!("Expected closure state, got {:?}", state),
        }
    }
    fn from_state_mut(state: &mut State) -> &mut Self {
        match state {
            State::Closure(state) => state,
            _ => ice!("Expected closure state, got {:?}", state),
        }
    }
    fn to_state(&self) -> gc::Borrow<State> {
        construct_gc!(State::Closure(@ gc::Borrow::new(self)))
    }
}

impl StackState for ExternState {
    fn from_state(state: &State) -> &Self {
        match state {
            State::Extern(state) => state,
            _ => ice!("Expected extern: {:?}", state),
        }
    }
    fn from_state_mut(state: &mut State) -> &mut Self {
        match state {
            State::Extern(state) => state,
            _ => ice!("Expected closure state, got {:?}", state),
        }
    }
    fn to_state(&self) -> gc::Borrow<State> {
        construct_gc!(State::Extern(@ gc::Borrow::new(self)))
    }
}

#[derive(Debug, PartialEq)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive",
    serde(
        deserialize_state = "crate::serialization::DeSeed<'gc>",
        de_parameters = "'gc"
    )
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(serialize_state = "crate::serialization::SeSeed")
)]
pub enum State {
    Unknown,
    Closure(#[cfg_attr(feature = "serde_derive", serde(state))] ClosureState),
    Extern(#[cfg_attr(feature = "serde_derive", serde(state))] ExternState),
}

unsafe impl CopyUnrooted for State {}
impl CloneUnrooted for State {
    type Value = Self;
    #[inline]
    unsafe fn clone_unrooted(&self) -> Self {
        self.copy_unrooted()
    }
}

#[derive(Debug, PartialEq)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive",
    serde(
        deserialize_state = "crate::serialization::DeSeed<'gc>",
        de_parameters = "'gc"
    )
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(
        deserialize = "S: ::serde::de::DeserializeState<'de, crate::serialization::DeSeed<'gc>>"
    ))
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(serialize_state = "crate::serialization::SeSeed")
)]
pub struct Frame<S = State> {
    pub offset: VmIndex,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    pub state: S,
    pub excess: bool,
}

unsafe impl<S> CopyUnrooted for Frame<S> where S: CopyUnrooted {}
impl<S> CloneUnrooted for Frame<S>
where
    S: CopyUnrooted,
{
    type Value = Self;
    #[inline]
    unsafe fn clone_unrooted(&self) -> Self {
        self.copy_unrooted()
    }
}

impl Frame<ClosureState> {
    pub fn upvars(&self) -> &[Value] {
        &self.state.closure.upvars
    }
}

impl<'a> FrameView<'a, ClosureState> {
    pub fn upvars(&self) -> &'a [Value] {
        &self.state.closure.upvars
    }
}

impl Frame<State> {
    fn from_state<S>(&self) -> gc::Borrow<Frame<S>>
    where
        S: StackState,
    {
        construct_gc!(Frame {
            offset: self.offset,
            @state: gc::Borrow::new(S::from_state(&self.state)),
            excess: self.excess,
        })
    }
}

#[derive(Debug)]
pub struct FrameView<'a, S> {
    pub offset: VmIndex,
    pub state: &'a S,
    pub excess: bool,
}

#[derive(Debug)]
pub struct FrameViewMut<'a, S> {
    pub offset: &'a mut VmIndex,
    pub state: &'a mut S,
    pub excess: &'a mut bool,
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[must_use = "Unused locks will prevent the stack from unwinding"]
pub struct Lock(VmIndex);

#[derive(Debug)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive",
    serde(
        deserialize_state = "crate::serialization::DeSeed<'gc>",
        de_parameters = "'gc"
    )
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(serialize_state = "crate::serialization::SeSeed")
)]
pub struct Stack {
    #[cfg_attr(feature = "serde_derive", serde(state))]
    values: Vec<Value>,
    #[cfg_attr(feature = "serde_derive", serde(state))]
    frames: Vec<Frame<State>>,
}

unsafe impl Trace for Stack {
    impl_trace! { self, gc,
        mark(&self.values, gc)
    }
}

impl Stack {
    pub fn new() -> Stack {
        Stack {
            values: Vec::new(),
            frames: Vec::new(),
        }
    }

    fn assert_pop(&self, count: VmIndex) {
        if let Some(frame) = self.frames.last() {
            assert!(
                self.len() >= frame.offset + count,
                "Attempted to pop value which did not belong to the current frame"
            );
            if let State::Extern(ExternState {
                locked: Some(args), ..
            }) = *frame.state.to_state()
            {
                assert!(
                    self.len() >= frame.offset + args + count,
                    "Attempt to pop locked value"
                );
            }
        }
    }

    pub fn pop(&mut self) -> Value {
        self.assert_pop(1);
        self.values.pop().expect("pop on empty stack")
    }

    pub fn pop_value<'s>(&'s mut self) -> PopValue<'s> {
        self.assert_pop(1);
        unsafe {
            let value = self.last().unwrap().get_repr().clone_unrooted();
            PopValue(self, Variants(value, PhantomData))
        }
    }

    pub fn pop_many(&mut self, count: VmIndex) {
        self.assert_pop(count);
        let len = self.values.len();
        self.values.truncate(len - count as usize);
    }

    pub fn clear(&mut self) {
        self.values.clear();
    }

    pub fn slide(&mut self, count: VmIndex) {
        let last = self.len() - 1;
        let i = last - count;
        self.copy_value(last, i);
        self.pop_many(count);
    }

    fn copy_value(&mut self, from: VmIndex, to: VmIndex) {
        // SAFETY The value is stored in the stack, rooting it
        unsafe {
            self[to] = self[from].clone_unrooted();
        }
    }

    #[inline(always)]
    pub fn push<T>(&mut self, v: T)
    where
        T: StackPrimitive,
    {
        v.push_to(self)
    }

    pub fn last(&self) -> Option<Variants> {
        self.get_variant(self.len() - 1)
    }

    #[inline]
    pub fn get_variant(&self, index: VmIndex) -> Option<Variants> {
        if index < self.len() {
            Some(Variants::new(&self.values[index as usize]))
        } else {
            None
        }
    }

    pub fn remove_range(&mut self, from: VmIndex, to: VmIndex) {
        self.values.drain(from as usize..to as usize);
    }

    pub fn len(&self) -> VmIndex {
        self.values.len() as VmIndex
    }

    pub fn get_values(&self) -> &[Value] {
        &self.values
    }

    pub fn get_frames(&self) -> &[Frame<State>] {
        &self.frames
    }

    pub fn get_frames_mut(&mut self) -> &mut [Frame<State>] {
        &mut self.frames
    }

    pub fn current_frame<S>(&mut self) -> StackFrame<S>
    where
        S: StackState,
    {
        let _: &Frame<S> = &*self.get_frames().last().expect("Frame").from_state();
        StackFrame {
            _frame: PhantomData,
            stack: self,
        }
    }

    /// Release a lock on the stack.
    ///
    /// Panics if the lock is not the top-most lock
    pub fn release_lock(&mut self, lock: Lock) {
        let i = self
            .frames
            .iter()
            .rposition(|frame| {
                if let State::Extern(ExternState {
                    locked: Some(_), ..
                }) = frame.state
                {
                    true
                } else {
                    false
                }
            })
            .unwrap();
        let frame = &mut self.frames[i];
        assert_eq!(frame.offset, lock.0);
        if let State::Extern(ref mut ext) = frame.state {
            ext.locked = None;
        }
    }

    /// Creates a stackrace starting from `frame_level`
    pub fn stacktrace(&self, frame_level: usize) -> Stacktrace {
        let frames = self.get_frames()[frame_level..]
            .iter()
            .filter_map(|frame| match frame.state {
                State::Closure(ClosureState {
                    ref closure,
                    instruction_index,
                }) => {
                    let line = closure
                        .function
                        .debug_info
                        .source_map
                        .line(instruction_index);
                    Some(Some(StacktraceFrame {
                        name: closure.function.name.clone(),
                        line,
                    }))
                }
                State::Extern(ref ext) => Some(Some(StacktraceFrame {
                    name: ext.function.id.clone(),
                    line: None,
                })),
                State::Unknown => Some(None),
            })
            .collect();
        Stacktrace { frames }
    }
}

impl Index<VmIndex> for Stack {
    type Output = Value;
    fn index(&self, index: VmIndex) -> &Value {
        &self.values[index as usize]
    }
}

impl IndexMut<VmIndex> for Stack {
    fn index_mut(&mut self, index: VmIndex) -> &mut Value {
        &mut self.values[index as usize]
    }
}

impl Index<RangeFrom<VmIndex>> for Stack {
    type Output = [Value];
    fn index(&self, range: RangeFrom<VmIndex>) -> &[Value] {
        &self.values[range.start as usize..]
    }
}

impl Index<RangeTo<VmIndex>> for Stack {
    type Output = [Value];
    fn index(&self, range: RangeTo<VmIndex>) -> &[Value] {
        &self.values[..range.end as usize]
    }
}

impl Index<RangeFull> for Stack {
    type Output = [Value];
    fn index(&self, range: RangeFull) -> &[Value] {
        &self.values[range]
    }
}

pub struct StackFrame<'b, S = State>
where
    S: StackState,
{
    pub stack: &'b mut Stack,
    _frame: PhantomData<Frame<S>>,
}

impl<'b, S> fmt::Debug for StackFrame<'b, S>
where
    S: fmt::Debug + StackState,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("StackFrame")
            .field("stack", &*self.stack)
            .field("frame", &self.frame())
            .finish()
    }
}

impl<'a: 'b, 'b> StackFrame<'b, State> {
    pub fn from_state<T>(self) -> StackFrame<'b, T>
    where
        T: StackState,
    {
        Frame::from_state::<T>(self.stack.frames.last().unwrap());
        let stack = self.take_stack();
        StackFrame {
            stack,
            _frame: PhantomData,
        }
    }

    pub fn new_frame(stack: &'b mut Stack, args: VmIndex, state: State) -> StackFrame<'b> {
        Self::add_new_frame(stack, args, gc::Borrow::new(&state));
        StackFrame {
            stack,
            _frame: PhantomData,
        }
    }
}

impl<'a: 'b, 'b> StackFrame<'b, ExternState> {
    /// Lock the stack below the current offset
    pub fn into_lock(mut self) -> Lock {
        let len = self.len();
        let frame = self.frame_mut();
        frame.state.locked = Some(len);
        let lock = Lock(*frame.offset);
        self.take_stack();
        lock
    }
}

impl<'a: 'b, 'b, S> StackFrame<'b, S>
where
    S: StackState,
{
    fn offset(&self) -> VmIndex {
        self.frame().offset
    }

    pub fn frame(&self) -> FrameView<S> {
        let Frame {
            offset,
            ref state,
            excess,
        } = *self.stack.frames.last().unwrap();
        FrameView {
            offset,
            state: S::from_state(state),
            excess,
        }
    }

    pub fn frame_mut(&mut self) -> FrameViewMut<S> {
        let Frame {
            offset,
            state,
            excess,
        } = self.stack.frames.last_mut().unwrap();
        FrameViewMut {
            offset,
            state: S::from_state_mut(state),
            excess,
        }
    }

    pub fn take_stack(self) -> &'b mut Stack {
        self.stack
    }

    pub fn len(&self) -> VmIndex {
        self.stack.len() - self.offset()
    }

    #[inline(always)]
    pub fn push<T>(&mut self, v: T)
    where
        T: StackPrimitive,
    {
        v.push_to(&mut self.stack)
    }

    pub fn top(&self) -> &Value {
        self.stack.values.last().expect("StackFrame: top")
    }

    pub fn pop(&mut self) -> Value {
        self.stack.pop()
    }

    pub fn pop_value<'s>(&'s mut self) -> PopValue<'s> {
        self.stack.pop_value()
    }

    pub fn pop_many(&mut self, count: VmIndex) {
        self.stack.pop_many(count);
    }

    pub fn clear(&mut self) {
        let len = self.len();
        self.stack.pop_many(len);
    }

    pub fn slide(&mut self, count: VmIndex) {
        self.stack.slide(count);
    }

    #[inline]
    pub fn get_variant(&self, index: VmIndex) -> Option<Variants> {
        self.stack.get_variant(self.offset() + index)
    }

    #[inline]
    pub fn get_value<'vm, 'value, T>(
        &'value self,
        thread: &'vm crate::thread::Thread,
        index: VmIndex,
    ) -> Option<T>
    where
        T: crate::api::Getable<'vm, 'value>,
    {
        self.get_variant(index).map(|v| T::from_value(thread, v))
    }

    pub fn insert_slice(&mut self, index: VmIndex, values: &[Value]) {
        let index = (self.offset() + index) as usize;
        // SAFETY the values get inserted to the stack
        unsafe {
            self.stack
                .values
                .splice(index..index, values.iter().map(|v| v.clone_unrooted()));
        }
    }

    pub fn remove_range(&mut self, from: VmIndex, to: VmIndex) {
        let offset = self.offset();
        self.stack.remove_range(offset + from, offset + to);
    }

    pub fn excess_args(&self) -> Option<&GcPtr<DataStruct>> {
        let i = self.stack.values.len() - self.len() as usize - 2;
        match self.stack.values[i].get_repr() {
            ValueRepr::Data(data) => Some(data),
            _ => None,
        }
    }

    pub(crate) fn enter_scope<T>(self, args: VmIndex, state: &T) -> StackFrame<'b, T>
    where
        T: StackState,
    {
        let stack = self.take_stack();
        Self::add_new_frame(stack, args, T::to_state(state));
        StackFrame {
            stack,
            _frame: PhantomData,
        }
    }

    pub(crate) fn exit_scope(self) -> Result<StackFrame<'b, State>, &'b mut Stack>
    where
        S: StackState,
    {
        if let State::Extern(ref ext) = *S::to_state(self.frame().state) {
            if ext.is_locked() {
                return Err(self.take_stack());
            }
        }
        let stack = self.take_stack();
        stack.frames.pop().expect("Expected frame");
        match stack.frames.last() {
            Some(_frame) => {
                let stack = StackFrame {
                    stack,
                    _frame: PhantomData,
                };
                debug!(
                    "<---- Restore {} {:?}",
                    stack.stack.frames.len(),
                    stack.frame()
                );
                Ok(stack)
            }
            None => Err(stack),
        }
    }

    pub(crate) fn current(stack: &mut Stack) -> StackFrame<S>
    where
        S: StackState,
    {
        stack.current_frame()
    }

    fn add_new_frame<'gc>(
        stack: &mut Stack,
        args: VmIndex,
        state: gc::Borrow<'gc, State>,
    ) -> gc::Borrow<'gc, Frame> {
        assert!(stack.len() >= args);
        let offset = stack.len() - args;
        let frame = construct_gc!(Frame {
            offset,
            @state,
            excess: false,
        });
        // Panic if the frame attempts to take ownership past the current frame
        if let Some(frame) = stack.frames.last() {
            assert!(frame.offset <= offset);
            if let State::Extern(ExternState {
                locked: Some(locked_args),
                ..
            }) = *State::to_state(&frame.state)
            {
                assert!(
                    frame.offset + locked_args <= offset,
                    "Attempt to add new frame that covers a locked frame"
                );
            }
        }
        // SAFETY The frame's gc pointers are scanned the `Stack::trace` since they are on
        // the stack
        unsafe {
            stack.frames.push(frame.clone_unrooted());
        }
        debug!("----> Store {} {:?}", stack.frames.len(), frame,);
        frame
    }
}

impl<'b> StackFrame<'b, ClosureState> {
    pub fn get_upvar(&self, index: VmIndex) -> Variants {
        Variants::new(&self.frame().upvars()[index as usize])
    }
}

impl<'b, S> Deref for StackFrame<'b, S>
where
    S: StackState,
{
    type Target = [Value];
    fn deref(&self) -> &[Value] {
        let offset = self.offset();
        &self.stack.values[offset as usize..]
    }
}

impl<'b, S> DerefMut for StackFrame<'b, S>
where
    S: StackState,
{
    fn deref_mut(&mut self) -> &mut [Value] {
        let offset = self.offset();
        &mut self.stack.values[offset as usize..]
    }
}

impl<'b, S> Index<VmIndex> for StackFrame<'b, S>
where
    S: StackState,
{
    type Output = Value;
    fn index(&self, index: VmIndex) -> &Value {
        let offset = self.offset();
        &self.stack.values[(offset + index) as usize]
    }
}
impl<'b, S> IndexMut<VmIndex> for StackFrame<'b, S>
where
    S: StackState,
{
    fn index_mut(&mut self, index: VmIndex) -> &mut Value {
        let offset = self.offset();
        &mut self.stack.values[(offset + index) as usize]
    }
}
impl<'b, S> Index<RangeFull> for StackFrame<'b, S>
where
    S: StackState,
{
    type Output = [Value];
    fn index(&self, _: RangeFull) -> &[Value] {
        let offset = self.offset();
        &self.stack.values[offset as usize..]
    }
}
impl<'b, S> IndexMut<RangeFull> for StackFrame<'b, S>
where
    S: StackState,
{
    fn index_mut(&mut self, _: RangeFull) -> &mut [Value] {
        let offset = self.offset();
        &mut self.stack.values[offset as usize..]
    }
}
impl<'b, S> Index<Range<VmIndex>> for StackFrame<'b, S>
where
    S: StackState,
{
    type Output = [Value];
    fn index(&self, range: Range<VmIndex>) -> &[Value] {
        let offset = self.offset();
        &self.stack.values[(range.start + offset) as usize..(range.end + offset) as usize]
    }
}
impl<'b, S> IndexMut<Range<VmIndex>> for StackFrame<'b, S>
where
    S: StackState,
{
    fn index_mut(&mut self, range: Range<VmIndex>) -> &mut [Value] {
        let offset = self.offset();
        &mut self.stack.values[(range.start + offset) as usize..(range.end + offset) as usize]
    }
}
impl<'b, S> Index<RangeTo<VmIndex>> for StackFrame<'b, S>
where
    S: StackState,
{
    type Output = [Value];
    fn index(&self, range: RangeTo<VmIndex>) -> &[Value] {
        let offset = self.offset();
        &self.stack.values[..(range.end + offset) as usize]
    }
}
impl<'b, S> IndexMut<RangeTo<VmIndex>> for StackFrame<'b, S>
where
    S: StackState,
{
    fn index_mut(&mut self, range: RangeTo<VmIndex>) -> &mut [Value] {
        let offset = self.offset();
        &mut self.stack.values[..(range.end + offset) as usize]
    }
}
impl<'b, S> Index<RangeFrom<VmIndex>> for StackFrame<'b, S>
where
    S: StackState,
{
    type Output = [Value];
    fn index(&self, range: RangeFrom<VmIndex>) -> &[Value] {
        let offset = self.offset();
        &self.stack.values[(range.start + offset) as usize..]
    }
}
impl<'b, S> IndexMut<RangeFrom<VmIndex>> for StackFrame<'b, S>
where
    S: StackState,
{
    fn index_mut(&mut self, range: RangeFrom<VmIndex>) -> &mut [Value] {
        let offset = self.offset();
        &mut self.stack.values[(range.start + offset) as usize..]
    }
}

impl<'c, T> Extend<&'c T> for Stack
where
    T: StackPrimitive + 'c,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'c T>,
    {
        T::extend_to(iter, self)
    }
}

impl<'b, 'c, T, S> Extend<&'c T> for StackFrame<'b, S>
where
    T: StackPrimitive + 'c,
    S: StackState,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'c T>,
    {
        T::extend_to(iter, &mut self.stack)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct StacktraceFrame {
    pub name: Symbol,
    pub line: Option<Line>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Stacktrace {
    pub frames: Vec<Option<StacktraceFrame>>,
}

impl fmt::Display for Stacktrace {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Stacktrace:\n")?;
        for (i, frame) in self.frames.iter().enumerate() {
            match *frame {
                Some(ref frame) => {
                    write!(f, "{}: {}", i, frame.name.declared_name())?;
                    if let Some(line) = frame.line {
                        write!(f, ":Line {}", line.number())?;
                    }
                    writeln!(f)
                }
                None => writeln!(f, "{}: <unknown>", i),
            }?
        }
        Ok(())
    }
}

pub struct PopValue<'a>(&'a mut Stack, Variants<'a>);

impl<'a> Drop for PopValue<'a> {
    fn drop(&mut self) {
        self.0.pop();
    }
}

impl<'a> Deref for PopValue<'a> {
    type Target = Variants<'a>;
    fn deref(&self) -> &Self::Target {
        &self.1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::base::symbol::Symbol;
    use crate::gc::{Gc, Move};
    use crate::thread::{Status, Thread};
    use crate::value::ValueRepr::*;

    fn dummy_extern() -> ExternFunction {
        extern "C" fn function(_: &Thread) -> Status {
            unreachable!()
        }
        ExternFunction {
            id: Symbol::from(""),
            args: 0,
            function,
        }
    }

    #[test]
    fn remove_range() {
        let _ = ::env_logger::try_init();

        let mut stack = Stack::new();
        let mut frame = StackFrame::frame(&mut stack, 0, State::Unknown);
        frame.push(Int(0));
        frame.push(Int(1));

        frame = frame.enter_scope(2, State::Unknown);
        frame.push(Int(2));
        frame.push(Int(3));

        frame = frame.enter_scope(1, State::Unknown);
        frame.push(Int(4));
        frame.push(Int(5));
        frame.push(Int(6));

        frame = frame.exit_scope().unwrap();
        frame.remove_range(2, 5);
        assert_eq!(
            frame.stack.values,
            vec![Int(0).into(), Int(1).into(), Int(5).into(), Int(6).into()]
        );

        frame = frame.exit_scope().unwrap();
        frame.remove_range(1, 3);
        assert_eq!(frame.stack.values, vec![Int(0).into(), Int(6).into()]);
    }

    #[test]
    #[should_panic]
    fn attempt_take_locked_range() {
        let _ = ::env_logger::try_init();

        let mut gc = Gc::new(Default::default(), 1024);
        let ext = gc.alloc_ignore_limit(Move(dummy_extern()));

        let mut stack = Stack::new();
        {
            let mut frame = StackFrame::frame(&mut stack, 0, State::Unknown);
            frame.push(Int(0));
            frame.push(Int(1));
            let frame = frame.enter_scope(2, ExternState::new(ext));
            let _lock = frame.into_lock();
        }
        // Panic as it attempts to access past the lock
        StackFrame::frame(&mut stack, 1, State::Unknown);

        unsafe { gc.clear() }
    }

    #[test]
    #[should_panic]
    fn attempt_pop_locked() {
        let _ = ::env_logger::try_init();

        let mut gc = Gc::new(Default::default(), 1024);
        let ext = gc.alloc_ignore_limit(Move(dummy_extern()));

        let mut stack = Stack::new();
        {
            let mut frame = StackFrame::frame(&mut stack, 0, State::Unknown);
            frame.push(Int(0));
            let frame = frame.enter_scope(1, ExternState::new(ext));
            let _lock = frame.into_lock();
        }
        // Panic as it attempts to pop a locked value
        stack.pop();

        unsafe { gc.clear() }
    }

    #[test]
    fn lock_unlock() {
        let _ = ::env_logger::try_init();

        let mut gc = Gc::new(Default::default(), 1024);
        let ext = gc.alloc_ignore_limit(Move(dummy_extern()));

        let mut stack = Stack::new();
        let lock = {
            let mut frame = StackFrame::frame(&mut stack, 0, State::Unknown);
            frame.push(Int(0));
            frame.push(Int(1));
            let frame = frame.enter_scope(2, ExternState::new(ext));
            frame.into_lock()
        };
        {
            let mut frame = StackFrame::frame(&mut stack, 0, State::Unknown);
            frame.push(Int(2));
            frame = frame.exit_scope().unwrap();
            frame.exit_scope().unwrap_err();
        }
        stack.release_lock(lock);
        let mut frame = StackFrame::<State>::current(&mut stack);
        assert_eq!(frame.pop(), Value::from(Int(2)));

        unsafe { gc.clear() }
    }

    #[test]
    fn insert_stack_slice() {
        let _ = ::env_logger::try_init();

        let mut stack = Stack::new();
        StackFrame::frame(&mut stack, 0, State::Unknown);
        let mut stack = StackFrame::<State>::current(&mut stack);
        stack.push(Int(0));
        stack.insert_slice(0, &[Int(2).into(), Int(1).into()]);
        assert_eq!(&stack[..], [Int(2).into(), Int(1).into(), Int(0).into()]);
        stack = stack.enter_scope(2, State::Unknown);
        stack.insert_slice(1, &[Int(10).into()]);
        assert_eq!(&stack[..], [Int(1).into(), Int(10).into(), Int(0).into()]);
        stack.insert_slice(1, &[]);
        assert_eq!(&stack[..], [Int(1).into(), Int(10).into(), Int(0).into()]);
        stack.insert_slice(2, &[Int(4).into(), Int(5).into(), Int(6).into()]);
        assert_eq!(
            &stack[..],
            [
                Int(1).into(),
                Int(10).into(),
                Int(4).into(),
                Int(5).into(),
                Int(6).into(),
                Int(0).into()
            ]
        );
    }
}
