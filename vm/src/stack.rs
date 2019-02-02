use std::{
    fmt,
    ops::{Deref, DerefMut, Index, IndexMut, Range, RangeFrom, RangeFull, RangeTo},
};

use crate::base::pos::Line;
use crate::base::symbol::Symbol;

use crate::gc::{Gc, GcPtr, Traverseable};
use crate::types::VmIndex;
use crate::value::{ClosureData, DataStruct, ExternFunction, Value, ValueRepr};
use crate::Variants;

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
        stack
            .values
            .extend(iter.into_iter().map(|i| Value::from(i.0)))
    }
}

impl StackPrimitive for ValueRepr {
    #[inline(always)]
    fn push_to(&self, stack: &mut Stack) {
        stack.values.push(Value::from(*self))
    }

    fn extend_to<'b, I>(iter: I, stack: &mut Stack)
    where
        I: IntoIterator<Item = &'b Self>,
    {
        stack
            .values
            .extend(iter.into_iter().map(|i| Value::from(*i)))
    }
}

impl StackPrimitive for Value {
    #[inline(always)]
    fn push_to(&self, stack: &mut Stack) {
        stack.values.push(Value::from(self.get_repr()))
    }

    fn extend_to<'b, I>(iter: I, stack: &mut Stack)
    where
        I: IntoIterator<Item = &'b Self>,
    {
        stack
            .values
            .extend(iter.into_iter().map(|i| Value::from(i.get_repr())))
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive",
    serde(deserialize_state = "crate::serialization::DeSeed")
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

#[derive(Copy, Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde_derive", derive(Deserialize, Serialize))]
pub(crate) enum ExternCallState {
    Start,
    InPoll,
    Poll,
}

#[derive(Copy, Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive",
    serde(deserialize_state = "crate::serialization::DeSeed")
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

impl ExternState {
    pub fn new(function: GcPtr<ExternFunction>) -> Self {
        ExternState {
            function,
            call_state: ExternCallState::Start,
            locked: None,
        }
    }

    pub fn is_locked(&self) -> bool {
        self.locked.is_some()
    }
}

pub trait StackState: Copy {
    fn from_state(state: State) -> Self;
    fn to_state(self) -> State;
}

impl StackState for State {
    fn from_state(state: State) -> Self {
        state
    }
    fn to_state(self) -> State {
        self
    }
}

impl StackState for ClosureState {
    fn from_state(state: State) -> Self {
        match state {
            State::Closure(state) => state,
            _ => ice!("Expected closure: {:?}", state),
        }
    }
    fn to_state(self) -> State {
        State::Closure(self)
    }
}

impl StackState for ExternState {
    fn from_state(state: State) -> Self {
        match state {
            State::Extern(state) => state,
            _ => ice!("Expected extern: {:?}", state),
        }
    }
    fn to_state(self) -> State {
        State::Extern(self)
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive",
    serde(deserialize_state = "crate::serialization::DeSeed")
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

#[derive(Copy, Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive",
    serde(deserialize_state = "crate::serialization::DeSeed")
)]
#[cfg_attr(
    feature = "serde_derive",
    serde(bound(
        deserialize = "S: ::serde::de::DeserializeState<'de, crate::serialization::DeSeed>"
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

impl<S> Frame<S> {
    fn to_state(self) -> Frame<State>
    where
        S: StackState,
    {
        Frame {
            offset: self.offset,
            state: self.state.to_state(),
            excess: self.excess,
        }
    }
}

impl Frame<ClosureState> {
    pub fn upvars(&self) -> &[Value] {
        &self.state.closure.upvars
    }
}

impl Frame<State> {
    fn from_state<S>(self) -> Frame<S>
    where
        S: StackState,
    {
        Frame {
            offset: self.offset,
            state: S::from_state(self.state),
            excess: self.excess,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[must_use = "Unused locks will prevent the stack from unwinding"]
pub struct Lock(VmIndex);

#[derive(Debug)]
#[cfg_attr(feature = "serde_derive", derive(DeserializeState, SerializeState))]
#[cfg_attr(
    feature = "serde_derive",
    serde(deserialize_state = "crate::serialization::DeSeed")
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

impl Traverseable for Stack {
    fn traverse(&self, gc: &mut Gc) {
        self.values.traverse(gc);
    }
}

impl Stack {
    pub fn new() -> Stack {
        Stack {
            values: Vec::new(),
            frames: Vec::new(),
        }
    }

    pub fn pop(&mut self) -> Value {
        if let Some(&frame) = self.frames.last() {
            assert!(
                self.len() > frame.offset,
                "Attempted to pop value which did not belong to the current frame"
            );
            if let State::Extern(ExternState {
                locked: Some(args), ..
            }) = frame.state.to_state()
            {
                assert!(
                    self.len() > frame.offset + args,
                    "Attempt to pop locked value"
                );
            }
        }
        self.values.pop().expect("pop on empty stack")
    }

    pub fn pop_many(&mut self, count: VmIndex) {
        let len = self.values.len();
        self.values.truncate(len - count as usize);
    }

    pub fn clear(&mut self) {
        self.values.clear();
    }

    pub fn slide(&mut self, count: VmIndex) {
        let i = self.len() - 1 - count;
        self[i] = self.last().unwrap().get_value();
        self.pop_many(count);
    }

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
        unsafe {
            if index < self.len() {
                Some(Variants::new(&self.values[index as usize]))
            } else {
                None
            }
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
        StackFrame {
            frame: self
                .get_frames()
                .last()
                .expect("Frame")
                .clone()
                .from_state(),
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
    pub frame: Frame<S>,
}

impl<'b, S> Drop for StackFrame<'b, S>
where
    S: StackState,
{
    fn drop(&mut self) {
        // Move the cached frame back to storage
        self.store_frame();
    }
}

impl<'b, S> fmt::Debug for StackFrame<'b, S>
where
    S: fmt::Debug + StackState,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("StackFrame")
            .field("stack", &*self.stack)
            .field("frame", &self.frame)
            .finish()
    }
}

impl<'a: 'b, 'b> StackFrame<'b, State> {
    pub fn from_state<T>(self) -> StackFrame<'b, T>
    where
        T: StackState,
    {
        let frame = self.frame.from_state();
        let stack = self.take_stack();
        StackFrame { stack, frame }
    }

    pub fn frame(stack: &'b mut Stack, args: VmIndex, state: State) -> StackFrame<'b> {
        let frame = Self::add_new_frame(stack, args, state);
        StackFrame {
            stack: stack,
            frame: frame,
        }
    }
}

impl<'a: 'b, 'b> StackFrame<'b, ExternState> {
    /// Lock the stack below the current offset
    pub fn into_lock(mut self) -> Lock {
        self.frame.state.locked = Some(self.len());
        let lock = Lock(self.frame.offset);
        self.take_stack();
        lock
    }
}

impl<'a: 'b, 'b, S> StackFrame<'b, S>
where
    S: StackState,
{
    pub fn take_stack(self) -> &'b mut Stack
    where
        S: Copy,
    {
        *self.stack.frames.last_mut().unwrap() = self.frame.to_state();
        // We only recover the Stack reference after the drop has run here.
        // Since drop doesn't leak the reference this is safe
        unsafe {
            let stack: *mut Stack = self.stack;
            drop(self);
            &mut *stack
        }
    }

    pub fn len(&self) -> VmIndex {
        self.stack.len() - self.frame.offset
    }

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
        self.stack.get_variant(self.frame.offset + index)
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
        self.stack.values.reserve(values.len());
        unsafe {
            let old_len = self.len();
            for i in (index..old_len).rev() {
                *self.get_unchecked_mut(i as usize + values.len()) = self[i].clone();
            }
            for (i, val) in (index..).zip(values) {
                *self.get_unchecked_mut(i as usize) = val.clone();
            }
            let new_len = self.stack.values.len() + values.len();
            self.stack.values.set_len(new_len);
        }
    }

    pub fn remove_range(&mut self, from: VmIndex, to: VmIndex) {
        self.stack
            .remove_range(self.frame.offset + from, self.frame.offset + to);
    }

    pub fn excess_args(&self) -> Option<GcPtr<DataStruct>> {
        let i = self.stack.values.len() - self.len() as usize - 2;
        match self.stack.values[i].get_repr() {
            ValueRepr::Data(data) => Some(data),
            _ => None,
        }
    }

    pub(crate) fn enter_scope<T>(self, args: VmIndex, state: T) -> StackFrame<'b, T>
    where
        T: StackState,
        S: Copy,
    {
        let stack = self.take_stack();
        let frame = Self::add_new_frame(stack, args, state.to_state());

        StackFrame {
            stack,
            frame: frame.from_state(),
        }
    }

    pub(crate) fn exit_scope(self) -> Result<StackFrame<'b, State>, &'b mut Stack>
    where
        S: StackState + Copy,
    {
        if let State::Extern(ref ext) = self.frame.state.to_state() {
            if ext.is_locked() {
                return Err(self.take_stack());
            }
        }
        let frame = self.frame;
        let stack = self.take_stack();
        let current_frame = stack.frames.pop().expect("Expected frame");
        // The root frame should always exist
        debug_assert!(!stack.frames.is_empty(), "Poped the last frame");
        assert!(
            current_frame.offset == frame.offset,
            "Attempted to exit a scope other than the top-most scope"
        );
        let frame = stack.frames.last().cloned();
        match frame {
            Some(frame) => {
                let stack = StackFrame {
                    stack,
                    frame: frame.from_state(),
                };
                debug!("<---- Restore {} {:?}", stack.stack.frames.len(), frame);
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

    fn add_new_frame(stack: &mut Stack, args: VmIndex, state: State) -> Frame {
        assert!(stack.len() >= args);
        let prev = stack.frames.last().cloned();
        let offset = stack.len() - args;
        let frame = Frame {
            offset,
            state,
            excess: false,
        };
        // Panic if the frame attempts to take ownership past the current frame
        if let Some(frame) = stack.frames.last() {
            assert!(frame.offset <= offset);
            if let State::Extern(ExternState {
                locked: Some(locked_args),
                ..
            }) = frame.state.to_state()
            {
                assert!(
                    frame.offset + locked_args <= offset,
                    "Attempt to add new frame that covers a locked frame"
                );
            }
        }
        stack.frames.push(frame);
        debug!(
            "----> Store {} {:?}\n||| {:?}",
            stack.frames.len(),
            frame,
            prev
        );
        frame
    }

    pub fn store_frame(&mut self)
    where
        S: StackState + Copy,
    {
        let last_frame = self.stack.frames.last_mut().unwrap();
        let frame = self.frame.to_state();
        use self::State::*;
        debug_assert!(match (&last_frame.state, &frame.state) {
            (Unknown, Unknown) => true,
            (Closure(_), Closure(_)) => true,
            (Extern(_), Extern(_)) => true,
            _ => false,
        });
        *last_frame = frame;
    }
}

impl<'b> StackFrame<'b, ClosureState> {
    pub fn get_upvar(&self, index: VmIndex) -> &Value {
        &self.frame.upvars()[index as usize]
    }
}

impl<'b, S> Deref for StackFrame<'b, S>
where
    S: StackState,
{
    type Target = [Value];
    fn deref(&self) -> &[Value] {
        &self.stack.values[self.frame.offset as usize..]
    }
}

impl<'b, S> DerefMut for StackFrame<'b, S>
where
    S: StackState,
{
    fn deref_mut(&mut self) -> &mut [Value] {
        &mut self.stack.values[self.frame.offset as usize..]
    }
}

impl<'b, S> Index<VmIndex> for StackFrame<'b, S>
where
    S: StackState,
{
    type Output = Value;
    fn index(&self, index: VmIndex) -> &Value {
        &self.stack.values[(self.frame.offset + index) as usize]
    }
}
impl<'b, S> IndexMut<VmIndex> for StackFrame<'b, S>
where
    S: StackState,
{
    fn index_mut(&mut self, index: VmIndex) -> &mut Value {
        &mut self.stack.values[(self.frame.offset + index) as usize]
    }
}
impl<'b, S> Index<RangeFull> for StackFrame<'b, S>
where
    S: StackState,
{
    type Output = [Value];
    fn index(&self, _: RangeFull) -> &[Value] {
        &self.stack.values[self.frame.offset as usize..]
    }
}
impl<'b, S> IndexMut<RangeFull> for StackFrame<'b, S>
where
    S: StackState,
{
    fn index_mut(&mut self, _: RangeFull) -> &mut [Value] {
        &mut self.stack.values[self.frame.offset as usize..]
    }
}
impl<'b, S> Index<Range<VmIndex>> for StackFrame<'b, S>
where
    S: StackState,
{
    type Output = [Value];
    fn index(&self, range: Range<VmIndex>) -> &[Value] {
        let offset = self.frame.offset;
        &self.stack.values[(range.start + offset) as usize..(range.end + offset) as usize]
    }
}
impl<'b, S> IndexMut<Range<VmIndex>> for StackFrame<'b, S>
where
    S: StackState,
{
    fn index_mut(&mut self, range: Range<VmIndex>) -> &mut [Value] {
        let offset = self.frame.offset;
        &mut self.stack.values[(range.start + offset) as usize..(range.end + offset) as usize]
    }
}
impl<'b, S> Index<RangeTo<VmIndex>> for StackFrame<'b, S>
where
    S: StackState,
{
    type Output = [Value];
    fn index(&self, range: RangeTo<VmIndex>) -> &[Value] {
        &self.stack.values[..(range.end + self.frame.offset) as usize]
    }
}
impl<'b, S> IndexMut<RangeTo<VmIndex>> for StackFrame<'b, S>
where
    S: StackState,
{
    fn index_mut(&mut self, range: RangeTo<VmIndex>) -> &mut [Value] {
        &mut self.stack.values[..(range.end + self.frame.offset) as usize]
    }
}
impl<'b, S> Index<RangeFrom<VmIndex>> for StackFrame<'b, S>
where
    S: StackState,
{
    type Output = [Value];
    fn index(&self, range: RangeFrom<VmIndex>) -> &[Value] {
        &self.stack.values[(range.start + self.frame.offset) as usize..]
    }
}
impl<'b, S> IndexMut<RangeFrom<VmIndex>> for StackFrame<'b, S>
where
    S: StackState,
{
    fn index_mut(&mut self, range: RangeFrom<VmIndex>) -> &mut [Value] {
        &mut self.stack.values[(range.start + self.frame.offset) as usize..]
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

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
pub struct StacktraceFrame {
    pub name: Symbol,
    pub line: Option<Line>,
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
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
