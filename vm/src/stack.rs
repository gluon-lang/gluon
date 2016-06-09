use std::fmt;
use std::sync::MutexGuard;
use std::ops::{Deref, DerefMut, Index, IndexMut, Range, RangeTo, RangeFrom, RangeFull};

use Variants;
use gc::GcPtr;
use vm::{ClosureData, Value, DataStruct, ExternFunction};
use types::VMIndex;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum State {
    Unknown,
    /// Locked frame which can only be unlocked by the caller which introduced the lock
    Lock,
    /// Extra frame introduced to store a call with excess arguments
    Excess,
    Closure(GcPtr<ClosureData>),
    Extern(GcPtr<ExternFunction>),
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Frame {
    pub offset: VMIndex,
    pub instruction_index: usize,
    pub state: State,
    pub excess: bool,
}

#[derive(Debug)]
pub struct Lock(VMIndex);

#[derive(Debug)]
pub struct Stack {
    values: Vec<Value>,
    frames: Vec<Frame>,
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
            assert!(self.len() > frame.offset,
                    "Attempted to pop value which did not belong to the current frame");
        }
        self.values
            .pop()
            .expect("pop on empty stack")
    }

    pub fn push(&mut self, v: Value) {
        self.values.push(v)
    }

    pub fn remove_range(&mut self, from: VMIndex, to: VMIndex) {
        let from = from as usize;
        let to = to as usize;
        let len = to - from;
        let mid = from + ::std::cmp::min(self.values.len() - to, len);
        for i in from..mid {
            self.values[i] = self.values[i + len];
        }
        for i in mid..(self.values.len() - len) {
            self.values[i] = self.values[i + len];
        }
        unsafe {
            let current_len = self.values.len();
            self.values.set_len(current_len - len as usize);
        }
    }

    pub fn len(&self) -> VMIndex {
        self.values.len() as VMIndex
    }

    pub fn get_values(&self) -> &[Value] {
        &self.values
    }

    pub fn get_frames(&self) -> &[Frame] {
        &self.frames
    }

    /// Release a lock on the stack.
    ///
    /// Panics if the lock is not the top-most lock
    pub fn release_lock(&mut self, lock: Lock) {
        assert!(self.frames.pop().map(|frame| frame.offset) == Some(lock.0));
    }
}

impl Index<VMIndex> for Stack {
    type Output = Value;
    fn index(&self, index: VMIndex) -> &Value {
        &self.values[index as usize]
    }
}

impl IndexMut<VMIndex> for Stack {
    fn index_mut(&mut self, index: VMIndex) -> &mut Value {
        &mut self.values[index as usize]
    }
}

impl Index<RangeFrom<VMIndex>> for Stack {
    type Output = [Value];
    fn index(&self, range: RangeFrom<VMIndex>) -> &[Value] {
        &self.values[range.start as usize..]
    }
}

impl Index<RangeTo<VMIndex>> for Stack {
    type Output = [Value];
    fn index(&self, range: RangeTo<VMIndex>) -> &[Value] {
        &self.values[..range.end as usize]
    }
}

pub struct StackFrame<'b> {
    pub stack: MutexGuard<'b, Stack>,
    pub frame: Frame,
}

impl<'b> Drop for StackFrame<'b> {
    fn drop(&mut self) {
        // Move the cached frame back to storage
        *self.stack.frames.last_mut().unwrap() = self.frame;
    }
}

impl<'b> fmt::Debug for StackFrame<'b> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("StackFrame")
         .field("stack", &*self.stack)
         .field("frame", &self.frame)
         .finish()
    }
}

impl<'a: 'b, 'b> StackFrame<'b> {
    pub fn len(&self) -> VMIndex {
        self.stack.len() - self.frame.offset
    }

    pub fn push(&mut self, v: Value) {
        self.stack.values.push(v);
    }

    pub fn top(&mut self) -> Value {
        *self.stack.values.last().expect("StackFrame: top")
    }

    pub fn pop(&mut self) -> Value {
        self.stack.pop()
    }

    pub fn get_variants(&self, index: VMIndex) -> Option<Variants> {
        if index < self.len() {
            Some(Variants(&self[index]))
        } else {
            None
        }
    }

    pub fn insert_slice(&mut self, index: VMIndex, values: &[Value]) {
        self.stack.values.reserve(values.len());
        unsafe {
            let old_len = self.len();
            for i in (index..old_len).rev() {
                *self.get_unchecked_mut(i as usize + values.len()) = self[i];
            }
            for (i, val) in (index..).zip(values) {
                *self.get_unchecked_mut(i as usize) = *val;
            }
            let new_len = self.stack.values.len() + values.len();
            self.stack.values.set_len(new_len);
        }
    }

    pub fn remove_range(&mut self, from: VMIndex, to: VMIndex) {
        self.stack.remove_range(self.frame.offset + from, self.frame.offset + to);
    }

    pub fn get_rooted_value(&self, index: VMIndex) -> Value {
        self[index]
    }

    pub fn get_upvar(&self, index: VMIndex) -> Value {
        let upvars = match self.frame.state {
            State::Closure(ref c) => c,
            _ => panic!("Attempted to access upvar in non closure function"),
        };
        upvars.upvars[index as usize]
    }

    pub fn excess_args(&self) -> Option<GcPtr<DataStruct>> {
        let i = self.stack.values.len() - self.len() as usize - 2;
        match self.stack.values[i] {
            Value::Data(data) => Some(data),
            _ => None,
        }
    }

    pub fn enter_scope(mut self, args: VMIndex, state: State) -> StackFrame<'b> {
        if let Some(frame) = self.stack.frames.last_mut() {
            *frame = self.frame;
        }
        let frame = StackFrame::add_new_frame(&mut self.stack, args, state);
        self.frame = frame;
        self
    }

    pub fn exit_scope(mut self) -> Option<StackFrame<'b>> {
        let current_frame = self.stack.frames.pop().expect("Expected frame");
        assert!(current_frame.offset == self.frame.offset,
                "Attempted to exit a scope other than the top-most scope");
        let frame = self.stack
                        .frames
                        .last()
                        .cloned();
        frame.and_then(move |frame| {
            self.frame = frame;
            if frame.state == State::Lock {
                // Locks must be unlocked manually using release lock
                None
            } else {
                debug!("<---- Restore {} {:?}", self.stack.frames.len(), frame);
                Some(self)
            }
        })
    }

    pub fn frame(mut stack: MutexGuard<'b, Stack>, args: VMIndex, state: State) -> StackFrame<'b> {
        let frame = StackFrame::add_new_frame(&mut stack, args, state);
        StackFrame {
            stack: stack,
            frame: frame,
        }
    }

    pub fn current(stack: MutexGuard<Stack>) -> StackFrame {
        StackFrame {
            frame: stack.get_frames().last().expect("Frame").clone(),
            stack: stack,
        }
    }

    /// Lock the stack below the current offset
    pub fn into_lock(mut self) -> Lock {
        let offset = self.stack.len();
        self.frame = StackFrame::add_new_frame(&mut self.stack, 0, State::Lock);
        Lock(offset)
    }

    fn add_new_frame(stack: &mut Stack, args: VMIndex, state: State) -> Frame {
        assert!(stack.len() >= args);
        let prev = stack.frames.last().cloned();
        let offset = stack.len() - args;
        let frame = Frame {
            offset: offset,
            instruction_index: 0,
            state: state,
            excess: false,
        };
        // Panic if the frame attempts to take ownership past the current frame
        if let Some(frame) = stack.frames.last() {
            assert!(frame.offset <= offset);
        }
        stack.frames.push(frame);
        debug!("----> Store {} {:?}\n||| {:?}",
               stack.frames.len(),
               frame,
               prev);
        frame
    }
}

impl<'b> Deref for StackFrame<'b> {
    type Target = [Value];
    fn deref(&self) -> &[Value] {
        &self.stack.values[self.frame.offset as usize..]
    }
}

impl<'b> DerefMut for StackFrame<'b> {
    fn deref_mut(&mut self) -> &mut [Value] {
        &mut self.stack.values[self.frame.offset as usize..]
    }
}

impl<'b> Index<VMIndex> for StackFrame<'b> {
    type Output = Value;
    fn index(&self, index: VMIndex) -> &Value {
        &self.stack.values[(self.frame.offset + index) as usize]
    }
}
impl<'b> IndexMut<VMIndex> for StackFrame<'b> {
    fn index_mut(&mut self, index: VMIndex) -> &mut Value {
        &mut self.stack.values[(self.frame.offset + index) as usize]
    }
}
impl<'b> Index<RangeFull> for StackFrame<'b> {
    type Output = [Value];
    fn index(&self, _: RangeFull) -> &[Value] {
        &self.stack.values[self.frame.offset as usize..]
    }
}
impl<'b> IndexMut<RangeFull> for StackFrame<'b> {
    fn index_mut(&mut self, _: RangeFull) -> &mut [Value] {
        &mut self.stack.values[self.frame.offset as usize..]
    }
}
impl<'b> Index<Range<VMIndex>> for StackFrame<'b> {
    type Output = [Value];
    fn index(&self, range: Range<VMIndex>) -> &[Value] {
        let offset = self.frame.offset;
        &self.stack.values[(range.start + offset) as usize..(range.end + offset) as usize]
    }
}
impl<'b> IndexMut<Range<VMIndex>> for StackFrame<'b> {
    fn index_mut(&mut self, range: Range<VMIndex>) -> &mut [Value] {
        let offset = self.frame.offset;
        &mut self.stack.values[(range.start + offset) as usize..(range.end + offset) as usize]
    }
}
impl<'b> Index<RangeTo<VMIndex>> for StackFrame<'b> {
    type Output = [Value];
    fn index(&self, range: RangeTo<VMIndex>) -> &[Value] {
        &self.stack.values[..(range.end + self.frame.offset) as usize]
    }
}
impl<'b> IndexMut<RangeTo<VMIndex>> for StackFrame<'b> {
    fn index_mut(&mut self, range: RangeTo<VMIndex>) -> &mut [Value] {
        &mut self.stack.values[..(range.end + self.frame.offset) as usize]
    }
}
impl<'b> Index<RangeFrom<VMIndex>> for StackFrame<'b> {
    type Output = [Value];
    fn index(&self, range: RangeFrom<VMIndex>) -> &[Value] {
        &self.stack.values[(range.start + self.frame.offset) as usize..]
    }
}
impl<'b> IndexMut<RangeFrom<VMIndex>> for StackFrame<'b> {
    fn index_mut(&mut self, range: RangeFrom<VMIndex>) -> &mut [Value] {
        &mut self.stack.values[(range.start + self.frame.offset) as usize..]
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Mutex;

    use super::*;
    use vm::Value::*;

    #[test]
    fn remove_range() {
        let _ = ::env_logger::init();

        let stack = Mutex::new(Stack::new());
        let stack = stack.lock().unwrap();
        let mut frame = StackFrame::frame(stack, 0, State::Unknown);
        frame.push(Int(0));
        frame.push(Int(1));
        let mut frame = frame.enter_scope(2, State::Unknown);
        frame.push(Int(2));
        frame.push(Int(3));
        frame = frame.enter_scope(1, State::Unknown);
        frame.push(Int(4));
        frame.push(Int(5));
        frame.push(Int(6));
        frame = frame.exit_scope().unwrap();
        frame.remove_range(2, 5);
        assert_eq!(frame.stack.values, vec![Int(0), Int(1), Int(5), Int(6)]);
        frame = frame.exit_scope().unwrap();
        frame.remove_range(1, 3);
        assert_eq!(frame.stack.values, vec![Int(0), Int(6)]);
    }

    #[test]
    #[should_panic]
    fn attempt_take_locked_range() {
        let _ = ::env_logger::init();

        let stack = Mutex::new(Stack::new());
        let mut frame = StackFrame::frame(stack.lock().unwrap(), 0, State::Unknown);
        frame.push(Int(0));
        frame.push(Int(1));
        let frame = frame.enter_scope(2, State::Unknown);
        let _lock = frame.into_lock();
        // Panic as it attempts to access past the lock
        StackFrame::frame(stack.lock().unwrap(), 1, State::Unknown);
    }

    #[test]
    fn lock_unlock() {
        let _ = ::env_logger::init();

        let stack = Mutex::new(Stack::new());
        let mut frame = StackFrame::frame(stack.lock().unwrap(), 0, State::Unknown);
        frame.push(Int(0));
        frame.push(Int(1));
        frame = frame.enter_scope(2, State::Unknown);
        let lock = frame.into_lock();
        frame = StackFrame::frame(stack.lock().unwrap(), 0, State::Unknown);
        frame.push(Int(2));
        frame.exit_scope();
        stack.lock().unwrap().release_lock(lock);
        frame = StackFrame::current(stack.lock().unwrap());
        assert_eq!(frame.pop(), Int(2));
    }
}
