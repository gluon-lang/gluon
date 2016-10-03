use std::fmt;
use std::ops::{Deref, DerefMut, Index, IndexMut, Range, RangeTo, RangeFrom, RangeFull};

use base::symbol::Symbol;

use Variants;
use gc::GcPtr;
use value::{ClosureData, Value, DataStruct, ExternFunction};
use types::VmIndex;

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
    pub offset: VmIndex,
    pub instruction_index: usize,
    pub state: State,
    pub excess: bool,
}

#[derive(Debug)]
pub struct Lock(VmIndex);

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

    pub fn remove_range(&mut self, from: VmIndex, to: VmIndex) {
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

    pub fn len(&self) -> VmIndex {
        self.values.len() as VmIndex
    }

    pub fn get_values(&self) -> &[Value] {
        &self.values
    }

    pub fn get_frames(&self) -> &[Frame] {
        &self.frames
    }

    pub fn current_frame(&mut self) -> StackFrame {
        StackFrame {
            frame: self.get_frames().last().expect("Frame").clone(),
            stack: self,
        }
    }

    /// Release a lock on the stack.
    ///
    /// Panics if the lock is not the top-most lock
    pub fn release_lock(&mut self, lock: Lock) {
        assert!(self.frames.pop().map(|frame| frame.offset) == Some(lock.0));
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

pub struct StackFrame<'b> {
    pub stack: &'b mut Stack,
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
    pub fn take_stack(mut self) -> &'b mut Stack {
        *self.stack.frames.last_mut().unwrap() = self.frame;
        self.stack
    }

    pub fn len(&self) -> VmIndex {
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

    pub fn get_variants(&self, index: VmIndex) -> Option<Variants> {
        if index < self.len() {
            Some(Variants(&self[index]))
        } else {
            None
        }
    }

    pub fn insert_slice(&mut self, index: VmIndex, values: &[Value]) {
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

    pub fn remove_range(&mut self, from: VmIndex, to: VmIndex) {
        self.stack.remove_range(self.frame.offset + from, self.frame.offset + to);
    }

    pub fn get_rooted_value(&self, index: VmIndex) -> Value {
        self[index]
    }

    pub fn get_upvar(&self, index: VmIndex) -> Value {
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

    pub fn enter_scope(&mut self, args: VmIndex, state: State) {
        if let Some(frame) = self.stack.frames.last_mut() {
            *frame = self.frame;
        }
        let frame = StackFrame::add_new_frame(&mut self.stack, args, state);
        self.frame = frame;
    }

    pub fn exit_scope(&mut self) -> Result<(), ()> {
        let current_frame = self.stack.frames.pop().expect("Expected frame");
        // The root frame should always exist
        debug_assert!(!self.stack.frames.is_empty(), "Poped the last frame");
        assert!(current_frame.offset == self.frame.offset,
                "Attempted to exit a scope other than the top-most scope");
        let frame = self.stack
            .frames
            .last()
            .cloned();
        match frame {
            Some(frame) => {
                self.frame = frame;
                if frame.state == State::Lock {
                    // Locks must be unlocked manually using release lock
                    Err(())
                } else {
                    debug!("<---- Restore {} {:?}", self.stack.frames.len(), frame);
                    Ok(())
                }
            }
            None => Err(()),
        }
    }

    pub fn frame(stack: &'b mut Stack, args: VmIndex, state: State) -> StackFrame<'b> {
        let frame = StackFrame::add_new_frame(stack, args, state);
        StackFrame {
            stack: stack,
            frame: frame,
        }
    }

    pub fn current(stack: &mut Stack) -> StackFrame {
        stack.current_frame()
    }

    /// Lock the stack below the current offset
    pub fn into_lock(mut self) -> Lock {
        let offset = self.stack.len();
        self.frame = StackFrame::add_new_frame(&mut self.stack, 0, State::Lock);
        Lock(offset)
    }

    /// Creates a stackrace starting from `frame_level`
    pub fn stacktrace(&self, frame_level: usize) -> Stacktrace {
        let frames = self.stack.get_frames()[frame_level..]
            .iter()
            .filter_map(|frame| {
                match frame.state {
                    State::Closure(ref closure) => Some(Some(closure.function.name.clone())),
                    State::Extern(ref ext) => Some(Some(ext.id.clone())),
                    State::Unknown => Some(None),
                    State::Lock | State::Excess => None,
                }
            })
            .collect();
        Stacktrace { frames: frames }
    }

    fn add_new_frame(stack: &mut Stack, args: VmIndex, state: State) -> Frame {
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

impl<'b> Index<VmIndex> for StackFrame<'b> {
    type Output = Value;
    fn index(&self, index: VmIndex) -> &Value {
        &self.stack.values[(self.frame.offset + index) as usize]
    }
}
impl<'b> IndexMut<VmIndex> for StackFrame<'b> {
    fn index_mut(&mut self, index: VmIndex) -> &mut Value {
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
impl<'b> Index<Range<VmIndex>> for StackFrame<'b> {
    type Output = [Value];
    fn index(&self, range: Range<VmIndex>) -> &[Value] {
        let offset = self.frame.offset;
        &self.stack.values[(range.start + offset) as usize..(range.end + offset) as usize]
    }
}
impl<'b> IndexMut<Range<VmIndex>> for StackFrame<'b> {
    fn index_mut(&mut self, range: Range<VmIndex>) -> &mut [Value] {
        let offset = self.frame.offset;
        &mut self.stack.values[(range.start + offset) as usize..(range.end + offset) as usize]
    }
}
impl<'b> Index<RangeTo<VmIndex>> for StackFrame<'b> {
    type Output = [Value];
    fn index(&self, range: RangeTo<VmIndex>) -> &[Value] {
        &self.stack.values[..(range.end + self.frame.offset) as usize]
    }
}
impl<'b> IndexMut<RangeTo<VmIndex>> for StackFrame<'b> {
    fn index_mut(&mut self, range: RangeTo<VmIndex>) -> &mut [Value] {
        &mut self.stack.values[..(range.end + self.frame.offset) as usize]
    }
}
impl<'b> Index<RangeFrom<VmIndex>> for StackFrame<'b> {
    type Output = [Value];
    fn index(&self, range: RangeFrom<VmIndex>) -> &[Value] {
        &self.stack.values[(range.start + self.frame.offset) as usize..]
    }
}
impl<'b> IndexMut<RangeFrom<VmIndex>> for StackFrame<'b> {
    fn index_mut(&mut self, range: RangeFrom<VmIndex>) -> &mut [Value] {
        &mut self.stack.values[(range.start + self.frame.offset) as usize..]
    }
}

#[derive(Debug)]
pub struct Stacktrace {
    frames: Vec<Option<Symbol>>,
}

impl fmt::Display for Stacktrace {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(writeln!(f, "Stacktrace:\n"));
        for (i, frame) in self.frames.iter().enumerate() {
            let name = frame.as_ref().map_or("<unknown>", |frame| frame.as_ref());
            try!(writeln!(f, "{}: {}", i, name));
        }
        Ok(())
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use value::Value::*;

    #[test]
    fn remove_range() {
        let _ = ::env_logger::init();

        let mut stack = Stack::new();
        let mut frame = StackFrame::frame(&mut stack, 0, State::Unknown);
        frame.push(Int(0));
        frame.push(Int(1));

        frame.enter_scope(2, State::Unknown);
        frame.push(Int(2));
        frame.push(Int(3));

        frame.enter_scope(1, State::Unknown);
        frame.push(Int(4));
        frame.push(Int(5));
        frame.push(Int(6));

        frame.exit_scope().unwrap();
        frame.remove_range(2, 5);
        assert_eq!(frame.stack.values, vec![Int(0), Int(1), Int(5), Int(6)]);

        frame.exit_scope().unwrap();
        frame.remove_range(1, 3);
        assert_eq!(frame.stack.values, vec![Int(0), Int(6)]);
    }

    #[test]
    #[should_panic]
    fn attempt_take_locked_range() {
        let _ = ::env_logger::init();

        let mut stack = Stack::new();
        {
            let mut frame = StackFrame::frame(&mut stack, 0, State::Unknown);
            frame.push(Int(0));
            frame.push(Int(1));
            frame.enter_scope(2, State::Unknown);
            let _lock = frame.into_lock();
        }
        // Panic as it attempts to access past the lock
        StackFrame::frame(&mut stack, 1, State::Unknown);
    }

    #[test]
    fn lock_unlock() {
        let _ = ::env_logger::init();

        let mut stack = Stack::new();
        let lock = {
            let mut frame = StackFrame::frame(&mut stack, 0, State::Unknown);
            frame.push(Int(0));
            frame.push(Int(1));
            frame.enter_scope(2, State::Unknown);
            frame.into_lock()
        };
        {
            let mut frame = StackFrame::frame(&mut stack, 0, State::Unknown);
            frame.push(Int(2));
            frame.exit_scope().unwrap_err();
        }
        stack.release_lock(lock);
        let mut frame = StackFrame::current(&mut stack);
        assert_eq!(frame.pop(), Int(2));
    }
}
