use std::cell::{Cell, RefMut};
use std::ops::{Deref, DerefMut, Index, IndexMut, Range, RangeTo, RangeFrom, RangeFull};

use vm::{Callable, Value};
use types::VMIndex;

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Frame<'a> {
    pub offset: VMIndex,
    pub instruction_index: usize,
    pub function: Option<Callable<'a>>,
    pub excess: bool,
}

#[derive(Debug)]
pub struct Stack<'a> {
    pub values: Vec<Value<'a>>,
    pub frames: Vec<Frame<'a>>,
}

impl<'a> Stack<'a> {
    pub fn new() -> Stack<'a> {
        Stack {
            values: Vec::new(),
            frames: Vec::new(),
        }
    }

    pub fn pop(&mut self) -> Value<'a> {
        self.values
            .pop()
            .expect("pop on empty stack")
    }

    pub fn push(&mut self, v: Value<'a>) {
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
}

#[derive(Debug)]
pub struct StackFrame<'a: 'b, 'b> {
    pub stack: RefMut<'b, Stack<'a>>,
    pub frame: Frame<'a>,
}

impl<'a, 'b> Drop for StackFrame<'a, 'b> {
    fn drop(&mut self) {
        // Move the cached frame back to storage
        *self.stack.frames.last_mut().unwrap() = self.frame;
    }
}

impl<'a: 'b, 'b> StackFrame<'a, 'b> {
    pub fn len(&self) -> VMIndex {
        self.stack.len() - self.frame.offset
    }

    pub fn push(&mut self, v: Value<'a>) {
        self.stack.values.push(v);
    }

    pub fn top(&mut self) -> Value<'a> {
        *self.stack.values.last().expect("StackFrame: top")
    }

    pub fn pop(&mut self) -> Value<'a> {
        self.stack.pop()
    }

    pub fn insert_slice(&mut self, index: VMIndex, values: &[Cell<Value<'a>>]) {
        self.stack.values.reserve(values.len());
        unsafe {
            let old_len = self.len();
            for i in (index..old_len).rev() {
                *self.get_unchecked_mut(i as usize + values.len()) = self[i];
            }
            for (i, val) in (index..).zip(values) {
                *self.get_unchecked_mut(i as usize) = val.get();
            }
            let new_len = self.stack.values.len() + values.len();
            self.stack.values.set_len(new_len);
        }
    }

    pub fn remove_range(&mut self, from: VMIndex, to: VMIndex) {
        self.stack.remove_range(self.frame.offset + from, self.frame.offset + to);
    }

    pub fn get_upvar(&self, index: VMIndex) -> Value<'a> {
        let upvars = match self.frame.function {
            Some(Callable::Closure(ref c)) => c,
            _ => panic!("Attempted to access upvar in non closure function"),
        };
        upvars.upvars[index as usize].get()
    }

    pub fn enter_scope(mut self,
                       args: VMIndex,
                       function: Option<Callable<'a>>)
                       -> StackFrame<'a, 'b> {
        if let Some(frame) = self.stack.frames.last_mut() {
            *frame = self.frame;
        }
        let frame = StackFrame::add_new_frame(&mut self.stack, args, function);
        self.frame = frame;
        self
    }

    pub fn exit_scope(mut self) -> Option<StackFrame<'a, 'b>> {
        self.stack.frames.pop().expect("Expected frame");
        let frame = self.stack
                        .frames
                        .last()
                        .cloned();
        frame.map(move |frame| {
            debug!("<---- Restore {} {:?}", self.stack.frames.len(), frame);
            self.frame = frame;
            self
        })
    }

    pub fn frame(mut stack: RefMut<'b, Stack<'a>>,
                 args: VMIndex,
                 function: Option<Callable<'a>>)
                 -> StackFrame<'a, 'b> {
        let frame = StackFrame::add_new_frame(&mut stack, args, function);
        StackFrame {
            stack: stack,
            frame: frame,
        }
    }

    fn add_new_frame(stack: &mut Stack<'a>,
                     args: VMIndex,
                     function: Option<Callable<'a>>)
                     -> Frame<'a> {
        assert!(stack.len() >= args);
        let prev = stack.frames.last().cloned();
        let offset = stack.len() - args;
        let frame = Frame {
            offset: offset,
            instruction_index: 0,
            function: function,
            excess: false,
        };
        stack.frames.push(frame);
        debug!("----> Store {} {:?}\n||| {:?}",
               stack.frames.len(),
               frame,
               prev);
        frame
    }
}

impl<'a, 'b> Deref for StackFrame<'a, 'b> {
    type Target = [Value<'a>];
    fn deref(&self) -> &[Value<'a>] {
        &self.stack.values[self.frame.offset as usize..]
    }
}

impl<'a, 'b> DerefMut for StackFrame<'a, 'b> {
    fn deref_mut(&mut self) -> &mut [Value<'a>] {
        &mut self.stack.values[self.frame.offset as usize..]
    }
}

impl<'a, 'b> Index<VMIndex> for StackFrame<'a, 'b> {
    type Output = Value<'a>;
    fn index(&self, index: VMIndex) -> &Value<'a> {
        &self.stack.values[(self.frame.offset + index) as usize]
    }
}
impl<'a, 'b> IndexMut<VMIndex> for StackFrame<'a, 'b> {
    fn index_mut(&mut self, index: VMIndex) -> &mut Value<'a> {
        &mut self.stack.values[(self.frame.offset + index) as usize]
    }
}
impl<'a, 'b> Index<RangeFull> for StackFrame<'a, 'b> {
    type Output = [Value<'a>];
    fn index(&self, _: RangeFull) -> &[Value<'a>] {
        &self.stack.values[self.frame.offset as usize..]
    }
}
impl<'a, 'b> IndexMut<RangeFull> for StackFrame<'a, 'b> {
    fn index_mut(&mut self, _: RangeFull) -> &mut [Value<'a>] {
        &mut self.stack.values[self.frame.offset as usize..]
    }
}
impl<'a, 'b> Index<Range<VMIndex>> for StackFrame<'a, 'b> {
    type Output = [Value<'a>];
    fn index(&self, range: Range<VMIndex>) -> &[Value<'a>] {
        let offset = self.frame.offset;
        &self.stack.values[(range.start + offset) as usize..(range.end + offset) as usize]
    }
}
impl<'a, 'b> IndexMut<Range<VMIndex>> for StackFrame<'a, 'b> {
    fn index_mut(&mut self, range: Range<VMIndex>) -> &mut [Value<'a>] {
        let offset = self.frame.offset;
        &mut self.stack.values[(range.start + offset) as usize..(range.end + offset) as usize]
    }
}
impl<'a, 'b> Index<RangeTo<VMIndex>> for StackFrame<'a, 'b> {
    type Output = [Value<'a>];
    fn index(&self, range: RangeTo<VMIndex>) -> &[Value<'a>] {
        &self.stack.values[..(range.end + self.frame.offset) as usize]
    }
}
impl<'a, 'b> IndexMut<RangeTo<VMIndex>> for StackFrame<'a, 'b> {
    fn index_mut(&mut self, range: RangeTo<VMIndex>) -> &mut [Value<'a>] {
        &mut self.stack.values[..(range.end + self.frame.offset) as usize]
    }
}
impl<'a, 'b> Index<RangeFrom<VMIndex>> for StackFrame<'a, 'b> {
    type Output = [Value<'a>];
    fn index(&self, range: RangeFrom<VMIndex>) -> &[Value<'a>] {
        &self.stack.values[(range.start + self.frame.offset) as usize..]
    }
}
impl<'a, 'b> IndexMut<RangeFrom<VMIndex>> for StackFrame<'a, 'b> {
    fn index_mut(&mut self, range: RangeFrom<VMIndex>) -> &mut [Value<'a>] {
        &mut self.stack.values[(range.start + self.frame.offset) as usize..]
    }
}


#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use super::*;
    use vm::Value::*;

    #[test]
    fn remove_range() {

        let stack = RefCell::new(Stack::new());
        let stack = stack.borrow_mut();
        let mut frame = StackFrame::frame(stack, 0, None);
        frame.push(Int(0));
        frame.push(Int(1));
        let mut frame = frame.enter_scope(2, None);
        frame.push(Int(2));
        frame.push(Int(3));
        frame = frame.enter_scope(1, None);
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
}
