use std::cell::{Cell, RefMut};
use std::ops::{Deref, DerefMut, Index, IndexMut, Range, RangeTo, RangeFrom, RangeFull};

use gc::GcPtr;
use base::symbol::Symbol;
use vm::{ClosureData, Value, VM};
use types::VMIndex;

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Frame<'a> {
    pub offset: VMIndex,
    pub instruction_index: usize,
    pub function_name: Option<Symbol>,
    pub upvars: Option<GcPtr<ClosureData<'a>>>,
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

    pub fn get(&self, index: usize) -> Value<'a> {
        self.values[index].clone()
    }

    pub fn pop(&mut self) -> Value<'a> {
        self.values
            .pop()
            .expect("pop on empty stack")
    }

    pub fn set(&mut self, index: usize, v: Value<'a>) {
        self.values[index] = v;
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
impl<'a: 'b, 'b> StackFrame<'a, 'b> {
    pub fn new(v: RefMut<'b, Stack<'a>>,
               args: VMIndex,
               upvars: Option<GcPtr<ClosureData<'a>>>)
               -> StackFrame<'a, 'b> {
        let offset = v.len() - args;
        StackFrame {
            stack: v,
            frame: Frame {
                offset: offset,
                upvars: upvars,
                function_name: None,
                instruction_index: 0,
                excess: false,
            },
        }
    }

    pub fn new_empty(vm: &'b VM<'a>) -> StackFrame<'a, 'b> {
        let stack = vm.stack.borrow_mut();
        StackFrame::new(stack, 0, None)
    }

    pub fn len(&self) -> VMIndex {
        self.stack.len() - self.frame.offset
    }

    pub fn push(&mut self, v: Value<'a>) {
        self.stack.values.push(v);
    }

    pub fn top(&mut self) -> &Value<'a> {
        self.stack.values.last().expect("StackFrame: top")
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

    pub fn set_upvar(&self, index: VMIndex, v: Value<'a>) {
        let upvars = self.frame
                         .upvars
                         .as_ref()
                         .expect("Attempted to access upvar in non closure function");
        upvars.upvars[index as usize].set(v)
    }

    pub fn get_upvar(&self, index: VMIndex) -> Value<'a> {
        let upvars = self.frame
                         .upvars
                         .as_ref()
                         .expect("Attempted to access upvar in non closure function");
        upvars.upvars[index as usize].get()
    }

    pub fn new_scope<E, F>(stack: RefMut<'b, Stack<'a>>,
                           args: VMIndex,
                           function_name: Option<Symbol>,
                           upvars: Option<GcPtr<ClosureData<'a>>>,
                           f: F)
                           -> Result<StackFrame<'a, 'b>, E>
        where F: FnOnce(StackFrame<'a, 'b>) -> Result<StackFrame<'a, 'b>, E>
    {
        let stack = StackFrame::frame(stack, args, function_name, upvars);
        let mut stack = try!(f(stack));
        stack.stack.frames.pop();
        Ok(stack)
    }

    pub fn enter_scope(mut self,
                       args: VMIndex,
                       function_name: Option<Symbol>,
                       new_upvars: Option<GcPtr<ClosureData<'a>>>)
                       -> StackFrame<'a, 'b> {
        if let Some(frame) = self.stack.frames.last_mut() {
            *frame = self.frame;
        }
        StackFrame::frame(self.stack, args, function_name, new_upvars)
    }

    pub fn exit_scope(mut self) -> StackFrame<'a, 'b> {
        self.stack.frames.pop().expect("Expected frame");
        let frame = self.stack
                        .frames
                        .last()
                        .cloned()
                        .unwrap_or(Frame {
                            offset: 0,
                            upvars: None,
                            function_name: None,
                            instruction_index: 0,
                            excess: false,
                        });
        debug!("<---- Restore {} {:?}", self.stack.frames.len(), frame);
        StackFrame {
            stack: self.stack,
            frame: frame,
        }
    }

    pub fn scope<E, F>(self,
                       args: VMIndex,
                       function_name: Option<Symbol>,
                       upvars: Option<GcPtr<ClosureData<'a>>>,
                       f: F)
                       -> Result<StackFrame<'a, 'b>, E>
        where F: FnOnce(StackFrame<'a, 'b>) -> Result<StackFrame<'a, 'b>, E>
    {
        let mut stack = self.enter_scope(args, function_name, upvars);
        stack = try!(f(stack));
        stack = stack.exit_scope();
        Ok(stack)
    }

    pub fn frame(mut stack: RefMut<'b, Stack<'a>>,
                 args: VMIndex,
                 function_name: Option<Symbol>,
                 upvars: Option<GcPtr<ClosureData<'a>>>)
                 -> StackFrame<'a, 'b> {
        assert!(stack.len() >= args);
        let prev = stack.frames.last().cloned();
        let offset = stack.len() - args;
        let frame = Frame {
            offset: offset,
            instruction_index: 0,
            function_name: function_name,
            upvars: upvars,
            excess: false,
        };
        stack.frames.push(frame);
        debug!("----> Store {} {:?}\n||| {:?}",
               stack.frames.len(),
               frame,
               prev);
        StackFrame {
            stack: stack,
            frame: frame,
        }
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
    use super::*;
    use vm::Value::*;
    use std::cell::RefCell;
    #[test]
    fn remove_range() {
        let stack = RefCell::new(Stack::new());
        let mut stack = stack.borrow_mut();
        stack.push(Int(0));
        stack.push(Int(1));
        let mut frame = StackFrame::frame(stack, 2, None, None);
        frame.push(Int(2));
        frame.push(Int(3));
        frame = frame.enter_scope(1, None, None);
        frame.push(Int(4));
        frame.push(Int(5));
        frame.push(Int(6));
        frame = frame.exit_scope();
        frame.remove_range(2, 5);
        assert_eq!(frame.stack.values, vec![Int(0), Int(1), Int(5), Int(6)]);
        frame = frame.exit_scope();
        frame.remove_range(1, 3);
        assert_eq!(frame.stack.values, vec![Int(0), Int(6)]);
    }
}
