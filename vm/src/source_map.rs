use std::slice::Iter;

use base::pos::Line;
use base::symbol::Symbol;

#[derive(Debug)]
pub struct SourceMap {
    /// The index of the first instruction for each line
    map: Vec<(usize, Line)>,
}

impl SourceMap {
    pub fn new() -> SourceMap {
        SourceMap { map: Vec::new() }
    }

    /// Defines the instruction at `instruction_index` to be at `current_line`.
    /// This function must be called with indexes in increasing order
    pub fn emit(&mut self, instruction_index: usize, current_line: Line) {
        let last_emitted_line = self.map.last().map_or(Line::from(0), |&(_, x)| x);
        if last_emitted_line != current_line {
            self.map.push((instruction_index, current_line));
        }
    }

    /// Returns the line where the instruction at `instruction_index` were defined
    pub fn line(&self, instruction_index: usize) -> Line {
        // The line for `instruction_index` is at the last index still larger than
        // the index in `map`
        let p = self.map
            .iter()
            .position(|&(index, _)| index > instruction_index)
            .unwrap_or(self.map.len());
        if p == 0 {
            Line::from(0)
        } else {
            self.map[p - 1].1
        }
    }
}

#[derive(Debug)]
pub struct LocalMap {
    // Instruction indexes marking [start, end) where the local variable `Symbol` exists
    map: Vec<(usize, Symbol, usize)>,
}

impl LocalMap {
    pub fn new() -> LocalMap {
        LocalMap { map: Vec::new() }
    }

    /// Emits a local which is available starting from `instruction_index`. The end of each local's
    /// scope must be defined by calling `close`
    pub fn emit(&mut self, instruction_index: usize, name: Symbol) {
        self.map.push((instruction_index, name, instruction_index));
    }

    /// `close` marks the end of a variables span and should be called for each variable inserted with
    /// `emit` but in reverse order
    pub fn close(&mut self, instruction_index: usize) {
        if let Some(&mut (_, _, ref mut end)) = self.map.iter_mut().rev().find(|t| t.0 == t.2) {
            *end = instruction_index;
        }
    }

    /// Returns an iterator over the variables in scope at `instruction_index`
    pub fn locals(&self, instruction_index: usize) -> LocalIter {
        LocalIter {
            locals: self.map.iter(),
            instruction_index: instruction_index,
        }
    }
}

pub struct LocalIter<'a> {
    locals: Iter<'a, (usize, Symbol, usize)>,
    instruction_index: usize,
}

impl<'a> LocalIter<'a> {
    pub fn empty() -> LocalIter<'a> {
        LocalIter {
            locals: [].iter(),
            instruction_index: 0,
        }
    }
}

impl<'a> Iterator for LocalIter<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        while let Some(local) = self.locals.next() {
            if local.0 <= self.instruction_index && self.instruction_index < local.2 {
                return Some(local.1.declared_name());
            }
        }
        None
    }
}
