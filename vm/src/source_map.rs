use base::pos::Line;

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
