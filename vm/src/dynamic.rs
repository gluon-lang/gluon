use std::borrow::Cow;
use std::ops::Deref;

use base::resolve;
use base::types::{ArcType, Type};

use thread::{RootedValue, Thread, ThreadInternal, VmRoot};

#[derive(Debug)]
pub struct FieldIter<'a, T>
where
    T: Deref<Target = Thread> + 'a,
{
    value: &'a RootedValue<T>,
    index: usize,
    resolved_type: Cow<'a, ArcType>,
}

impl<'a, T> Iterator for FieldIter<'a, T>
where
    T: VmRoot<'a>,
{
    type Item = (RootedValue<T>, ArcType);

    fn next(&mut self) -> Option<Self::Item> {
        match **self.resolved_type {
            Type::Record(ref row) => {
                match **row {
                    Type::ExtendRow { ref fields, .. } => {
                        let index = self.index;
                        self.index += 1;
                        self.value.get(index).map(|value| {
                            (value, fields[index].typ.clone())
                        })
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

pub fn field_iter<'vm, T>(
    value: &'vm RootedValue<T>,
    typ: &'vm ArcType,
    thread: &Thread,
) -> FieldIter<'vm, T>
where
    T: VmRoot<'vm>,
{
    FieldIter {
        value: value,
        index: 0,
        resolved_type: resolve::remove_aliases_cow(&*thread.global_env().get_env(), typ),
    }
}
