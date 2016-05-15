use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::ops::Deref;

use base::types;
use base::types::{Type, Generic, merge};
use base::symbol::Symbol;
use base::types::{TcType, TypeEnv};
use unify_type::TypeError::UndefinedType;
use unify;

pub struct AliasInstantiator<'a> {
    pub inst: &'a Instantiator,
    pub env: &'a TypeEnv,
}

impl<'a> AliasInstantiator<'a> {
    pub fn new(inst: &'a Instantiator, env: &'a TypeEnv) -> AliasInstantiator<'a> {
        AliasInstantiator {
            inst: inst,
            env: env,
        }
    }

    /// Removes type aliases from `typ` until it is an actual type
    pub fn remove_aliases(&self, mut typ: TcType) -> TcType {
        while let Some(new) = self.maybe_remove_alias(&typ) {
            typ = new;
        }
        typ
    }

    pub fn remove_alias(&self, typ: TcType) -> TcType {
        self.maybe_remove_alias(&typ).unwrap_or(typ)
    }

    pub fn maybe_remove_alias(&self, typ: &TcType) -> Option<TcType> {
        let (id, args) = match **typ {
            Type::Id(ref r) => (r, &[][..]),
            Type::Data(ref r, ref args) => {
                match **r {
                    Type::Id(ref r) => (r, &args[..]),
                    _ => return None,
                }
            }
            _ => return None,
        };
        self.type_of_alias(id, args)
            .unwrap_or_else(|_| None)
    }

    pub fn type_of_alias(&self,
                         id: &Symbol,
                         arguments: &[TcType])
                         -> Result<Option<TcType>, ::unify_type::Error<Symbol>> {
        let (args, mut typ) = {
            let alias = try!(self.env
                                 .find_type_info(&id)
                                 .ok_or_else(|| unify::Error::Other(UndefinedType(id.clone()))));
            match alias.typ {
                Some(ref typ) => {
                    // TODO avoid clones here
                    (alias.args.clone(), typ.clone())
                }
                None => return Ok(None),
            }
        };
        // It is ok to take the aliased type only if the alias is fully applied or if it
        // the missing argument only appear in order at the end of the alias
        // i.e
        // type Test a b c = Type (a Int) b c
        //
        // Test a b == Type (a Int) b
        // Test a == Type (a Int)
        // Test == ??? (Impossible to do a sane substitution)

        let ok_substitution = match *typ.clone() {
            Type::Data(ref d, ref arg_types) => {
                let allowed_missing_args = arg_types.iter()
                                                    .rev()
                                                    .zip(args.iter().rev())
                                                    .take_while(|&(l, r)| {
                                                        match **l {
                                                            Type::Generic(ref g) => g == r,
                                                            _ => false,
                                                        }
                                                    })
                                                    .count();
                if args.len() - arguments.len() <= allowed_missing_args {
                    // Remove the args at the end of the aliased type
                    let arg_types: Vec<_> = arg_types.iter()
                                                     .take(arg_types.len() -
                                                           (args.len() - arguments.len()))
                                                     .cloned()
                                                     .collect();
                    typ = Type::data(d.clone(), arg_types);
                    true
                } else {
                    false
                }
            }
            _ => arguments.len() == args.len(),
        };
        if !ok_substitution {
            return Ok(None);
        }
        let typ = self.inst.instantiate_with(typ, arguments, &args);
        Ok(Some(typ))
    }
}

#[derive(Debug, Default)]
pub struct Instantiator {
    pub named_variables: RefCell<HashMap<Symbol, TcType>>,
}

impl Instantiator {
    pub fn new() -> Instantiator {
        Instantiator { named_variables: RefCell::new(HashMap::new()) }
    }

    fn variable_for(&self,
                    generic: &Generic<Symbol>,
                    on_unbound: &mut FnMut(&Symbol) -> TcType)
                    -> TcType {
        let mut variables = self.named_variables.borrow_mut();
        let var = match variables.entry(generic.id.clone()) {
            Entry::Vacant(entry) => {
                let t = on_unbound(&generic.id);
                entry.insert(t).clone()
            }
            Entry::Occupied(entry) => entry.get().clone(),
        };
        let mut var = (*var).clone();
        if let Type::Variable(ref mut var) = var {
            var.kind = generic.kind.clone();
        }
        TcType::from(var)
    }

    ///Instantiates a type, replacing all generic variables with fresh type variables
    pub fn instantiate<F>(&mut self, typ: &TcType, on_unbound: F) -> TcType
        where F: FnMut(&Symbol) -> TcType
    {
        self.named_variables.borrow_mut().clear();
        self.instantiate_(typ, on_unbound)
    }

    pub fn instantiate_<F>(&mut self, typ: &TcType, mut on_unbound: F) -> TcType
        where F: FnMut(&Symbol) -> TcType
    {
        instantiate(typ.clone(),
                    |id| Some(self.variable_for(id, &mut on_unbound)))
    }

    fn instantiate_with(&self,
                        typ: TcType,
                        arguments: &[TcType],
                        args: &[Generic<Symbol>])
                        -> TcType {
        self.named_variables.borrow_mut().clear();
        instantiate(typ, |gen| {
            // Replace the generic variable with the type from the list
            // or if it is not found the make a fresh variable
            args.iter()
                .zip(arguments)
                .find(|&(arg, _)| arg.id == gen.id)
                .map(|(_, typ)| typ.clone())
        })
    }
}

pub fn instantiate<F>(typ: TcType, mut f: F) -> TcType
    where F: FnMut(&Generic<Symbol>) -> Option<TcType>
{
    walk_move_type_no_recurse(typ,
                              &mut |typ| {
                                  match *typ {
                                      Type::Generic(ref x) => f(x),
                                      _ => None,
                                  }
                              })
}


pub fn unroll_app(typ: &Type<Symbol>) -> Option<TcType> {
    let mut args = Vec::new();
    let mut current = typ;
    loop {
        match *current {
            Type::App(ref l, ref r) => {
                args.push(r.clone());
                current = &**l;
            }
            Type::Data(ref l, ref rest) => {
                args.extend(rest.iter().rev().cloned());
                args.reverse();
                return Some(Type::data(l.clone(), args));
            }
            _ => return None,
        }
    }
}


/// Walks through a type replacing some types
/// If a type is replaced the new type will not be traversed
fn walk_move_type_no_recurse<F, I, T>(typ: T, f: &mut F) -> T
    where F: FnMut(&Type<I, T>) -> Option<T>,
          T: Deref<Target = Type<I, T>> + From<Type<I, T>> + Clone,
          I: Clone
{
    walk_move_type2(&typ, f).unwrap_or(typ)
}

fn walk_move_type2<F, I, T>(typ: &Type<I, T>, f: &mut F) -> Option<T>
    where F: FnMut(&Type<I, T>) -> Option<T>,
          T: Deref<Target = Type<I, T>> + From<Type<I, T>> + Clone,
          I: Clone
{
    let new = f(typ);
    let result = match new {
        Some(new_type) => return Some(new_type),
        None => {
            let typ = new.as_ref().map_or(typ, |t| &**t);
            match *typ {
                Type::Data(ref id, ref args) => {
                    let new_args = walk_move_types(args.iter(), |t| walk_move_type2(t, f));
                    merge(id, walk_move_type2(id, f), args, new_args, Type::data)
                }
                Type::Array(ref inner) => walk_move_type2(&**inner, f).map(Type::array),
                Type::Function(ref args, ref ret) => {
                    let new_args = walk_move_types(args.iter(), |t| walk_move_type2(t, f));
                    merge(args, new_args, ret, walk_move_type2(ret, f), Type::function)
                }
                Type::Record { ref types, ref fields } => {
                    let new_types = None;
                    let new_fields = walk_move_types(fields.iter(), |field| {
                        walk_move_type2(&field.typ, f).map(|typ| {
                            types::Field {
                                name: field.name.clone(),
                                typ: typ,
                            }
                        })
                    });
                    merge(types, new_types, fields, new_fields, Type::record)
                }
                Type::App(ref l, ref r) => {
                    merge(l,
                          walk_move_type2(l, f),
                          r,
                          walk_move_type2(r, f),
                          Type::app)
                }
                Type::Variants(ref variants) => {
                    walk_move_types(variants.iter(),
                                    |v| walk_move_type2(&v.1, f).map(|t| (v.0.clone(), t)))
                        .map(Type::variants)
                }
                Type::Builtin(_) |
                Type::Variable(_) |
                Type::Generic(_) |
                Type::Id(_) |
                Type::Alias(_) => None,
            }
        }
    };
    result.or(new)
}
fn walk_move_types<'a, I, F, T>(types: I, mut f: F) -> Option<Vec<T>>
    where I: Iterator<Item = &'a T>,
          F: FnMut(&'a T) -> Option<T>,
          T: Clone + 'a
{
    let mut out = Vec::new();
    walk_move_types2(types, false, &mut out, &mut f);
    if out.is_empty() {
        None
    } else {
        out.reverse();
        Some(out)
    }
}
fn walk_move_types2<'a, I, F, T>(mut types: I, replaced: bool, output: &mut Vec<T>, f: &mut F)
    where I: Iterator<Item = &'a T>,
          F: FnMut(&'a T) -> Option<T>,
          T: Clone + 'a
{
    if let Some(typ) = types.next() {
        let new = f(typ);
        walk_move_types2(types, replaced || new.is_some(), output, f);
        match new {
            Some(typ) => {
                output.push(typ);
            }
            None if replaced || !output.is_empty() => {
                output.push(typ.clone());
            }
            None => (),
        }
    }
}
