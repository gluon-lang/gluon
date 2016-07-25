use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::ops::Deref;

use types;
use types::{AliasData, Type, Generic, TcType, TypeEnv, merge};
use symbol::Symbol;

quick_error! {
    #[derive(Debug)]
    pub enum Error {
        SelfRecursive(id: Symbol) {
            description("self recursive")
            display("The use of self recursion in type `{}` could not be unified.", id)
        }
        UndefinedType(id: Symbol) {
            description("undefined type")
            display("Type `{}` does not exist.", id)
        }
    }
}

/// Removes type aliases from `typ` until it is an actual type
pub fn remove_aliases(env: &TypeEnv, mut typ: TcType) -> TcType {
    while let Ok(Some(new)) = maybe_remove_alias(env, &typ) {
        typ = new;
    }
    typ
}

pub fn remove_aliases_cow<'t>(env: &TypeEnv, typ: &'t TcType) -> Cow<'t, TcType> {
    let mut typ = match maybe_remove_alias(env, typ) {
        Ok(Some(new)) => new,
        _ => return Cow::Borrowed(typ),
    };
    while let Ok(Some(new)) = maybe_remove_alias(env, &typ) {
        typ = new;
    }
    Cow::Owned(typ)
}

/// Removes all possible aliases while checking that
pub fn remove_aliases_checked(reduced_aliases: &mut Vec<Symbol>,
                              env: &TypeEnv,
                              typ: &TcType)
                              -> Result<Option<TcType>, Error> {
    if let Some((alias_id, _)) = typ.as_alias() {
        if reduced_aliases.iter().any(|name| name == alias_id) {
            return Err(Error::SelfRecursive(alias_id.clone()));
        }
        reduced_aliases.push(alias_id.clone());
    }
    let mut typ = match try!(maybe_remove_alias(env, typ)) {
        Some(new) => new,
        None => return Ok(None),
    };
    loop {
        if let Some((alias_id, _)) = typ.as_alias() {
            if reduced_aliases.iter().any(|name| name == alias_id) {
                return Err(Error::SelfRecursive(alias_id.clone()));
            }
            reduced_aliases.push(alias_id.clone());
        }
        match try!(maybe_remove_alias(env, &typ)) {
            Some(new) => typ = new,
            None => break,
        }
    }
    Ok(Some(typ))
}

pub fn remove_alias(env: &TypeEnv, typ: TcType) -> TcType {
    maybe_remove_alias(env, &typ).unwrap_or(None).unwrap_or(typ)
}

/// Expand `typ` if it is an alias that can be expanded and return the expanded type. Returns `None` if the type is not an alias or the alias could not be expanded.
pub fn maybe_remove_alias(env: &TypeEnv, typ: &TcType) -> Result<Option<TcType>, Error> {
    let maybe_alias = match **typ {
        Type::Alias(ref alias) if alias.args.is_empty() => Some(alias),
        Type::App(ref alias, ref args) => {
            match **alias {
                Type::Alias(ref alias) if alias.args.len() == args.len() => Some(alias),
                _ => None,
            }
        }
        _ => None,
    };
    let (id, args) = match typ.as_alias() {
        Some(x) => x,
        None => return Ok(None),
    };
    let alias = match maybe_alias {
        Some(alias) => alias,
        None => {
            try!(env.find_type_info(&id)
                .map(|a| &**a)
                .ok_or_else(|| Error::UndefinedType(id.clone())))
        }
    };
    Ok(type_of_alias(alias, args))
}

/// Returns the type which is aliased by `alias` if it was possible to do a substitution on the
/// type arguments of `alias` using `arguments`
///
/// Example:
///     alias = Result e t (| Err e | Ok t)
///     arguments = [Error, Option a]
///     result = | Err Error | Ok (Option a)
pub fn type_of_alias(alias: &AliasData<Symbol, TcType>, arguments: &[TcType]) -> Option<TcType> {
    let args = &alias.args;
    let mut typ = match alias.typ {
        Some(ref typ) => typ.clone(),
        None => return None,
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
        Type::App(ref d, ref arg_types) => {
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
                    .take(arg_types.len() - (args.len() - arguments.len()))
                    .cloned()
                    .collect();
                typ = Type::app(d.clone(), arg_types);
                true
            } else {
                false
            }
        }
        _ => arguments.len() == args.len(),
    };
    if !ok_substitution {
        return None;
    }
    let typ = instantiate(typ, |gen| {
        // Replace the generic variable with the type from the list
        // or if it is not found the make a fresh variable
        args.iter()
            .zip(arguments)
            .find(|&(arg, _)| arg.id == gen.id)
            .map(|(_, typ)| typ.clone())
    });
    Some(typ)
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

    /// Instantiates a type, replacing all generic variables with fresh type variables
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
                Type::App(ref id, ref args) => {
                    let new_args = walk_move_types(args.iter(), |t| walk_move_type2(t, f));
                    merge(id, walk_move_type2(id, f), args, new_args, Type::app)
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
