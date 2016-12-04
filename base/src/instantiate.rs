use std::borrow::Cow;
use std::collections::hash_map::Entry;

use types;
use types::{AliasData, AppVec, Type, ArcType, TypeEnv};
use symbol::Symbol;
use fnv::FnvMap;

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
pub fn remove_aliases(env: &TypeEnv, mut typ: ArcType) -> ArcType {
    while let Ok(Some(new)) = maybe_remove_alias(env, &typ) {
        typ = new;
    }
    typ
}

pub fn remove_aliases_cow<'t>(env: &TypeEnv, typ: &'t ArcType) -> Cow<'t, ArcType> {
    match maybe_remove_alias(env, typ) {
        Ok(Some(typ)) => Cow::Owned(remove_aliases(env, typ)),
        _ => return Cow::Borrowed(typ),
    }
}

/// Removes all possible aliases while checking that
pub fn remove_aliases_checked(reduced_aliases: &mut Vec<Symbol>,
                              env: &TypeEnv,
                              typ: &ArcType)
                              -> Result<Option<ArcType>, Error> {
    if let Some((alias_id, _)) = typ.as_alias() {
        if reduced_aliases.iter().any(|name| name == alias_id) {
            return Err(Error::SelfRecursive(alias_id.clone()));
        }
        reduced_aliases.push(alias_id.clone());
    }
    let mut typ = match maybe_remove_alias(env, typ)? {
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
        match maybe_remove_alias(env, &typ)? {
            Some(new) => typ = new,
            None => break,
        }
    }
    Ok(Some(typ))
}

pub fn remove_alias(env: &TypeEnv, typ: ArcType) -> ArcType {
    maybe_remove_alias(env, &typ).unwrap_or(None).unwrap_or(typ)
}

/// Expand `typ` if it is an alias that can be expanded and return the expanded type.
/// Returns `None` if the type is not an alias or the alias could not be expanded.
pub fn maybe_remove_alias(env: &TypeEnv, typ: &ArcType) -> Result<Option<ArcType>, Error> {
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
            env.find_type_info(&id)
                .map(|a| &**a)
                .ok_or_else(|| Error::UndefinedType(id.clone()))?
        }
    };
    Ok(type_of_alias(alias, args))
}

/// Returns the type which is aliased by `alias` if it was possible to do a substitution on the
/// type arguments of `alias` using `args`
///
/// Example:
///     alias = Result e t (| Err e | Ok t)
///     args = [Error, Option a]
///     result = | Err Error | Ok (Option a)
pub fn type_of_alias(alias: &AliasData<Symbol, ArcType>, args: &[ArcType]) -> Option<ArcType> {
    let alias_args = &alias.args;
    let mut typ = alias.typ.clone();

    // It is ok to take the aliased type only if the alias is fully applied or if it
    // the missing argument only appear in order at the end of the alias
    // i.e
    // type Test a b c = Type (a Int) b c
    //
    // Test a b == Type (a Int) b
    // Test a == Type (a Int)
    // Test == ??? (Impossible to do a sane substitution)
    match *typ.clone() {
        Type::App(ref d, ref arg_types) => {
            let allowed_missing_args = arg_types.iter()
                .rev()
                .zip(alias_args.iter().rev())
                .take_while(|&(l, r)| {
                    match **l {
                        Type::Generic(ref g) => g == r,
                        _ => false,
                    }
                })
                .count();
            if alias_args.len() - args.len() <= allowed_missing_args {
                // Remove the args at the end of the aliased type
                let arg_types: AppVec<_> = arg_types.iter()
                    .take(arg_types.len() - (alias_args.len() - args.len()))
                    .cloned()
                    .collect();
                typ = Type::app(d.clone(), arg_types);
            } else {
                return None;
            }
        }
        _ => {
            if args.len() != alias_args.len() {
                return None;
            }
        }
    }

    Some(types::walk_move_type(typ,
                               &mut |typ| {
        match *typ {
            Type::Generic(ref generic) => {
                // Replace the generic variable with the type from the list
                // or if it is not found the make a fresh variable
                alias_args.iter()
                    .zip(args)
                    .find(|&(arg, _)| arg.id == generic.id)
                    .map(|(_, typ)| typ.clone())
            }
            _ => None,
        }
    }))
}

#[derive(Debug, Default)]
pub struct Instantiator {
    pub named_variables: FnvMap<Symbol, ArcType>,
}

impl Instantiator {
    pub fn new() -> Instantiator {
        Instantiator { named_variables: FnvMap::default() }
    }

    pub fn instantiate<F>(&mut self, typ: &ArcType, mut on_unbound: F) -> ArcType
        where F: FnMut(&Symbol) -> ArcType,
    {
        types::walk_move_type(typ.clone(),
                              &mut |typ| {
            match *typ {
                Type::Generic(ref generic) => {
                    let var = match self.named_variables.entry(generic.id.clone()) {
                        Entry::Vacant(entry) => entry.insert(on_unbound(&generic.id)).clone(),
                        Entry::Occupied(entry) => entry.get().clone(),
                    };

                    let mut var = (*var).clone();
                    if let Type::Variable(ref mut var) = var {
                        var.kind = generic.kind.clone();
                    }

                    Some(ArcType::from(var))
                }
                _ => None,
            }
        })
    }
}
