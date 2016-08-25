use std::borrow::Cow;
use std::collections::hash_map::Entry;

use types;
use types::{AliasData, Type, Generic, TcType, TypeEnv};
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

/// Expand `typ` if it is an alias that can be expanded and return the expanded type.
/// Returns `None` if the type is not an alias or the alias could not be expanded.
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
    pub named_variables: FnvMap<Symbol, TcType>,
}

impl Instantiator {
    pub fn new() -> Instantiator {
        Instantiator { named_variables: FnvMap::default() }
    }

    fn variable_for(&mut self,
                    generic: &Generic<Symbol, TcType>,
                    on_unbound: &mut FnMut(&Symbol) -> TcType)
                    -> TcType {
        let var = match self.named_variables.entry(generic.id.clone()) {
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
        self.named_variables.clear();
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
    where F: FnMut(&Generic<Symbol, TcType>) -> Option<TcType>
{
    types::walk_move_type(typ,
                          &mut |typ| {
                              match *typ {
                                  Type::Generic(ref x) => f(x),
                                  _ => None,
                              }
                          })
}
