use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::hash_map::Entry;

use base::ast;
use base::ast::Type;
use base::symbol::Symbol;
use base::types::{TcType, TypeEnv};
use unify_type::TypeError::UndefinedType;
use substitution::Substitution;
use unify;

pub struct AliasInstantiator<'a> {
    pub inst: &'a Instantiator,
    pub env: &'a TypeEnv
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
        match **typ {
            Type::Data(ast::TypeConstructor::Data(id), ref args) => {
                self.type_of_alias(id, args)
                    .unwrap_or_else(|_| None)
            }
            _ => None,
        }
    }

    pub fn type_of_alias(&self,
                     id: Symbol,
                     arguments: &[TcType])
                     -> Result<Option<TcType>, ::unify_type::Error<Symbol>> {
        let (args, mut typ) = {
            let (args, typ) = try!(self.env
                                       .find_type_info(&id)
                                       .map(|s| Ok(s))
                                       .unwrap_or_else(|| {
                                           Err(unify::Error::Other(UndefinedType(id.clone())))
                                       }));
            match typ {
                Some(typ) => {
                    // TODO avoid clones here
                    let args: Vec<_> = args.iter().cloned().collect();
                    (args, typ.clone())
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
            let expected = Type::data(ast::TypeConstructor::Data(id),
                                      arguments.iter().cloned().collect());
            return Err(unify::Error::TypeMismatch(expected, typ));
        }
        let typ = self.inst.instantiate_with(typ, arguments, &args);
        Ok(Some(typ))
    }
}

pub struct Instantiator {
    pub subs: Substitution<TcType>,
    pub named_variables: RefCell<HashMap<Symbol, TcType>>,
}

impl Instantiator {
    pub fn new() -> Instantiator {
        Instantiator {
            subs: Substitution::new(),
            named_variables: RefCell::new(HashMap::new()),
        }
    }

    fn variable_for(&self, generic: &ast::Generic<Symbol>) -> TcType {
        let mut variables = self.named_variables.borrow_mut();
        let var = match variables.entry(generic.id) {
            Entry::Vacant(entry) => {
                let t = self.subs.new_var();
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
    pub fn instantiate(&mut self, typ: &TcType) -> TcType {
        self.named_variables.borrow_mut().clear();
        self.instantiate_(typ)
    }

    pub fn instantiate_(&mut self, typ: &TcType) -> TcType {
        instantiate(typ.clone(), |id| Some(self.variable_for(id)))
    }

    fn instantiate_with(&self,
                        typ: TcType,
                        arguments: &[TcType],
                        args: &[ast::Generic<Symbol>])
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

    pub fn replace_variable(&self, typ: &Type<Symbol>) -> Option<TcType> {
        match *typ {
            Type::Variable(ref id) => {
                self.subs
                    .find_type_for_var(id.id)
                    .map(|t| t.clone())
            }
            _ => None,
        }
    }

    pub fn set_type(&self, t: TcType) -> TcType {
        ast::walk_move_type(t,
                            &mut |typ| {
                                let replacement = self.replace_variable(typ);
                                let result = {
                                    let mut typ = typ;
                                    if let Some(ref t) = replacement {
                                        typ = &**t;
                                    }
                                    unroll_app(typ)
                                };
                                result.or(replacement)
                            })
    }
}

pub fn instantiate<F>(typ: TcType, mut f: F) -> TcType
    where F: FnMut(&ast::Generic<Symbol>) -> Option<TcType>
{
    ast::walk_move_type(typ,
                        &mut |typ| {
                            match *typ {
                                Type::Generic(ref x) => f(x),
                                _ => None,
                            }
                        })
}


fn unroll_app(typ: &Type<Symbol>) -> Option<TcType> {
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
