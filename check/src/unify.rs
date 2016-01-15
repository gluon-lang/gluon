use std::cell::RefCell;
use std::fmt;
use std::mem;

use base::ast;
use base::ast::{ASTType, Type, TypeVariable};
use base::error::Errors;
use base::symbol::Symbol;
use typecheck::{AliasInstantiator, Instantiator, TcResult, TcType, TypeError};

#[derive(Debug, PartialEq)]
pub enum Error<I> {
    TypeMismatch(ASTType<I>, ASTType<I>),
    FieldMismatch(I, I),
    Occurs(TypeVariable, ASTType<I>),
    UndefinedType(I),
}

fn apply_subs(inst: &Instantiator, error: Vec<Error<Symbol>>) -> Vec<Error<Symbol>> {
    error.into_iter()
         .map(|error| {
             match error {
                 Error::TypeMismatch(expected, actual) => {
                     Error::TypeMismatch(inst.set_type(expected), inst.set_type(actual))
                 }
                 Error::FieldMismatch(expected, actual) => Error::FieldMismatch(expected, actual),
                 Error::Occurs(var, typ) => Error::Occurs(var, inst.set_type(typ)),
                 Error::UndefinedType(id) => Error::UndefinedType(id),
             }
         })
         .collect()
}

impl<I> fmt::Display for Error<I> where I: fmt::Display + ::std::ops::Deref<Target = str>
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Error::*;
        match *self {
            TypeMismatch(ref l, ref r) => {
                write!(f, "Types do not match:\n\tExpected: {}\n\tFound: {}", l, r)
            }
            FieldMismatch(ref l, ref r) => {
                write!(f,
                       "Field names in record do not match.\n\tExpected: {}\n\tFound: {}",
                       l,
                       r)
            }
            Occurs(ref var, ref typ) => write!(f, "Variable `{}` occurs in `{}`.", var, typ),
            UndefinedType(ref id) => write!(f, "Type `{}` does not exist.", id),
        }
    }
}


pub struct Unifier<'a> {
    alias: AliasInstantiator<'a>,
    symbols: &'a ast::DisplayEnv<Ident = Symbol>,
    unification_errors: RefCell<Errors<Error<Symbol>>>,
}

impl<'a> Unifier<'a> {
    pub fn new(alias: AliasInstantiator<'a>,
               symbols: &'a ast::DisplayEnv<Ident = Symbol>)
               -> Unifier<'a> {
        Unifier {
            alias: alias,
            symbols: symbols,
            unification_errors: RefCell::new(Errors::new()),
        }
    }

    fn unification_error(&self, err: Error<Symbol>) {
        self.unification_errors.borrow_mut().error(err);
    }

    pub fn unify(&self, expected: &TcType, mut actual: TcType) -> TcResult {
        debug!("Unify {} <=> {}",
               ast::display_type(&self.symbols, expected),
               ast::display_type(&self.symbols, &actual));
        self.unify_(expected, &actual);
        let has_errors = self.unification_errors.borrow().has_errors();
        if has_errors {
            let errors = mem::replace(&mut *self.unification_errors.borrow_mut(), Errors::new());
            let mut expected = expected.clone();
            expected = self.alias.inst.set_type(expected);
            actual = self.alias.inst.set_type(actual);
            debug!("Error '{:?}' between:\n>> {}\n>> {}",
                   errors.errors,
                   ast::display_type(&self.symbols, &expected),
                   ast::display_type(&self.symbols, &actual));
            Err(TypeError::Unification(expected,
                                       actual,
                                       apply_subs(&self.alias.inst, errors.errors)))
        } else {
            // Return the `expected` type as that is what is passed in for type
            // declarations
            Ok(self.alias.inst.set_type(expected.clone()))
        }
    }

    fn unify_(&self, expected: &TcType, actual: &TcType) {
        let expected = self.alias.inst.subs.real(expected);
        let actual = self.alias.inst.subs.real(actual);
        debug!("{} <=> {}",
               ast::display_type(&self.symbols, expected),
               ast::display_type(&self.symbols, actual));
        match (&**expected, &**actual) {
            (&Type::Variable(ref l), &Type::Variable(ref r)) if l.id == r.id => (),
            (&Type::Variable(ref l), _) => self.union(l, actual),
            (_, &Type::Variable(ref r)) => self.union(r, expected),
            (&Type::Function(ref l_args, ref l_ret),
             &Type::Function(ref r_args, ref r_ret)) => {
                if l_args.len() == r_args.len() {
                    for (l, r) in l_args.iter().zip(r_args.iter()) {
                        self.unify_(l, r);
                    }
                    self.unify_(l_ret, r_ret)
                } else {
                    self.unification_error(Error::TypeMismatch(expected.clone(), actual.clone()))
                }
            }
            (&Type::Function(ref l_args, ref l_ret), &Type::App(..)) => {
                self.unify_function(&l_args[0], l_ret, actual)
            }
            (&Type::App(..), &Type::Function(ref l_args, ref l_ret)) => {
                self.unify_function(&l_args[0], l_ret, expected)
            }
            (&Type::Array(ref l), &Type::Array(ref r)) => self.unify_(l, r),
            (&Type::Data(ref l, ref l_args),
             &Type::Data(ref r, ref r_args))
                if l == r && l_args.len() == r_args.len() => {
                for (l, r) in l_args.iter().zip(r_args.iter()) {
                    self.unify_(l, r);
                }
            }
            (&Type::Record { fields: ref l_args, .. },
             &Type::Record { fields: ref r_args, .. })
                if l_args.len() == r_args.len() => {
                for (l, r) in l_args.iter().zip(r_args.iter()) {
                    if l.name != r.name {
                        self.unification_error(Error::FieldMismatch(l.name, r.name));
                    } else {
                        self.unify_(&l.typ, &r.typ);
                    }
                }
            }
            (&Type::Data(ref l, ref l_args), &Type::App(_, _)) => {
                let error_count = self.unification_errors.borrow().errors.len();
                self.unify_app(l, l_args, expected, &|last, r_arg| self.unify_(r_arg, last));
                let range = error_count..self.unification_errors.borrow().errors.len();
                if range.start != range.end {
                    // Attempt to unify using the type that is aliased if that exists
                    match *l {
                        ast::TypeConstructor::Data(l) => {
                            let l = match self.alias.type_of_alias(l, l_args) {
                                Ok(typ) => typ,
                                Err(err) => return self.unification_error(err),
                            };
                            match l {
                                Some(l) => {
                                    self.unify_(&l, expected);
                                    self.rollback_unification_errors(range);
                                }
                                None => (),
                            }
                        }
                        _ => (),
                    }
                }
            }
            (&Type::App(_, _), &Type::Data(ref r, ref r_args)) => {
                let error_count = self.unification_errors.borrow().errors.len();
                self.unify_app(r, r_args, expected, &|last, l_arg| self.unify_(l_arg, last));
                let range = error_count..self.unification_errors.borrow().errors.len();
                if range.start != range.end {
                    match *r {
                        ast::TypeConstructor::Data(r) => {
                            let r = match self.alias.type_of_alias(r, r_args) {
                                Ok(typ) => typ,
                                Err(err) => return self.unification_error(err),
                            };
                            match r {
                                Some(r) => {
                                    self.unify_(&r, expected);
                                    self.rollback_unification_errors(range);
                                }
                                None => (),
                            }
                        }
                        _ => (),
                    }
                }
            }
            (&Type::App(ref l1, ref l2), &Type::App(ref r1, ref r2)) => {
                self.unify_(l1, r1);
                self.unify_(l2, r2);
            }
            _ => {
                if expected == actual {
                    // Successful unification
                    return;
                }
                // Attempt to unify by replacing the right or left hand side with the type it
                // aliases (if any)
                let len = self.unification_errors.borrow().errors.len();
                if self.unify_alias(expected, actual, len..len) {
                    // Successful unification
                    return;
                }
                let len2 = self.unification_errors.borrow().errors.len();
                if self.unify_alias(actual, expected, len..len2) {
                    // Successful unification
                    return;
                }
                let len3 = self.unification_errors.borrow().errors.len();
                self.rollback_unification_errors(len..len3);
                self.unification_error(Error::TypeMismatch(expected.clone(), actual.clone()));
            }
        }
    }

    fn rollback_unification_errors(&self, range: ::std::ops::Range<usize>) -> bool {
        // If there were no errors in this unification, remove the errors generatedfrom the
        // first attempt
        let errors = self.unification_errors.borrow().errors.len();
        if range.end == errors {
            // No errors found
            let start = range.start;
            for _ in range {
                self.unification_errors
                    .borrow_mut()
                    .errors
                    .remove(start);
            }
            true
        } else {
            false
        }
    }

    fn unify_alias(&self,
                   expected: &TcType,
                   actual: &TcType,
                   range: ::std::ops::Range<usize>)
                   -> bool {
        match **actual {
            Type::Data(ast::TypeConstructor::Data(r), ref r_args) => {
                let r = match self.alias.type_of_alias(r, r_args) {
                    Ok(typ) => typ,
                    Err(err) => {
                        self.unification_error(err);
                        return false;
                    }
                };
                match r {
                    Some(r) => {
                        self.unify_(expected, &r);
                        self.rollback_unification_errors(range)
                    }
                    None => {
                        self.unification_error(Error::TypeMismatch(expected.clone(),
                                                                   actual.clone()));
                        false
                    }
                }
            }
            _ => false,
        }
    }

    fn unify_app<F>(&self, l: &ast::TypeConstructor<Symbol>, l_args: &[TcType], r: &TcType, f: &F)
        where F: Fn(&TcType, &TcType)
    {
        let r = self.alias.inst.subs.real(r);
        debug!("{:?} {:?} <==> {}",
               l,
               l_args,
               ast::display_type(&self.symbols, r));
        match **r {
            Type::App(ref r, ref r_arg) => {
                match l_args.last() {
                    Some(last) => {
                        f(last, r_arg);
                        self.unify_app(l, &l_args[0..l_args.len() - 1], r, f);
                    }
                    None => {
                        let l = Type::data(l.clone(), l_args.iter().cloned().collect());
                        self.unification_error(Error::TypeMismatch(l, r.clone()));
                    }
                }
            }
            Type::Data(ref r, ref r_args) if l == r && l_args.len() == r_args.len() => {
                for (l, r) in l_args.iter().zip(r_args) {
                    self.unify_(l, r);
                }
            }
            Type::Variable(ref r) => {
                self.union(r, &Type::data(l.clone(), l_args.iter().cloned().collect()))
            }
            _ => {
                let l = Type::data(l.clone(), l_args.iter().cloned().collect());
                self.unification_error(Error::TypeMismatch(l, r.clone()));
            }
        }
    }

    fn union(&self, id: &ast::TypeVariable, typ: &TcType) {
        if let Err(()) = self.alias.inst.subs.union(id, typ) {
            self.unification_error(Error::Occurs(id.clone(), typ.clone()));
        }
    }

    fn unify_function(&self, arg: &TcType, ret: &TcType, other: &TcType) {
        let error = || {
            let func = Type::function(vec![arg.clone()], ret.clone());
            self.unification_error(Error::TypeMismatch(func, other.clone()));
        };
        let other = self.alias.inst.subs.real(other);
        match **other {
            Type::App(ref other_f, ref other_ret) => {
                let other_f = self.alias.inst.subs.real(other_f);
                match **other_f {
                    Type::App(ref fn_prim, ref other_arg) => {
                        self.unify_(fn_prim, &Type::builtin(ast::BuiltinType::FunctionType));
                        self.unify_(arg, other_arg);
                        self.unify_(ret, other_ret);
                    }
                    _ => error(),
                }
            }
            _ => error(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::Error::*;
    use typecheck::{AliasInstantiator, Instantiator, TypeError};
    use base::ast;
    use base::ast::Type;
    use typecheck::tests::*;

    #[test]
    fn detect_multiple_type_errors_in_single_type() {
        let _ = ::env_logger::init();
        let (x, y, z, w) = (intern("x"), intern("y"), intern("z"), intern("w"));
        let l = Type::record(vec![],
                             vec![ast::Field {
                                      name: x,
                                      typ: Type::int(),
                                  },
                                  ast::Field {
                                      name: y,
                                      typ: Type::string(),
                                  }]);
        let r = Type::record(vec![],
                             vec![ast::Field {
                                      name: z,
                                      typ: Type::int(),
                                  },
                                  ast::Field {
                                      name: w,
                                      typ: Type::string(),
                                  }]);
        let inst = Instantiator::new();
        let i = get_local_interner();
        let symbols = i.borrow();
        let result = Unifier::new(AliasInstantiator::new(&inst, &()), &*symbols)
                         .unify(&l, r.clone());
        assert_eq!(result,
                   Err(TypeError::Unification(l.clone(),
                                              r.clone(),
                                              vec![FieldMismatch(x, z), FieldMismatch(y, w)])));
    }
}
