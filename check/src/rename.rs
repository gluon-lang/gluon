use std::fmt;

use base::ast;
use base::ast::{Typed, DisplayEnv, MutVisitor};
use base::scoped_map::ScopedMap;
use base::symbol::{Symbol, SymbolRef, SymbolModule};
use base::types;
use base::types::{Alias, TcType, Type, TcIdent, RcKind, KindEnv, TypeEnv};
use base::error::Errors;

pub type Error = Errors<ast::Spanned<RenameError>>;

#[derive(Clone, Debug, PartialEq)]
pub enum RenameError {
    NoMatchingType {
        symbol: String,
        expected: TcType,
        possible_types: Vec<(Option<ast::Location>, TcType)>,
    },
}

impl fmt::Display for RenameError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            RenameError::NoMatchingType { ref symbol, ref expected, ref possible_types } => {
                try!(writeln!(f,
                              "Could not resolve a binding for `{}` with type `{}`",
                              symbol,
                              expected));
                try!(writeln!(f, "Possibilities:"));
                for &(ref location, ref typ) in possible_types {
                    match *location {
                        Some(ref location) => try!(writeln!(f, "{} at {}", typ, location)),
                        None => try!(writeln!(f, "{} at 'global'", typ)),
                    }
                }
                Ok(())
            }
        }
    }
}

struct Environment<'b> {
    env: &'b TypeEnv,
    stack: ScopedMap<Symbol, (Symbol, ast::Location, TcType)>,
    stack_types: ScopedMap<Symbol, types::Alias<Symbol, TcType>>,
}

impl<'a> KindEnv for Environment<'a> {
    fn find_kind(&self, _type_name: &SymbolRef) -> Option<RcKind> {
        None
    }
}

impl<'a> TypeEnv for Environment<'a> {
    fn find_type(&self, id: &SymbolRef) -> Option<&TcType> {
        self.stack.get(id).map(|t| &t.2).or_else(|| self.env.find_type(id))
    }
    fn find_type_info(&self, id: &SymbolRef) -> Option<&types::Alias<Symbol, TcType>> {
        self.stack_types
            .get(id)
            .or_else(|| self.env.find_type_info(id))
    }
    fn find_record(&self, _fields: &[Symbol]) -> Option<(&TcType, &TcType)> {
        None
    }
}

pub fn rename(symbols: &mut SymbolModule,
              env: &TypeEnv,
              expr: &mut ast::LExpr<TcIdent>)
              -> Result<(), Error> {
    struct RenameVisitor<'a: 'b, 'b> {
        symbols: &'b mut SymbolModule<'a>,
        env: Environment<'b>,
        errors: Error,
    }
    impl<'a, 'b> RenameVisitor<'a, 'b> {
        fn find_fields(&self, typ: &TcType) -> Option<Vec<types::Field<Symbol, TcType>>> {
            // Walk through all type aliases
            match *instantiate::remove_aliases(&self.env, typ.clone()) {
                Type::Record { ref fields, .. } => Some(fields.to_owned()),
                _ => None,
            }
        }

        fn new_pattern(&mut self, typ: &TcType, pattern: &mut ast::LPattern<TcIdent>) {
            match pattern.value {
                ast::Pattern::Record { ref mut fields, ref types, .. } => {
                    let field_types = self.find_fields(typ).expect("field_types");
                    for field in fields.iter_mut() {
                        let field_type = field_types.iter()
                            .find(|field_type| field_type.name.name_eq(&field.0))
                            .expect("ICE: Existing field")
                            .typ
                            .clone();
                        let id = field.1.as_ref().unwrap_or_else(|| &field.0).clone();
                        field.1 = Some(self.stack_var(id, pattern.location, field_type));
                    }
                    let record_type = instantiate::remove_aliases(&self.env, typ.clone()).clone();
                    let imported_types = match *record_type {
                        Type::Record { ref types, .. } => types,
                        _ => panic!(),
                    };
                    for &(ref name, _) in types {
                        let field_type = imported_types.iter()
                            .find(|field| field.name.name_eq(name))
                            .expect("field_type");
                        self.stack_type(name.clone(), pattern.location, &field_type.typ);
                    }
                }
                ast::Pattern::Identifier(ref mut id) => {
                    let new_name =
                        self.stack_var(id.name.clone(), pattern.location, id.typ.clone());
                    id.name = new_name;
                }
                ast::Pattern::Constructor(ref mut id, ref mut args) => {
                    let typ = self.env
                        .find_type(id.id())
                        .expect("ICE: Expected constructor")
                        .clone();
                    for (arg_type, arg) in types::arg_iter(&typ).zip(args) {
                        arg.name =
                            self.stack_var(arg.name.clone(), pattern.location, arg_type.clone());
                    }
                }
            }
        }

        fn stack_var(&mut self, id: Symbol, location: ast::Location, typ: TcType) -> Symbol {
            let old_id = id.clone();
            let name = self.symbols.string(&id).to_owned();
            let new_id = self.symbols.symbol(format!("{}:{}", name, location));
            debug!("Rename binding `{}` = `{}` `{}`",
                   self.symbols.string(&old_id),
                   self.symbols.string(&new_id),
                   types::display_type(&self.symbols, &typ));
            self.env.stack.insert(old_id, (new_id.clone(), location, typ));
            new_id

        }

        fn stack_type(&mut self,
                      id: Symbol,
                      location: ast::Location,
                      alias: &Alias<Symbol, TcType>) {
            // Insert variant constructors into the local scope
            if let Some(ref real_type) = alias.typ {
                if let Type::Variants(ref variants) = **real_type {
                    for &(ref name, ref typ) in variants {
                        self.env.stack.insert(name.clone(), (name.clone(), location, typ.clone()));
                    }
                }
            }
            // FIXME: Workaround so that both the types name in this module and its global
            // name are imported. Without this aliases may not be traversed properly
            self.env.stack_types.insert(alias.name.clone(), alias.clone());
            self.env.stack_types.insert(id, alias.clone());
        }

        /// Renames `id` to the unique identifier which have the type `expected`
        /// Returns `Some(new_id)` if renaming was necessary or `None` if no renaming was necessary
        /// as `id` was currently unique (#Int+, #Float*, etc)
        fn rename(&self, id: &Symbol, expected: &TcType) -> Result<Option<Symbol>, RenameError> {
            let locals = self.env
                .stack
                .get_all(id);
            let global = self.env.env.find_type(id).map(|typ| (id, None, typ));
            let candidates = || {
                locals.iter()
                    .flat_map(|bindings| {
                        bindings.iter().rev().map(|bind| (&bind.0, Some(&bind.1), &bind.2))
                    })
                    .chain(global)
            };
            // If there is a single binding (or no binding in case of primitives such as #Int+)
            // there is no need to check for equivalency as typechecker couldnt have infered a
            // different binding
            if candidates().count() <= 1 {
                return Ok(candidates().next().map(|tup| tup.0.clone()));
            }
            candidates()
                .find(|tup| equivalent(&self.env, tup.2, expected))
                .map(|tup| Some(tup.0.clone()))
                .ok_or_else(|| {
                    RenameError::NoMatchingType {
                        symbol: String::from(self.symbols.string(id)),
                        expected: expected.clone(),
                        possible_types: candidates()
                            .map(|tup| (tup.1.cloned(), tup.2.clone()))
                            .collect(),
                    }
                })
        }

        fn rename_expr(&mut self, expr: &mut ast::LExpr<TcIdent>) -> Result<(), RenameError> {
            match expr.value {
                ast::Expr::Identifier(ref mut id) => {
                    if let Some(new_id) = try!(self.rename(&id.name, &id.typ)) {
                        debug!("Rename identifier {} = {}", id.name, new_id);
                        id.name = new_id;
                    }
                }
                ast::Expr::Record { ref mut typ, ref mut exprs, .. } => {
                    let field_types = self.find_fields(&typ.typ).expect("field_types");
                    for (field, &mut (ref id, ref mut maybe_expr)) in field_types.iter()
                        .zip(exprs) {
                        match *maybe_expr {
                            Some(ref mut expr) => self.visit_expr(expr),
                            None => {
                                if let Some(new_id) = try!(self.rename(id, &field.typ)) {
                                    debug!("Rename record field {} = {}", id, new_id);
                                    *maybe_expr =
                                        Some(ast::no_loc(ast::Expr::Identifier(ast::TcIdent {
                                            name: new_id,
                                            typ: field.typ.clone(),
                                        })));
                                }
                            }
                        }
                    }
                }
                ast::Expr::BinOp(ref mut l, ref mut id, ref mut r) => {
                    if let Some(new_id) = try!(self.rename(id.id(), &id.typ)) {
                        debug!("Rename {} = {}",
                               self.symbols.string(&id.name),
                               self.symbols.string(&new_id));
                        id.name = new_id;
                    }
                    self.visit_expr(l);
                    self.visit_expr(r);
                }
                ast::Expr::Match(ref mut expr, ref mut alts) => {
                    self.visit_expr(expr);
                    for alt in alts {
                        self.env.stack_types.enter_scope();
                        self.env.stack.enter_scope();
                        let typ = expr.env_type_of(&self.env);
                        self.new_pattern(&typ, &mut alt.pattern);
                        self.visit_expr(&mut alt.expression);
                        self.env.stack.exit_scope();
                        self.env.stack_types.exit_scope();
                    }
                }
                ast::Expr::Let(ref mut bindings, ref mut expr) => {
                    self.env.stack_types.enter_scope();
                    self.env.stack.enter_scope();
                    let is_recursive = bindings.iter().all(|bind| !bind.arguments.is_empty());
                    for bind in bindings.iter_mut() {
                        if !is_recursive {
                            self.visit_expr(&mut bind.expression);
                        }
                        let typ = bind.env_type_of(&self.env);
                        self.new_pattern(&typ, &mut bind.name);
                    }
                    if is_recursive {
                        for bind in bindings {
                            self.env.stack.enter_scope();
                            for (typ, arg) in types::arg_iter(&bind.env_type_of(&self.env))
                                .zip(&mut bind.arguments) {
                                arg.name =
                                    self.stack_var(arg.name.clone(), expr.location, typ.clone());
                            }
                            self.visit_expr(&mut bind.expression);
                            self.env.stack.exit_scope();
                        }
                    }
                    self.visit_expr(expr);
                    self.env.stack.exit_scope();
                    self.env.stack_types.exit_scope();
                }
                ast::Expr::Lambda(ref mut lambda) => {
                    self.env.stack.enter_scope();
                    for (typ, arg) in types::arg_iter(&lambda.id.typ).zip(&mut lambda.arguments) {
                        arg.name = self.stack_var(arg.name.clone(), expr.location, typ.clone());
                    }
                    self.visit_expr(&mut lambda.body);
                    self.env.stack.exit_scope();
                }
                ast::Expr::Type(ref bindings, ref mut body) => {
                    self.env.stack_types.enter_scope();
                    for bind in bindings {
                        self.stack_type(bind.name.clone(), expr.location, &bind.alias);
                    }
                    self.visit_expr(body);
                    self.env.stack_types.exit_scope();
                }
                _ => ast::walk_mut_expr(self, expr),
            }
            Ok(())
        }
    }
    impl<'a, 'b> MutVisitor for RenameVisitor<'a, 'b> {
        type T = ast::TcIdent<Symbol>;

        fn visit_expr(&mut self, expr: &mut ast::LExpr<Self::T>) {
            if let Err(err) = self.rename_expr(expr) {
                self.errors.error(ast::Spanned {
                    span: expr.span(&ast::TcIdentEnvWrapper(&self.symbols)),
                    value: err,
                });
            }
        }
    }
    let mut visitor = RenameVisitor {
        symbols: symbols,
        errors: Errors::new(),
        env: Environment {
            env: env,
            stack: ScopedMap::new(),
            stack_types: ScopedMap::new(),
        },
    };
    visitor.visit_expr(expr);
    if visitor.errors.has_errors() {
        Err(visitor.errors)
    } else {
        Ok(())
    }
}


use base::instantiate;
use unify_type::{TypeError, State};
use unify::{Error as UnifyError, Unifier, Unifiable, UnifierState};

use base::fnv::FnvMap;

pub fn equivalent(env: &TypeEnv, actual: &TcType, inferred: &TcType) -> bool {
    let mut unifier = UnifierState {
        state: State::new(env),
        unifier: Equivalent {
            map: FnvMap::default(),
            equiv: true,
        },
    };
    unifier.try_match(actual, inferred);
    unifier.unifier.equiv
}

struct Equivalent {
    map: FnvMap<Symbol, TcType>,
    equiv: bool,
}

impl<'a> Unifier<State<'a>, TcType> for Equivalent {
    fn report_error(_unifier: &mut UnifierState<State<'a>, Self>,
                    _error: UnifyError<TcType, TypeError<Symbol>>) {
    }

    fn try_match(unifier: &mut UnifierState<State<'a>, Self>,
                 l: &TcType,
                 r: &TcType)
                 -> Option<TcType> {
        debug!("{} ====> {}", l, r);
        match (&**l, &**r) {
            (&Type::Generic(ref gl), &Type::Generic(ref gr)) if gl == gr => None,
            (&Type::Generic(ref gl), _) => {
                match unifier.unifier.map.get(&gl.id).cloned() {
                    Some(ref typ) => unifier.try_match(typ, r),
                    None => {
                        unifier.unifier.map.insert(gl.id.clone(), r.clone());
                        None
                    }
                }
            }
            _ => {
                match l.zip_match(r, unifier) {
                    Ok(typ) => typ,
                    Err(_) => {
                        unifier.unifier.equiv = false;
                        None
                    }
                }
            }
        }
    }
}
