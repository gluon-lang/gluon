use std::cell::RefCell;
use std::collections::HashMap;
use std::error::Error as StdError;
use std::rc::Rc;

use base::ast;
use base::ast::MutVisitor;
use base::symbol::Symbol;
use typecheck::TcIdent;
use base::error::Errors;

pub type Error = Box<StdError>;

pub trait Macro<Env>: ::mopa::Any {
    fn expand(&self,
              env: &Env,
              arguments: &mut [ast::LExpr<TcIdent>])
              -> Result<ast::LExpr<TcIdent>, Error>;
}
mopafy!(Macro<Env>);

impl<F: ::mopa::Any, Env> Macro<Env> for F
    where F: Fn(&Env, &mut [ast::LExpr<TcIdent>]) -> Result<ast::LExpr<TcIdent>, Error>
{
    fn expand(&self,
              env: &Env,
              arguments: &mut [ast::LExpr<TcIdent>])
              -> Result<ast::LExpr<TcIdent>, Error> {
        self(env, arguments)
    }
}

pub struct MacroEnv<Env> {
    macros: RefCell<HashMap<Symbol, Rc<Macro<Env>>>>,
}

impl<Env> MacroEnv<Env> {
    pub fn new() -> MacroEnv<Env> {
        MacroEnv { macros: RefCell::new(HashMap::new()) }
    }

    pub fn insert<M>(&self, name: Symbol, mac: M)
        where M: Macro<Env> + 'static
    {
        self.macros.borrow_mut().insert(name, Rc::new(mac));
    }

    pub fn get(&self, name: Symbol) -> Option<Rc<Macro<Env>>> {
        self.macros.borrow().get(&name).cloned()
    }
}

pub struct MacroExpander<'a, Env: 'a> {
    env: &'a Env,
    macros: &'a MacroEnv<Env>,
    errors: Errors<Error>,
}

impl<'a, Env> MacroExpander<'a, Env> {
    pub fn new(env: &'a Env, macros: &'a MacroEnv<Env>) -> MacroExpander<'a, Env> {
        MacroExpander {
            env: env,
            macros: macros,
            errors: Errors::new(),
        }
    }

    pub fn run(mut self, expr: &mut ast::LExpr<TcIdent>) -> Result<(), Errors<Error>> {
        self.visit_expr(expr);
        if self.errors.has_errors() {
            Err(self.errors)
        } else {
            Ok(())
        }
    }
}

impl<'a, Env> MutVisitor for MacroExpander<'a, Env> {
    type T = TcIdent;

    fn visit_expr(&mut self, expr: &mut ast::LExpr<TcIdent>) {
        let replacement = match expr.value {
            ast::Expr::Call(ref mut id, ref mut args) => {
                match ***id {
                    ast::Expr::Identifier(ref id) => {
                        let mac = {
                            let macros = self.macros.macros.borrow();
                            macros.get(&id.name).cloned()
                        };
                        match mac {
                            Some(m) => {
                                match m.expand(self.env, args) {
                                    Ok(e) => Some(e),
                                    Err(err) => {
                                        self.errors.error(err);
                                        None
                                    }
                                }
                            }
                            None => None,
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        if let Some(mut e) = replacement {
            e.location = expr.location;
            *expr = e;
        }
        ast::walk_mut_expr(self, expr);
    }
}
