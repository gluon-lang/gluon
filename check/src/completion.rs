use std::iter::once;

use base::ast;
use std::cmp::Ordering;

use base::ast::{DisplayEnv, Location, Typed};
use base::symbol::Symbol;
use base::types::TcType;

trait OnFound {
    fn expr(&mut self, expr: &mut ast::LExpr<ast::TcIdent<Symbol>>);
    fn ident(&mut self, ident: &mut ast::TcIdent<Symbol>);
}

struct GetType(Option<TcType>);
impl OnFound for GetType {
    fn expr(&mut self, expr: &mut ast::LExpr<ast::TcIdent<Symbol>>) {
        self.0 = Some(expr.type_of());
    }
    fn ident(&mut self, ident: &mut ast::TcIdent<Symbol>) {
        self.0 = Some(ident.type_of());
    }
}

struct FindVisitor<'a, F> {
    env: &'a (DisplayEnv<Ident = ast::TcIdent<Symbol>> + 'a),
    location: Location,
    on_found: F,
}

impl<'a, F> FindVisitor<'a, F> {

    fn select_expr<'e, I>(&mut self, iter: I) -> Option<&'e mut ast::LExpr<ast::TcIdent<Symbol>>>
    where I: Iterator<Item=&'e mut ast::LExpr<ast::TcIdent<Symbol>>>
    {
        let mut iter = iter.peekable();
        let mut prev = None;
        loop {
            match iter.peek() {
                Some(expr) => {
                    match expr.span(self.env).containment(&self.location) {
                        Ordering::Equal => {
                            break;
                        }
                        Ordering::Less if prev.is_some() => {
                            // Select the previous expression
                            return prev;
                        }
                        _ => ()
                    }
                }
                None => return prev,
            }
            prev = iter.next();
        }
        iter.next()
    }
}

impl<'a, F> FindVisitor<'a, F>
where F: OnFound
{
    fn visit_one<'e, I>(&mut self, iter: I)
    where I: IntoIterator<Item=&'e mut ast::LExpr<ast::TcIdent<Symbol>>>
    {
        let expr = self.select_expr(iter.into_iter()).unwrap();
        self.visit_expr(expr);
    }

    fn visit_expr(&mut self, expr: &mut ast::LExpr<ast::TcIdent<Symbol>>) {
        use base::ast::Expr::*;
        match expr.value {
            Identifier(_) | Literal(_) => self.on_found.expr(expr),
            Call(ref mut func, ref mut args) => {
                self.visit_one(once(&mut **func).chain(args));
            }
            IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
                self.visit_one([pred, if_true, if_false.as_mut().expect("false branch")].iter_mut().map(|x| &mut ***x))
            }
            Match(ref mut expr, ref mut alts) => {
                self.visit_one(once(&mut **expr).chain(alts.iter_mut().map(|alt| &mut alt.expression)))
            }
            BinOp(ref mut l, ref mut op, ref mut r) => {
                match (l.span(self.env).containment(&self.location), r.span(self.env).containment(&self.location)) {
                    (Ordering::Greater, Ordering::Less) => self.on_found.ident(op),
                    (_, Ordering::Greater) | (_, Ordering::Equal) => self.visit_expr(r),
                    _ => self.visit_expr(l),
                }
            }
            Let(ref mut bindings, ref mut expr) => {
                self.visit_one(bindings.iter_mut().map(|bind| &mut bind.expression).chain(once(&mut **expr)))
            }
            Type(_, ref mut expr) => self.visit_expr(expr),
            FieldAccess(ref mut expr, ref mut id) => {
                if expr.span(self.env).containment(&self.location) <= Ordering::Equal {
                    self.visit_expr(expr);
                }
                else {
                    self.on_found.ident(id);
                }
            }
            Array(ref mut array) => {
                self.visit_one(&mut array.expressions)
            }
            Record { ref mut exprs, .. } => {
                if let Some(expr) = self.select_expr(exprs.iter_mut().filter_map(|tup| tup.1.as_mut())) {
                    self.visit_expr(expr);
                }
            }
            Lambda(ref mut lambda) => self.visit_expr(&mut lambda.body),
            Tuple(ref mut args) => self.visit_one(args),
            Block(ref mut exprs) => self.visit_one(exprs),
        };
    }
}
pub fn find(env: &DisplayEnv<Ident = ast::TcIdent<Symbol>>, expr: &mut ast::LExpr<ast::TcIdent<Symbol>>, location: Location) -> Result<TcType, ()> {
    let mut visitor = FindVisitor {
        env: env,
        location: location,
        on_found: GetType(None),
    };
    visitor.visit_expr(expr);
    visitor.on_found.0.ok_or(())
}
