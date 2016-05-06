use std::iter::once;

use base::ast;
use base::scoped_map::ScopedMap;
use std::cmp::Ordering;

use base::ast::{DisplayEnv, Location, Typed};
use base::symbol::Symbol;
use base::types::{Type, TcType};

trait OnFound {
    fn on_ident(&mut self, ident: &ast::TcIdent<Symbol>) {
        let _ = ident;
    }
    fn on_expr(&mut self, expr: &ast::LExpr<ast::TcIdent<Symbol>>) {
        let _ = expr;
    }
    fn on_pattern(&mut self, pattern: &ast::LPattern<ast::TcIdent<Symbol>>) {
        let _ = pattern;
    }

    fn expr(&mut self, expr: &ast::LExpr<ast::TcIdent<Symbol>>);
    fn ident(&mut self, context: &ast::LExpr<ast::TcIdent<Symbol>>, ident: &ast::TcIdent<Symbol>);
}

struct GetType(Option<TcType>);
impl OnFound for GetType {
    fn expr(&mut self, expr: &ast::LExpr<ast::TcIdent<Symbol>>) {
        self.0 = Some(expr.type_of());
    }
    fn ident(&mut self,
             _context: &ast::LExpr<ast::TcIdent<Symbol>>,
             ident: &ast::TcIdent<Symbol>) {
        self.0 = Some(ident.type_of());
    }
}

struct Suggest {
    stack: ScopedMap<Symbol, ()>,
    result: Vec<Symbol>,
}
impl OnFound for Suggest {
    fn on_ident(&mut self, ident: &ast::TcIdent<Symbol>) {
        self.stack.insert(ident.name.clone(), ());
    }

    fn on_pattern(&mut self, pattern: &ast::LPattern<ast::TcIdent<Symbol>>) {
        match pattern.value {
            ast::Pattern::Record { ref fields, .. } => {
                for field in fields {
                    let f = field.1.as_ref().unwrap_or(&field.0).clone();
                    self.stack.insert(f, ());
                }
            }
            ast::Pattern::Identifier(ref id) => {
                self.stack.insert(id.name.clone(), ());
            }
            ast::Pattern::Constructor(_, ref args) => {
                for arg in args {
                    self.stack.insert(arg.name.clone(), ());
                }
            }
        }
    }

    fn expr(&mut self, expr: &ast::LExpr<ast::TcIdent<Symbol>>) {
        match expr.value {
            ast::Expr::Identifier(ref ident) => {
                let id = ident.name.as_ref();
                for (k, _) in self.stack.iter() {
                    if k.as_ref().starts_with(id) {
                        self.result.push(k.clone());
                    }
                }
            }
            _ => (),
        }
    }

    fn ident(&mut self, context: &ast::LExpr<ast::TcIdent<Symbol>>, ident: &ast::TcIdent<Symbol>) {
        match context.value {
            ast::Expr::FieldAccess(ref expr, _) => {
                match *expr.type_of() {
                    Type::Record { ref fields, .. } => {
                        let id = ident.name.as_ref();
                        for field in fields {
                            if field.name.as_ref().starts_with(id) {
                                self.result.push(field.name.clone());
                            }
                        }
                    }
                    _ => (),
                }
            }
            _ => (),
        }
    }
}

struct FindVisitor<'a, F> {
    env: &'a (DisplayEnv<Ident = ast::TcIdent<Symbol>> + 'a),
    location: Location,
    on_found: F,
}

impl<'a, F> FindVisitor<'a, F> {
    fn select_spanned<'e, I, S, T>(&self, iter: I, mut span: S) -> (bool, Option<&'e T>)
        where I: IntoIterator<Item = &'e T>,
              S: FnMut(&T) -> ast::Span
    {
        let mut iter = iter.into_iter().peekable();
        let mut prev = None;
        loop {
            match iter.peek() {
                Some(expr) => {
                    match span(expr).containment(&self.location) {
                        Ordering::Equal => {
                            break;
                        }
                        Ordering::Less if prev.is_some() => {
                            // Select the previous expression
                            return (true, prev);
                        }
                        _ => (),
                    }
                }
                None => return (true, prev),
            }
            prev = iter.next();
        }
        (false, iter.next())
    }
}

impl<'a, F> FindVisitor<'a, F>
    where F: OnFound
{
    fn visit_one<'e, I>(&mut self, iter: I)
        where I: IntoIterator<Item = &'e ast::LExpr<ast::TcIdent<Symbol>>>
    {
        let (_, expr) = self.select_spanned(iter, |e| e.span(self.env));
        self.visit_expr(expr.unwrap());
    }

    fn visit_pattern(&mut self, pattern: &ast::LPattern<ast::TcIdent<Symbol>>) {
        self.on_found.on_pattern(pattern);
    }
    fn visit_expr(&mut self, current: &ast::LExpr<ast::TcIdent<Symbol>>) {
        use base::ast::Expr::*;
        match current.value {
            Identifier(_) | Literal(_) => self.on_found.expr(current),
            Call(ref func, ref args) => {
                self.visit_one(once(&**func).chain(args));
            }
            IfElse(ref pred, ref if_true, ref if_false) => {
                self.visit_one([pred, if_true, if_false.as_ref().expect("false branch")]
                                   .iter()
                                   .map(|x| &***x))
            }
            Match(ref expr, ref alts) => {
                self.visit_one(once(&**expr).chain(alts.iter().map(|alt| &alt.expression)))
            }
            BinOp(ref l, ref op, ref r) => {
                match (l.span(self.env).containment(&self.location),
                       r.span(self.env).containment(&self.location)) {
                    (Ordering::Greater, Ordering::Less) => self.on_found.ident(current, op),
                    (_, Ordering::Greater) |
                    (_, Ordering::Equal) => self.visit_expr(r),
                    _ => self.visit_expr(l),
                }
            }
            Let(ref bindings, ref expr) => {
                for bind in bindings {
                    self.visit_pattern(&bind.name);
                }
                match self.select_spanned(bindings, |b| b.expression.span(self.env)) {
                    (false, Some(bind)) => {
                        for arg in &bind.arguments {
                            self.on_found.on_ident(&arg);
                        }
                        self.visit_expr(&bind.expression)
                    }
                    _ => self.visit_expr(expr),
                }
            }
            Type(_, ref expr) => self.visit_expr(expr),
            FieldAccess(ref expr, ref id) => {
                if expr.span(self.env).containment(&self.location) <= Ordering::Equal {
                    self.visit_expr(expr);
                } else {
                    self.on_found.ident(current, id);
                }
            }
            Array(ref array) => self.visit_one(&array.expressions),
            Record { ref exprs, .. } => {
                let exprs = exprs.iter().filter_map(|tup| tup.1.as_ref());
                if let (_, Some(expr)) = self.select_spanned(exprs, |e| e.span(self.env)) {
                    self.visit_expr(expr);
                }
            }
            Lambda(ref lambda) => {
                for arg in &lambda.arguments {
                    self.on_found.on_ident(&arg);
                }
                self.visit_expr(&lambda.body)
            }
            Tuple(ref args) => self.visit_one(args),
            Block(ref exprs) => self.visit_one(exprs),
        };
    }
}

pub fn find(env: &DisplayEnv<Ident = ast::TcIdent<Symbol>>,
            expr: &ast::LExpr<ast::TcIdent<Symbol>>,
            location: Location)
            -> Result<TcType, ()> {
    let mut visitor = FindVisitor {
        env: env,
        location: location,
        on_found: GetType(None),
    };
    visitor.visit_expr(expr);
    visitor.on_found.0.ok_or(())
}

pub fn suggest(env: &DisplayEnv<Ident = ast::TcIdent<Symbol>>,
               expr: &ast::LExpr<ast::TcIdent<Symbol>>,
               location: Location)
               -> Result<Vec<Symbol>, ()> {
    let mut visitor = FindVisitor {
        env: env,
        location: location,
        on_found: Suggest {
            stack: ScopedMap::new(),
            result: Vec::new(),
        },
    };
    visitor.visit_expr(expr);
    Ok(visitor.on_found.result)
}
