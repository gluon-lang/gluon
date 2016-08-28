//! Primitive auto completion and type quering on ASTs

use std::iter::once;
use std::cmp::Ordering;

use base::ast::{Expr, SpannedExpr, SpannedPattern, Pattern, TcIdent, Typed};
use base::instantiate;
use base::pos::{BytePos, Span};
use base::scoped_map::ScopedMap;
use base::symbol::Symbol;
use base::types::{TcType, Type, TypeEnv};

trait OnFound {
    fn on_ident(&mut self, ident: &TcIdent<Symbol>) {
        let _ = ident;
    }

    fn on_pattern(&mut self, pattern: &SpannedPattern<TcIdent<Symbol>>) {
        let _ = pattern;
    }

    fn expr(&mut self, expr: &SpannedExpr<TcIdent<Symbol>>);

    fn ident(&mut self, context: &SpannedExpr<TcIdent<Symbol>>, ident: &TcIdent<Symbol>);

    /// Location points to whitespace
    fn nothing(&mut self);
}

struct GetType<E> {
    env: E,
    typ: Option<TcType>,
}

impl<E: TypeEnv> OnFound for GetType<E> {
    fn expr(&mut self, expr: &SpannedExpr<TcIdent<Symbol>>) {
        self.typ = Some(expr.env_type_of(&self.env));
    }

    fn ident(&mut self, _context: &SpannedExpr<TcIdent<Symbol>>, ident: &TcIdent<Symbol>) {
        self.typ = Some(ident.env_type_of(&self.env));
    }
    fn nothing(&mut self) {}
}

pub struct Suggestion {
    pub name: String,
    pub typ: TcType,
}

struct Suggest<E> {
    env: E,
    stack: ScopedMap<Symbol, TcType>,
    result: Vec<Suggestion>,
}

impl<E: TypeEnv> OnFound for Suggest<E> {
    fn on_ident(&mut self, ident: &TcIdent<Symbol>) {
        self.stack.insert(ident.name.clone(), ident.typ.clone());
    }

    fn on_pattern(&mut self, pattern: &SpannedPattern<TcIdent<Symbol>>) {
        match pattern.value {
            Pattern::Record { ref id, fields: ref field_ids, .. } => {
                let unaliased = instantiate::remove_aliases(&self.env, id.typ.clone());
                if let Type::Record { ref fields, .. } = *unaliased {
                    for (field, field_type) in field_ids.iter().zip(fields) {
                        let f = field.1.as_ref().unwrap_or(&field.0).clone();
                        self.stack.insert(f, field_type.typ.clone());
                    }
                }
            }
            Pattern::Identifier(ref id) => {
                self.stack.insert(id.name.clone(), id.typ.clone());
            }
            Pattern::Constructor(_, ref args) => {
                for arg in args {
                    self.stack.insert(arg.name.clone(), arg.typ.clone());
                }
            }
        }
    }

    fn expr(&mut self, expr: &SpannedExpr<TcIdent<Symbol>>) {
        if let Expr::Identifier(ref ident) = expr.value {
            for (k, typ) in self.stack.iter() {
                if k.declared_name().starts_with(ident.name.declared_name()) {
                    self.result.push(Suggestion {
                        name: k.declared_name().into(),
                        typ: typ.clone(),
                    });
                }
            }
        }
    }

    fn ident(&mut self, context: &SpannedExpr<TcIdent<Symbol>>, ident: &TcIdent<Symbol>) {
        if let Expr::FieldAccess(ref expr, _) = context.value {
            let typ = instantiate::remove_aliases(&self.env, expr.env_type_of(&self.env));
            if let Type::Record { ref fields, .. } = *typ {
                let id = ident.name.as_ref();
                for field in fields {
                    if field.name.as_ref().starts_with(id) {
                        self.result.push(Suggestion {
                            name: field.name.declared_name().into(),
                            typ: field.typ.clone(),
                        });
                    }
                }
            }
        }
    }

    fn nothing(&mut self) {
        self.result.extend(self.stack.iter().map(|(name, typ)| {
            Suggestion {
                name: name.declared_name().into(),
                typ: typ.clone(),
            }
        }));
    }
}

struct FindVisitor<F> {
    pos: BytePos,
    on_found: F,
}

impl<F> FindVisitor<F> {
    fn select_spanned<'e, I, S, T>(&self, iter: I, mut span: S) -> (bool, Option<&'e T>)
        where I: IntoIterator<Item = &'e T>,
              S: FnMut(&T) -> Span<BytePos>
    {
        let mut iter = iter.into_iter().peekable();
        let mut prev = None;
        loop {
            match iter.peek() {
                Some(expr) => {
                    match span(expr).containment(&self.pos) {
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

impl<F> FindVisitor<F>
    where F: OnFound
{
    fn visit_one<'e, I>(&mut self, iter: I)
        where I: IntoIterator<Item = &'e SpannedExpr<TcIdent<Symbol>>>
    {
        let (_, expr) = self.select_spanned(iter, |e| e.span);
        self.visit_expr(expr.unwrap());
    }

    fn visit_pattern(&mut self, pattern: &SpannedPattern<TcIdent<Symbol>>) {
        self.on_found.on_pattern(pattern);
    }

    fn visit_expr(&mut self, current: &SpannedExpr<TcIdent<Symbol>>) {
        use base::ast::Expr::*;

        match current.value {
            Identifier(_) | Literal(_) => {
                if current.span.containment(&self.pos) == Ordering::Equal {
                    self.on_found.expr(current)
                } else {
                    self.on_found.nothing()
                }
            }
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
                match (l.span.containment(&self.pos), r.span.containment(&self.pos)) {
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
                match self.select_spanned(bindings, |b| b.expression.span) {
                    (false, Some(bind)) => {
                        for arg in &bind.arguments {
                            self.on_found.on_ident(arg);
                        }
                        self.visit_expr(&bind.expression)
                    }
                    _ => self.visit_expr(expr),
                }
            }
            Type(_, ref expr) => self.visit_expr(expr),
            FieldAccess(ref expr, ref id) => {
                if expr.span.containment(&self.pos) <= Ordering::Equal {
                    self.visit_expr(expr);
                } else {
                    self.on_found.ident(current, id);
                }
            }
            Array(ref array) => self.visit_one(&array.expressions),
            Record { ref exprs, .. } => {
                let exprs = exprs.iter().filter_map(|tup| tup.1.as_ref());
                if let (_, Some(expr)) = self.select_spanned(exprs, |e| e.span) {
                    self.visit_expr(expr);
                }
            }
            Lambda(ref lambda) => {
                for arg in &lambda.arguments {
                    self.on_found.on_ident(arg);
                }
                self.visit_expr(&lambda.body)
            }
            Tuple(ref args) => self.visit_one(args),
            Block(ref exprs) => self.visit_one(exprs),
        };
    }
}

pub fn find<T>(env: &T, expr: &SpannedExpr<TcIdent<Symbol>>, pos: BytePos) -> Result<TcType, ()>
    where T: TypeEnv
{
    let mut visitor = FindVisitor {
        pos: pos,
        on_found: GetType {
            env: env,
            typ: None,
        },
    };
    visitor.visit_expr(expr);
    visitor.on_found.typ.ok_or(())
}

pub fn suggest<T>(env: &T,
                  expr: &SpannedExpr<TcIdent<Symbol>>,
                  pos: BytePos)
                  -> Vec<Suggestion>
    where T: TypeEnv
{
    let mut visitor = FindVisitor {
        pos: pos,
        on_found: Suggest {
            env: env,
            stack: ScopedMap::new(),
            result: Vec::new(),
        },
    };
    visitor.visit_expr(expr);
    visitor.on_found.result
}
