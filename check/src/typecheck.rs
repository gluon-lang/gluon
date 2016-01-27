use std::fmt;
use std::mem;

use base::scoped_map::ScopedMap;
use base::ast;
use base::ast::{DisplayEnv, MutVisitor, RcKind};
use base::error::Errors;
use base::symbol::{Name, Symbol, SymbolModule, Symbols};
use base::types::{KindEnv, TypeEnv};
use instantiate::{AliasInstantiator, Instantiator};
use kindcheck;
use substitution::Substitution;
use unify::Error as UnifyError;
use unify;
use base::types::Typed;

use self::TypeError::*;

pub use base::ast::{TypeVariable, Type, Kind};

pub use base::types::TcType;

pub type TcIdent = ast::TcIdent<Symbol>;

type ErrType = ast::ASTType<String>;

#[derive(Debug, PartialEq)]
pub enum TypeError<I> {
    UndefinedVariable(I),
    NotAFunction(ast::ASTType<I>),
    UndefinedType(I),
    UndefinedField(ast::ASTType<I>, I),
    PatternError(ast::ASTType<I>, usize),
    Unification(ast::ASTType<I>, ast::ASTType<I>, Vec<::unify_type::Error<I>>),
    KindError(kindcheck::Error<I>),
    Rename(::rename::RenameError),
    DuplicateTypeDefinition(I),
    InvalidFieldAccess(ast::ASTType<I>),
    StringError(&'static str),
}

fn map_symbol(symbols: &SymbolModule,
              err: &ast::Spanned<TypeError<Symbol>>)
              -> ast::Spanned<TypeError<String>> {
    use self::TypeError::*;
    use unify::Error::{TypeMismatch, Occurs, Other};
    use unify_type::TypeError::FieldMismatch;

    let f = |symbol| String::from(symbols.string(symbol));

    let result = match err.value {
        UndefinedVariable(ref name) => UndefinedVariable(f(name)),
        NotAFunction(ref typ) => NotAFunction(typ.clone_strings(symbols)),
        UndefinedType(ref name) => UndefinedType(f(name)),
        UndefinedField(ref typ, ref field) => UndefinedField(typ.clone_strings(symbols), f(field)),
        Unification(ref expected, ref actual, ref errors) => {
            let errors = errors.iter()
                               .map(|error| {
                                   match *error {
                                       TypeMismatch(ref l, ref r) => {
                                           TypeMismatch(l.clone_strings(symbols),
                                                        r.clone_strings(symbols))
                                       }
                                       Occurs(ref var, ref typ) => {
                                           Occurs(var.clone(), typ.clone_strings(symbols))
                                       }
                                       Other(::unify_type::TypeError::UndefinedType(ref id)) => {
                                           Other(::unify_type::TypeError::UndefinedType(f(&id)))
                                       }
                                       Other(FieldMismatch(ref l, ref r)) => {
                                           Other(FieldMismatch(f(l), f(r)))
                                       }
                                   }
                               })
                               .collect();
            Unification(expected.clone_strings(symbols),
                        actual.clone_strings(symbols),
                        errors)
        }
        PatternError(ref typ, expected_len) => {
            PatternError(typ.clone_strings(symbols), expected_len)
        }
        KindError(ref err) => {
            KindError(match *err {
                TypeMismatch(ref l, ref r) => TypeMismatch(l.clone(), r.clone()),
                Occurs(ref var, ref typ) => Occurs(var.clone(), typ.clone()),
                Other(::kindcheck::KindError::UndefinedType(ref x)) => {
                    Other(::kindcheck::KindError::UndefinedType(f(x)))
                }
            })
        }
        Rename(ref err) => Rename(err.clone()),
        DuplicateTypeDefinition(ref id) => DuplicateTypeDefinition(f(id)),
        InvalidFieldAccess(ref typ) => InvalidFieldAccess(typ.clone_strings(symbols)),
        StringError(name) => StringError(name),
    };
    ast::Spanned {
        span: err.span,
        value: result,
    }
}

fn map_symbols(symbols: &SymbolModule, errors: &Errors<ast::Spanned<TypeError<Symbol>>>) -> Error {
    Errors {
        errors: errors.errors
                      .iter()
                      .map(|e| map_symbol(symbols, e))
                      .collect(),
    }
}

impl<I> From<kindcheck::Error<I>> for TypeError<I> where I: PartialEq + Clone
{
    fn from(e: kindcheck::Error<I>) -> TypeError<I> {
        match e {
            UnifyError::Other(::kindcheck::KindError::UndefinedType(name)) => UndefinedType(name),
            e => KindError(e),
        }
    }
}

impl <I> From<::rename::RenameError> for TypeError<I> {
    fn from(e: ::rename::RenameError) -> TypeError<I> {
        TypeError::Rename(e)
    }
}

impl<I: fmt::Display + ::std::ops::Deref<Target = str>> fmt::Display for TypeError<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::TypeError::*;
        match *self {
            UndefinedVariable(ref name) => write!(f, "Undefined variable `{}`", name),
            NotAFunction(ref typ) => write!(f, "`{}` is not a function", typ),
            UndefinedType(ref name) => write!(f, "Type `{}` is not defined", name),
            UndefinedField(ref typ, ref field) => {
                write!(f, "Type `{}` does not have the field `{}`", typ, field)
            }
            Unification(ref expected, ref actual, ref errors) => {
                try!(writeln!(f,
                              "Expected the following types to be equal\nExpected: {}\nFound: \
                               {}\n{} errors were found during unification:",
                              expected,
                              actual,
                              errors.len()));
                if errors.len() == 0 {
                    return Ok(());
                }
                for error in &errors[..errors.len() - 1] {
                    try!(::unify_type::fmt_error(error, f));
                    try!(writeln!(f, ""));
                }
                ::unify_type::fmt_error(errors.last().unwrap(), f)
            }
            PatternError(ref typ, expected_len) => {
                write!(f, "Type {} has {} to few arguments", typ, expected_len)
            }
            KindError(ref err) => ::kindcheck::fmt_kind_error(err, f),
            Rename(ref err) => write!(f, "{}", err),
            DuplicateTypeDefinition(ref id) => {
                write!(f,
                       "Type '{}' has been already been defined in this module",
                       id)
            }
            InvalidFieldAccess(ref typ) => {
                write!(f,
                       "Type '{}' is not a type which allows field accesses",
                       typ)
            }
            StringError(ref name) => write!(f, "{}", name),
        }
    }
}

pub type TcResult<T = TcType> = Result<T, TypeError<Symbol>>;

pub struct Environment<'a> {
    pub environment: Option<&'a (TypeEnv + 'a)>,
    pub stack: ScopedMap<Symbol, TcType>,
    pub stack_types: ScopedMap<Symbol, (TcType, Vec<ast::Generic<Symbol>>, TcType)>,
}

impl<'a> KindEnv for Environment<'a> {
    fn find_kind(&self, type_name: Symbol) -> Option<RcKind> {
        self.stack_types
            .get(&type_name)
            .map(|&(_, ref args, _)| {
                let mut kind = ast::Kind::star();
                for arg in args.iter().rev() {
                    kind = Kind::function(arg.kind.clone(), kind);
                }
                kind
            })
            .or_else(|| self.environment.and_then(|env| env.find_kind(type_name)))
    }
}

impl<'a> TypeEnv for Environment<'a> {
    fn find_type(&self, id: &Symbol) -> Option<&TcType> {
        let stack = &self.stack;
        let environment = &self.environment;
        match stack.get(id) {
            Some(x) => Some(x),
            None => environment.and_then(|e| e.find_type(id)),
        }
    }
    fn find_type_info(&self, id: &Symbol) -> Option<(&[ast::Generic<Symbol>], Option<&TcType>)> {
        self.stack_types
            .get(id)
            .map(|&(_, ref generics, ref typ)| (&generics[..], Some(typ)))
            .or_else(|| self.environment.and_then(|e| e.find_type_info(id)))
    }
    fn find_record(&self, fields: &[Symbol]) -> Option<(&TcType, &TcType)> {
        self.stack_types
            .iter()
            .find(|&(_, &(_, _, ref typ))| {
                match **typ {
                    Type::Record { fields: ref record_fields, .. } => {
                        fields.iter().all(|&name| record_fields.iter().any(|f| f.name == name))
                    }
                    _ => false,
                }
            })
            .map(|t| (&(t.1).0, &(t.1).2))
            .or_else(|| self.environment.and_then(|e| e.find_record(fields)))
    }
}

pub struct Typecheck<'a> {
    environment: Environment<'a>,
    symbols: SymbolModule<'a>,
    /// Mapping from the fresh symbol generated during typechecking to the symbol that was assigned
    /// during typechecking
    original_symbols: ScopedMap<Symbol, Symbol>,
    inst: Instantiator,
    errors: Errors<ast::Spanned<TypeError<Symbol>>>,
}

pub type Error = Errors<ast::Spanned<TypeError<String>>>;

impl<'a> Typecheck<'a> {
    pub fn new(module: String, symbols: &'a mut Symbols) -> Typecheck<'a> {
        let mut symbols = SymbolModule::new(module, symbols);
        for t in ["Int", "Float"].iter() {
            for op in "+-*/".chars() {
                symbols.symbol(format!("#{}{}", t, op));
            }
        }
        Typecheck {
            environment: Environment {
                environment: None,
                stack: ScopedMap::new(),
                stack_types: ScopedMap::new(),
            },
            symbols: symbols,
            original_symbols: ScopedMap::new(),
            inst: Instantiator::new(),
            errors: Errors::new(),
        }
    }

    fn find(&mut self, id: &Symbol) -> TcResult {
        let t: Option<&TcType> = {
            match self.environment.stack.get(id) {
                Some(x) => Some(x),
                None => self.environment.environment.and_then(|e| e.find_type(id)),
            }
        };
        match t {
            Some(typ) => {
                let x = self.inst.instantiate(typ);
                debug!("Find {} : {}",
                       self.symbols.string(id),
                       ast::display_type(&self.symbols, &x));
                Ok(x)
            }
            None => Err(UndefinedVariable(id.clone())),
        }
    }

    fn find_record(&self, fields: &[Symbol]) -> Result<(&TcType, &TcType), TypeError<Symbol>> {
        self.environment
            .find_record(fields)
            .map(|s| Ok(s))
            .unwrap_or_else(|| Err(StringError("Expected fields")))
    }

    fn find_type_info(&self, id: &Symbol) -> TcResult<(&[ast::Generic<Symbol>], Option<&TcType>)> {
        self.environment
            .find_type_info(id)
            .map(|s| Ok(s))
            .unwrap_or_else(|| Err(UndefinedType(id.clone())))
    }

    fn stack_var(&mut self, id: Symbol, typ: TcType) {
        self.environment.stack.insert(id, typ);
    }

    fn stack_type(&mut self,
                  id: Symbol,
                  typ: TcType,
                  generics: Vec<ast::Generic<Symbol>>,
                  real_type: TcType) {
        // Insert variant constructors into the local scope
        if let Type::Variants(ref variants) = *real_type {
            for &(name, ref typ) in variants {
                self.stack_var(name, typ.clone());
            }
        }
        if let Type::Data(ast::TypeConstructor::Data(id), _) = *typ {
            // FIXME: Workaround so that both the types name in this module and its global
            // name are imported. Without this aliases may not be traversed properly
            self.environment
                .stack_types
                .insert(id, (typ.clone(), generics.clone(), real_type.clone()));
        }
        self.environment.stack_types.insert(id, (typ, generics, real_type));
    }

    fn enter_scope(&mut self) {
        self.environment.stack.enter_scope();
        self.environment.stack_types.enter_scope();
        self.original_symbols.enter_scope();
    }

    fn exit_scope(&mut self) {
        self.environment.stack.exit_scope();
        self.environment.stack_types.exit_scope();
        self.original_symbols.exit_scope();
    }

    pub fn add_environment(&mut self, env: &'a TypeEnv) {
        self.environment.environment = Some(env);
    }

    fn generalize_variables(&mut self, level: u32, expr: &mut ast::LExpr<TcIdent>) {
        // Replace all type variables with their inferred types
        struct ReplaceVisitor<'a, 'b: 'a> {
            level: u32,
            tc: &'a mut Typecheck<'b>,
        }
        impl<'a, 'b> MutVisitor for ReplaceVisitor<'a, 'b> {
            type T = TcIdent;
            fn visit_identifier(&mut self, id: &mut TcIdent) {
                id.typ = self.tc.finish_type(self.level, id.typ.clone());
            }
        }
        let mut stack = mem::replace(&mut self.environment.stack, ScopedMap::new());
        for (_, vec) in stack.iter_mut() {
            for typ in vec {
                *typ = self.finish_type(level, typ.clone());
            }
        }
        mem::swap(&mut self.environment.stack, &mut stack);
        ReplaceVisitor {
            level: level,
            tc: self,
        }
        .visit_expr(expr);
    }

    pub fn typecheck_expr(&mut self, expr: &mut ast::LExpr<TcIdent>) -> Result<TcType, Error> {
        self.inst.subs.clear();
        self.environment.stack.clear();

        let mut typ = self.typecheck(expr).unwrap();
        if self.errors.has_errors() {
            Err(map_symbols(&self.symbols, &self.errors))
        } else {
            typ = self.finish_type(0, typ);
            typ = ast::walk_move_type(typ, &mut unroll_app);
            self.generalize_variables(0, expr);
            match ::rename::rename(&mut self.symbols, &self.environment, expr) {
                Ok(()) => Ok(typ),
                Err(errors) => {
                    for ast::Spanned { span, value } in errors.errors {
                        self.errors.error(ast::Spanned { span: span, value: value.into() });
                    }
                    Err(map_symbols(&self.symbols, &self.errors))
                }
            }
        }
    }

    fn typecheck(&mut self, expr: &mut ast::LExpr<TcIdent>) -> TcResult {
        self.refresh_symbols(expr);
        match self.typecheck_(expr) {
            Ok(typ) => Ok(typ),
            Err(err) => {
                self.errors.error(ast::Spanned {
                    span: expr.span(&ast::TcIdentEnvWrapper(&self.symbols)),
                    value: err,
                });
                Ok(self.inst.subs.new_var())
            }
        }
    }
    fn typecheck_(&mut self, expr: &mut ast::LExpr<TcIdent>) -> TcResult {
        match expr.value {
            ast::Expr::Identifier(ref mut id) => {
                id.typ = try!(self.find(id.id()));
                Ok(id.typ.clone())
            }
            ast::Expr::Literal(ref lit) => {
                Ok(match *lit {
                    ast::LiteralEnum::Integer(_) => Type::int(),
                    ast::LiteralEnum::Float(_) => Type::float(),
                    ast::LiteralEnum::String(_) => Type::string(),
                    ast::LiteralEnum::Char(_) => Type::char(),
                    ast::LiteralEnum::Bool(_) => Type::bool(),
                })
            }
            ast::Expr::Call(ref mut func, ref mut args) => {
                let mut func_type = try!(self.typecheck(&mut **func));
                for arg in args.iter_mut() {
                    let f = Type::function(vec![self.inst.subs.new_var()],
                                           self.inst.subs.new_var());
                    func_type = try!(self.unify(&f, func_type));
                    func_type = match *func_type {
                        Type::Function(ref arg_type, ref ret) => {
                            assert!(arg_type.len() == 1);
                            let actual = try!(self.typecheck(arg));
                            try!(self.unify(&arg_type[0], actual));
                            ret.clone()
                        }
                        _ => return Err(NotAFunction(func_type.clone())),
                    };
                }
                Ok(func_type)
            }
            ast::Expr::IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
                let pred_type = try!(self.typecheck(&mut **pred));
                try!(self.unify(&Type::bool(), pred_type));
                let true_type = try!(self.typecheck(&mut **if_true));
                let false_type = match *if_false {
                    Some(ref mut if_false) => try!(self.typecheck(&mut **if_false)),
                    None => Type::unit(),
                };
                self.unify(&true_type, false_type)
            }
            ast::Expr::BinOp(ref mut lhs, ref mut op, ref mut rhs) => {
                let lhs_type = try!(self.typecheck(&mut **lhs));
                let rhs_type = try!(self.typecheck(&mut **rhs));
                let op_name = String::from(self.symbols.string(&op.name));
                if op_name.starts_with("#") {
                    let arg_type = try!(self.unify(&lhs_type, rhs_type));
                    let offset;
                    let typ = if op_name[1..].starts_with("Int") {
                        offset = "Int".len();
                        op.typ = Type::function(vec![Type::int(), Type::int()], Type::int());
                        try!(self.unify(&Type::int(), arg_type))
                    } else if op_name[1..].starts_with("Float") {
                        offset = "Float".len();
                        op.typ = Type::function(vec![Type::float(), Type::float()], Type::float());
                        try!(self.unify(&Type::float(), arg_type))
                    } else {
                        panic!("ICE: Unknown primitive type")
                    };
                    match &op_name[1 + offset..] {
                        "+" | "-" | "*" => Ok(typ),
                        "==" | "<" => Ok(Type::bool().clone()),
                        _ => Err(UndefinedVariable(op.name.clone())),
                    }
                } else {
                    match &*op_name {
                        "&&" | "||" => {
                            try!(self.unify(&lhs_type, rhs_type.clone()));
                            op.typ = Type::function(vec![Type::bool(), Type::bool()], Type::bool());
                            self.unify(&Type::bool(), lhs_type)
                        }
                        _ => {
                            op.typ = try!(self.find(op.id()));
                            let func_type = Type::function(vec![lhs_type, rhs_type],
                                                           self.inst.subs.new_var());
                            match *try!(self.unify(&op.typ, func_type)) {
                                Type::Function(_, ref return_type) => {
                                    match **return_type {
                                        Type::Function(_, ref return_type) => {
                                            Ok(return_type.clone())
                                        }
                                        _ => panic!("ICE: unify binop"),
                                    }
                                }
                                _ => panic!("ICE: unify binop"),
                            }
                        }
                    }
                }
            }
            ast::Expr::Tuple(ref mut exprs) => {
                assert!(exprs.len() == 0);
                Ok(Type::unit())
            }
            ast::Expr::Match(ref mut expr, ref mut alts) => {
                let typ = try!(self.typecheck(&mut **expr));
                let mut expected_alt_type = None;

                for alt in alts.iter_mut() {
                    self.enter_scope();
                    try!(self.typecheck_pattern(&mut alt.pattern, typ.clone()));
                    let mut alt_type = try!(self.typecheck(&mut alt.expression));
                    self.exit_scope();
                    if let Some(ref expected) = expected_alt_type {
                        alt_type = try!(self.unify(expected, alt_type));
                    }
                    expected_alt_type = Some(alt_type);
                }
                expected_alt_type.ok_or(StringError("No alternative in case expression"))
            }
            ast::Expr::Let(ref mut bindings, ref mut body) => {
                self.enter_scope();
                let level = self.inst.subs.var_id();
                let is_recursive = bindings.iter().all(|bind| bind.arguments.len() > 0);
                if is_recursive {
                    for bind in bindings.iter_mut() {
                        let mut typ = self.inst.subs.new_var();
                        if let Some(ref mut type_decl) = bind.typ {
                            try!(self.kindcheck(type_decl, &mut []));
                            let decl = self.inst.instantiate(type_decl);
                            typ = try!(self.unify(&decl, typ));
                        }
                        try!(self.typecheck_pattern(&mut bind.name, typ));
                        if let ast::Expr::Lambda(ref mut lambda) = bind.expression.value {
                            if let ast::Pattern::Identifier(ref name) = bind.name.value {
                                lambda.id.name = name.name;
                            }
                        }
                    }
                }
                let mut types = Vec::new();
                for bind in bindings.iter_mut() {
                    // Functions which are declared as `let f x = ...` are allowed to be self
                    // recursive
                    let mut typ = if bind.arguments.len() != 0 {
                        let function_type = match bind.typ {
                            Some(ref typ) => typ.clone(),
                            None => self.inst.subs.new_var(),
                        };
                        try!(self.typecheck_lambda(function_type,
                                                   &mut bind.arguments,
                                                   &mut bind.expression))
                    } else {
                        if let Some(ref mut type_decl) = bind.typ {
                            try!(self.kindcheck(type_decl, &mut []));
                        }
                        try!(self.typecheck(&mut bind.expression))
                    };
                    debug!("let {:?} : {}",
                           bind.name,
                           ast::display_type(&self.symbols, &typ));
                    if let Some(ref type_decl) = bind.typ {
                        typ = try!(self.unify(type_decl, typ));
                    }
                    if !is_recursive {
                        // Merge the type declaration and the actual type
                        self.generalize_variables(level, &mut bind.expression);
                        try!(self.typecheck_pattern(&mut bind.name, typ));
                    } else {
                        types.push(typ);
                    }
                }
                if is_recursive {
                    for (typ, bind) in types.into_iter().zip(bindings.iter_mut()) {
                        // Merge the variable we bound to the name and the type inferred
                        // in the expression
                        try!(self.unify(&bind.type_of().clone(), typ));
                    }
                }
                // Once all variables inside the let has been unified we can quantify them
                debug!("Generalize {}", level);
                for bind in bindings {
                    self.generalize_variables(level, &mut bind.expression);
                    self.finish_binding(level, bind);
                }
                debug!("Typecheck `in`");
                let result = self.typecheck(body);
                self.exit_scope();
                result
            }
            ast::Expr::FieldAccess(ref mut expr, ref mut field_access) => {
                let mut typ = try!(self.typecheck(&mut **expr));
                debug!("FieldAccess {} . {:?}",
                       ast::display_type(&self.symbols, &typ),
                       self.symbols.string(&field_access.name));
                self.inst.subs.make_real(&mut typ);
                if let Type::Variable(_) = *typ {
                    let (record_type, _) = try!(self.find_record(&[field_access.name])
                                                    .map(|t| (t.0.clone(), t.1.clone())));
                    let record_type = self.inst.instantiate(&record_type);
                    typ = try!(self.unify(&record_type, typ));
                }
                let record = self.remove_aliases(typ.clone());
                match *record {
                    Type::Record { ref fields, .. } => {
                        let field_type = fields.iter()
                                               .find(|field| field.name == *field_access.id())
                                               .map(|field| field.typ.clone());
                        field_access.typ = match field_type {
                            Some(typ) => self.inst.instantiate(&typ),
                            None => {
                                return Err(UndefinedField(typ.clone(), field_access.name.clone()))
                            }
                        };
                        Ok(field_access.typ.clone())
                    }
                    _ => Err(InvalidFieldAccess(record.clone())),
                }
            }
            ast::Expr::Array(ref mut a) => {
                let mut expected_type = self.inst.subs.new_var();
                for expr in a.expressions.iter_mut() {
                    let typ = try!(self.typecheck(expr));
                    expected_type = try!(self.unify(&expected_type, typ));
                }
                a.id.typ = Type::array(expected_type);
                Ok(a.id.typ.clone())
            }
            ast::Expr::Lambda(ref mut lambda) => {
                let loc = format!("lambda:{}", expr.location);
                lambda.id.name = self.symbols.symbol(loc);
                let function_type = self.inst.subs.new_var();
                let typ = try!(self.typecheck_lambda(function_type,
                                                     &mut lambda.arguments,
                                                     &mut lambda.body));
                lambda.id.typ = typ.clone();
                Ok(typ)
            }
            ast::Expr::Type(ref mut bindings, ref mut expr) => {
                // enter_scope is called in refresh_symbols
                {
                    let subs = Substitution::new();
                    let mut check = super::kindcheck::KindCheck::new(&self.environment,
                                                                     &self.symbols,
                                                                     subs);
                    // Setup kind variables for all type variables and insert the types in the
                    // this type expression into the kindcheck environment
                    for &mut ast::TypeBinding { ref mut name, .. } in bindings.iter_mut() {
                        *name = match (**name).clone() {
                            Type::Data(ast::TypeConstructor::Data(id), mut args) => {
                                // Create the kind for this binding
                                // Test a b: 2 -> 1 -> *
                                // and bind the same variables to the arguments of the type binding
                                // ('a' and 'b' in the example)
                                let mut id_kind = check.star();
                                for arg in args.iter_mut().rev() {
                                    let mut a = (**arg).clone();
                                    if let Type::Generic(ref mut gen) = a {
                                        gen.kind = check.subs.new_var();
                                        id_kind = Kind::function(gen.kind.clone(), id_kind);
                                    }
                                    *arg = TcType::from(a);
                                }
                                check.add_local(id, id_kind);
                                Type::data(ast::TypeConstructor::Data(id), args)
                            }
                            _ => {
                                panic!("ICE: Unexpected lhs of type binding {}",
                                       ast::display_type(&self.symbols, name))
                            }
                        };
                    }

                    // Kindcheck all the types in the environment
                    for &mut ast::TypeBinding { ref mut name, ref mut typ } in bindings.iter_mut() {
                        match **name {
                            Type::Data(_, ref args) => {
                                check.set_variables(args);
                            }
                            _ => {
                                panic!("ICE: Unexpected lhs of type binding {}",
                                       ast::display_type(&self.symbols, name))
                            }
                        }
                        try!(check.kindcheck_type(typ));
                        try!(check.kindcheck_type(name));
                    }

                    // All kinds are now inferred so replace the kinds store in the AST
                    for &mut ast::TypeBinding { ref mut name, ref mut typ } in bindings.iter_mut() {
                        *typ = check.finalize_type(typ.clone());
                        *name = check.finalize_type(name.clone());
                    }
                }

                // Finally insert the declared types into the global scope
                for &mut ast::TypeBinding { ref name, ref typ } in bindings {
                    match **name {
                        Type::Data(ast::TypeConstructor::Data(id), ref args) => {
                            debug!("HELP {} \n{:?}", self.symbols.string(&id), args);
                            if self.environment.stack_types.get(&id).is_some() {
                                self.errors.error(ast::Spanned {
                                    span: expr.span(&ast::TcIdentEnvWrapper(&self.symbols)),
                                    value: DuplicateTypeDefinition(id),
                                });
                            } else {
                                let generic_args = extract_generics(args);
                                self.stack_type(id, name.clone(), generic_args, typ.clone());
                            }
                        }
                        _ => {
                            panic!("ICE: Unexpected lhs of type binding {}",
                                   ast::display_type(&self.symbols, name))
                        }
                    }
                }
                let expr_type = try!(self.typecheck(&mut **expr));
                self.exit_scope();
                Ok(expr_type)
            }
            ast::Expr::Record { typ: ref mut id, ref mut types, exprs: ref mut fields } => {
                let types = try!(types.iter_mut()
                                      .map(|tup| {
                                          let (generics, typ) = {
                                              let (generics, typ) =
                                                  try!(self.find_type_info(&tup.0));
                                              let generics: Vec<_> = generics.iter()
                                                                             .cloned()
                                                                             .collect();
                                              (generics, typ.cloned())
                                          };

                                          let name = Type::data(ast::TypeConstructor::Data(tup.0),
                                                                generics.iter()
                                                                        .cloned()
                                                                        .map(Type::generic)
                                                                        .collect());
                                          let typ = match typ {
                                              Some(typ) => typ.clone(),
                                              None => name.clone(),
                                          };
                                          let n = String::from(Name::new(self.symbols
                                                                             .string(&tup.0))
                                                                   .name()
                                                                   .as_str());
                                          Ok(ast::Field {
                                              name: self.symbols.symbol(n),
                                              typ: ast::Alias {
                                                  name: tup.0,
                                                  args: generics,
                                                  typ: typ,
                                              },
                                          })
                                      })
                                      .collect::<TcResult<Vec<_>>>());
                let fields = try!(fields.iter_mut()
                                        .map(|field| {
                                            match field.1 {
                                                Some(ref mut expr) => self.typecheck(expr),
                                                None => self.find(&field.0),
                                            }
                                            .map(|typ| {
                                                ast::Field {
                                                    name: field.0,
                                                    typ: typ,
                                                }
                                            })
                                        })
                                        .collect::<TcResult<Vec<_>>>());
                let (id_type, record_type) = match self.find_record(&fields.iter()
                                                                           .map(|f| f.name)
                                                                           .collect::<Vec<_>>())
                                                       .map(|t| (t.0.clone(), t.1.clone())) {
                    Ok(x) => x,
                    Err(_) => {
                        id.typ = Type::record(types.clone(), fields);
                        return Ok(id.typ.clone());
                    }
                };
                let id_type = self.inst.instantiate(&id_type);
                let record_type = self.inst.instantiate_(&record_type);
                try!(self.unify(&Type::record(types, fields), record_type));
                id.typ = id_type.clone();
                Ok(id_type.clone())
            }
        }
    }

    fn typecheck_lambda(&mut self,
                        function_type: TcType,
                        arguments: &mut [TcIdent],
                        body: &mut ast::LExpr<TcIdent>)
                        -> TcResult {
        self.enter_scope();
        let mut arg_types = Vec::new();
        {
            let mut iter1 = function_arg_iter(self, function_type);
            let mut iter2 = arguments.iter_mut();
            while let (Some(arg_type), Some(arg)) = (iter1.next(), iter2.next()) {
                arg.typ = arg_type;
                arg_types.push(arg.typ.clone());
                iter1.tc.stack_var(arg.name.clone(), arg.typ.clone());
            }
        }
        let body_type = try!(self.typecheck(body));
        self.exit_scope();
        Ok(Type::function(arg_types, body_type))
    }

    fn typecheck_pattern(&mut self,
                         pattern: &mut ast::LPattern<TcIdent>,
                         match_type: TcType)
                         -> TcResult {
        match pattern.value {
            ast::Pattern::Constructor(ref id, ref mut args) => {
                // Find the enum constructor and return the types for its arguments
                let ctor_type = try!(self.find(&id.name));
                let return_type = try!(self.typecheck_pattern_rec(args, ctor_type));
                self.unify(&match_type, return_type)
            }
            ast::Pattern::Record { ref mut id, types: ref mut associated_types, ref fields } => {
                id.typ = match_type.clone();
                let mut match_type = self.remove_alias(match_type);
                let mut types = Vec::new();
                let new_type = match *match_type {
                    Type::Record { fields: ref expected_fields, .. } => {
                        for pattern_field in fields {
                            let expected_field = try!(expected_fields.iter()
                                .find(|expected_field| pattern_field.0 == expected_field.name)
                                .ok_or(UndefinedField(match_type.clone(), pattern_field.0)));
                            let var = self.inst.subs.new_var();
                            types.push(var.clone());
                            try!(self.unify(&var, expected_field.typ.clone()));
                        }
                        None
                    }
                    _ => {
                        let fields: Vec<_> = fields.iter().map(|t| t.0).collect();
                        // actual_type is the record (not hidden behind an alias)
                        let (mut typ, mut actual_type) = match self.find_record(&fields)
                                                                   .map(|t| {
                                                                       (t.0.clone(), t.1.clone())
                                                                   }) {
                            Ok(typ) => typ,
                            Err(_) => {
                                let fields = fields.iter()
                                                   .map(|field| {
                                                       ast::Field {
                                                           name: *field,
                                                           typ: self.inst.subs.new_var(),
                                                       }
                                                   })
                                                   .collect();
                                let t = Type::record(Vec::new(), fields);
                                (t.clone(), t)
                            }
                        };
                        typ = self.inst.instantiate_(&typ);
                        actual_type = self.inst.instantiate_(&actual_type);
                        try!(self.unify(&match_type, typ));
                        match *actual_type {
                            Type::Record { fields: ref record_types, .. } => {
                                types.extend(record_types.iter().map(|f| f.typ.clone()));
                            }
                            _ => {
                                panic!("Expected record found {}",
                                       ast::display_type(&self.symbols, &match_type))
                            }
                        }
                        Some(actual_type)
                    }
                };
                match_type = new_type.unwrap_or(match_type);
                for (field, field_type) in fields.iter().zip(types) {
                    let (mut name, ref bind) = *field;
                    if let Some(bind_name) = *bind {
                        name = bind_name;
                    }
                    self.stack_var(name, field_type);
                }
                match *match_type {
                    Type::Record { ref types, .. } => {
                        for field in associated_types.iter_mut() {
                            let (mut name, ref bind) = *field;
                            if let Some(bind_name) = *bind {
                                name = bind_name;
                            }
                            // The `types` in the record type should have a type matching the
                            // `name`
                            let field_type = types.iter()
                                                  .find(|field| field.name == name);
                            match field_type {
                                Some(field_type) => {
                                    let args = field_type.typ
                                                         .args
                                                         .iter()
                                                         .cloned()
                                                         .map(Type::generic)
                                                         .collect();
                                    let alias_type = ast::Type::data(
                                        ast::TypeConstructor::Data(field_type.typ.name.clone()),
                                        args
                                    );
                                    // This forces refresh_type to remap the name a type was given
                                    // in this module to its actual name
                                    self.original_symbols
                                        .insert(field_type.name, field_type.typ.name);
                                    self.stack_type(name,
                                                    alias_type,
                                                    field_type.typ.args.clone(),
                                                    field_type.typ.typ.clone());
                                }
                                None => return Err(UndefinedField(match_type.clone(), name)),
                            }
                        }
                    }
                    _ => panic!("Expected a record"),
                }
                Ok(match_type)
            }
            ast::Pattern::Identifier(ref mut id) => {
                self.stack_var(id.id().clone(), match_type.clone());
                id.typ = match_type.clone();
                Ok(match_type)
            }
        }
    }

    fn typecheck_pattern_rec(&mut self, args: &[TcIdent], typ: TcType) -> TcResult {
        if args.len() == 0 {
            return Ok(typ);
        }
        match *typ {
            Type::Function(ref argument_types, ref return_type) => {
                assert!(argument_types.len() == 1);
                self.stack_var(args[0].id().clone(), argument_types.last().unwrap().clone());
                self.typecheck_pattern_rec(&args[1..], return_type.clone())
            }
            _ => Err(PatternError(typ.clone(), args.len())),
        }
    }

    fn kindcheck(&self, typ: &mut TcType, args: &mut [TcType]) -> Result<(), TypeError<Symbol>> {
        let subs = Substitution::new();
        let mut check = super::kindcheck::KindCheck::new(&self.environment, &self.symbols, subs);
        check.set_variables(args);
        try!(check.kindcheck_type(typ));
        Ok(())
    }

    fn finish_binding(&mut self, level: u32, bind: &mut ast::Binding<TcIdent>) {
        match bind.name.value {
            ast::Pattern::Identifier(ref mut id) => {
                id.typ = self.finish_type(level, id.typ.clone());
                debug!("{}: {}",
                       self.symbols.string(&id.name),
                       ast::display_type(&self.symbols, &id.typ));
                self.intersect_type(level, id.name, &id.typ);
            }
            ast::Pattern::Record { ref id, ref mut fields, .. } => {
                debug!("{{ .. }}: {}",
                       ast::display_type(&self.symbols,
                                         &bind.expression
                                              .env_type_of(&self.environment)));
                let record_type = self.remove_alias(id.typ.clone());
                with_pattern_types(fields, &record_type, |field_name, field_type| {
                    self.intersect_type(level, field_name, field_type);
                });
            }
            ast::Pattern::Constructor(ref id, ref arguments) => {
                debug!("{}: {}",
                       self.symbols.string(&id.name),
                       ast::display_type(&self.symbols,
                                         &bind.expression
                                              .env_type_of(&self.environment)));
                for arg in arguments {
                    self.intersect_type(level, arg.name, &arg.typ);
                }
            }
        }
    }

    fn intersect_type(&mut self, level: u32, symbol: Symbol, symbol_type: &TcType) {
        let mut typ = None;
        if let Some(existing_types) = self.environment.stack.get_all(&symbol) {
            if existing_types.len() >= 2 {
                let existing_type = &existing_types[existing_types.len() - 2];
                let mut alias = AliasInstantiator::new(&self.inst, &self.environment);
                debug!("Intersect\n{} <> {}", ast::display_type(&self.symbols, existing_type),
                                              ast::display_type(&self.symbols, symbol_type));
                typ = Some(unify::intersection(&self.inst.subs, &mut alias, existing_type, symbol_type));
            }
        }
        if let Some(typ) = typ {
            *self.environment.stack.get_mut(&symbol).unwrap() = self.finish_type(level, typ);
        }
    }

    fn finish_type(&mut self, level: u32, typ: TcType) -> TcType {
        let generic = {
            let vars = self.inst.named_variables.borrow();
            let max_var = vars.keys()
                              .fold("a", |max, current| {
                                  ::std::cmp::max(max, self.symbols.string(&current))
                              });
            String::from(max_var)
        };
        let mut i = 0;
        ast::walk_move_type(typ,
                            &mut |typ| {
                                let replacement = self.inst.replace_variable(typ);
                                let mut typ = typ;
                                if let Some(ref t) = replacement {
                                    debug!("{} ==> {}",
                                           ast::display_type(&self.symbols, &typ),
                                           ast::display_type(&self.symbols, t));
                                    typ = &**t;
                                }
                                match *typ {
                                    Type::Variable(ref var) if self.inst.subs.get_level(var.id) >
                                                               level => {
                                        let generic = format!("{}{}", generic, i);
                                        i += 1;
                                        let id = self.symbols.symbol(generic);
                                        let gen = Type::generic(ast::Generic {
                                            kind: var.kind.clone(),
                                            id: id,
                                        });
                                        self.inst.subs.insert(var.id, gen.clone());
                                        self.inst
                                            .named_variables
                                            .borrow_mut()
                                            .insert(id, gen.clone());
                                        Some(gen)
                                    }
                                    _ => unroll_app(typ).or(replacement.clone()),
                                }
                            })
    }

    fn refresh_symbols(&mut self, expr: &mut ast::LExpr<TcIdent>) {
        match expr.value {
            ast::Expr::Identifier(ref mut id) => {
                if let Some(&new) = self.original_symbols.get(&id.name) {
                    id.name = new;
                }
            }
            ast::Expr::Let(ref mut bindings, _) => {
                for bind in bindings {
                    if let Some(ref mut type_decl) = bind.typ {
                        *type_decl = self.refresh_symbols_in_type(type_decl.clone());
                    }
                }
            }
            ast::Expr::Type(ref mut bindings, _) => {
                self.enter_scope();
                for &mut ast::TypeBinding { ref mut name, .. } in bindings.iter_mut() {
                    *name = match (**name).clone() {
                        Type::Data(ast::TypeConstructor::Data(original), args) => {
                            // Create a new symbol for this binding so that this type will
                            // differ from any other types which are named the same
                            let s = String::from(self.symbols.string(&original));
                            let new = self.symbols.scoped_symbol(&s);
                            self.original_symbols.insert(original, new);
                            Type::data(ast::TypeConstructor::Data(new), args)
                        }
                        _ => {
                            panic!("ICE: Unexpected lhs of type binding {}",
                                   ast::display_type(&self.symbols, name))
                        }
                    };
                }
                for &mut ast::TypeBinding { ref mut typ, .. } in bindings.iter_mut() {
                    *typ = self.refresh_symbols_in_type(typ.clone());
                }
            }
            ast::Expr::Record { ref mut types, .. } => {
                for &mut (ref mut symbol, ref mut typ) in types {
                    if let Some(&new) = self.original_symbols.get(symbol) {
                        *symbol = new;
                    }
                    if let Some(ref mut typ) = *typ {
                        *typ = self.refresh_symbols_in_type(typ.clone());
                    }
                }
            }
            _ => (),
        }
    }

    fn refresh_symbols_in_type(&mut self, typ: TcType) -> TcType {
        ast::walk_move_type(typ,
                            &mut |typ| {
                                match *typ {
                                    Type::Data(ast::TypeConstructor::Data(id), ref args) => {
                                        self.original_symbols
                                            .get(&id)
                                            .map(|current| {
                                                Type::data(ast::TypeConstructor::Data(*current),
                                                           args.clone())
                                            })
                                    }
                                    Type::Variants(ref variants) => {
                                        let iter = || {
                                            variants.iter()
                                                    .map(|var| self.original_symbols.get(&var.0))
                                        };
                                        if iter().any(|opt| opt.is_some()) {
                                            // If any of the variants requires a symbol replacement
                                            // we create a new type
                                            Some(Type::variants(iter()
                                                                    .zip(variants.iter())
                                                                    .map(|(new, old)| {
                                                                        match new {
                                                                            Some(&new) => {
                                                                                (new, old.1.clone())
                                                                            }
                                                                            None => old.clone(),
                                                                        }
                                                                    })
                                                                    .collect()))
                                        } else {
                                            None
                                        }
                                    }
                                    _ => None,
                                }
                            })
    }

    fn unify(&self, expected: &TcType, mut actual: TcType) -> TcResult {
        debug!("Unify {} <=> {}",
               ast::display_type(&self.symbols, expected),
               ast::display_type(&self.symbols, &actual));
        let mut alias = AliasInstantiator::new(&self.inst, &self.environment);
        match unify::unify(&self.inst.subs, &mut alias, expected, &actual) {
            Ok(typ) => Ok(self.inst.set_type(typ)),
            Err(errors) => {
                let mut expected = expected.clone();
                expected = self.inst.set_type(expected);
                actual = self.inst.set_type(actual);
                debug!("Error '{:?}' between:\n>> {}\n>> {}",
                       errors,
                       ast::display_type(&self.symbols, &expected),
                       ast::display_type(&self.symbols, &actual));
                Err(TypeError::Unification(expected, actual, apply_subs(&self.inst, errors)))
            }
        }
    }

    fn remove_alias(&self, typ: TcType) -> TcType {
        AliasInstantiator::new(&self.inst, &self.environment).remove_alias(typ)
    }

    fn remove_aliases(&self, typ: TcType) -> TcType {
        AliasInstantiator::new(&self.inst, &self.environment).remove_aliases(typ)
    }

    fn type_of_alias(&self,
                     id: Symbol,
                     arguments: &[TcType])
                     -> Result<Option<TcType>, ::unify_type::Error<Symbol>> {
        AliasInstantiator::new(&self.inst, &self.environment).type_of_alias(id, arguments)
    }
}

fn with_pattern_types<F>(fields: &[(Symbol, Option<Symbol>)], typ: &TcType, mut f: F)
    where F: FnMut(Symbol, &TcType)
{
    if let Type::Record { fields: ref field_types, .. } = **typ {
        for field in fields {
            let associated_type = field_types.iter()
                                             .find(|type_field| type_field.name == field.0)
                                             .expect("Associated type to exist in record");
            f(field.0, &associated_type.typ);
        }
    }
}

fn apply_subs(inst: &Instantiator,
              error: Vec<::unify_type::Error<Symbol>>)
              -> Vec<::unify_type::Error<Symbol>> {
    use unify::Error::*;
    error.into_iter()
         .map(|error| {
             match error {
                 TypeMismatch(expected, actual) => {
                     TypeMismatch(inst.set_type(expected), inst.set_type(actual))
                 }
                 Occurs(var, typ) => Occurs(var, inst.set_type(typ)),
                 Other(::unify_type::TypeError::UndefinedType(id)) => {
                     Other(::unify_type::TypeError::UndefinedType(id))
                 }
                 Other(::unify_type::TypeError::FieldMismatch(expected, actual)) => {
                     UnifyError::Other(::unify_type::TypeError::FieldMismatch(expected, actual))
                 }
             }
         })
         .collect()
}


pub fn extract_generics(args: &[TcType]) -> Vec<ast::Generic<Symbol>> {
    args.iter()
        .map(|arg| {
            match **arg {
                Type::Generic(ref gen) => gen.clone(),
                _ => {
                    panic!("The type on the lhs of a type binding did not have all generic \
                            arguments")
                }
            }
        })
        .collect()
}

pub fn unroll_app(typ: &Type<Symbol>) -> Option<TcType> {
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

struct FunctionArgIter<'a, 'b: 'a> {
    tc: &'a mut Typecheck<'b>,
    typ: TcType,
}

impl<'a, 'b> Iterator for FunctionArgIter<'a, 'b> {
    type Item = TcType;
    fn next(&mut self) -> Option<TcType> {
        loop {
            let (arg, new) = match *self.typ {
                Type::Function(ref args, ref ret) => (Some(args[0].clone()), ret.clone()),
                Type::Data(ast::TypeConstructor::Data(id), ref args) => {
                    match self.tc.type_of_alias(id, args) {
                        Ok(Some(typ)) => (None, typ.clone()),
                        Ok(None) => return None,
                        Err(_) => return Some(self.tc.inst.subs.new_var()),
                    }
                }
                _ => return Some(self.tc.inst.subs.new_var()),
            };
            self.typ = new;
            if let Some(arg) = arg {
                return Some(arg);
            }
        }
    }
}

fn function_arg_iter<'a, 'b>(tc: &'a mut Typecheck<'b>, typ: TcType) -> FunctionArgIter<'a, 'b> {
    FunctionArgIter { tc: tc, typ: typ }
}


pub fn walk_real_type<F>(subs: &Substitution<TcType>, typ: &TcType, f: &mut F)
    where F: FnMut(&Type<Symbol>)
{
    let typ = subs.real(typ);
    f(typ);
    match **typ {
        Type::Data(_, ref args) => {
            for a in args {
                walk_real_type(subs, a, f);
            }
        }
        Type::Array(ref inner) => {
            walk_real_type(subs, inner, f);
        }
        Type::Function(ref args, ref ret) => {
            for a in args {
                walk_real_type(subs, a, f);
            }
            walk_real_type(subs, ret, f);
        }
        Type::Record { ref types, ref fields } => {
            for field in types {
                walk_real_type(subs, &field.typ.typ, f);
            }
            for field in fields {
                walk_real_type(subs, &field.typ, f);
            }
        }
        Type::App(ref l, ref r) => {
            walk_real_type(subs, l, f);
            walk_real_type(subs, r, f);
        }
        Type::Variants(ref variants) => {
            for variant in variants {
                walk_real_type(subs, &variant.1, f);
            }
        }
        Type::Builtin(_) | Type::Variable(_) | Type::Generic(_) => (),
    }
}
