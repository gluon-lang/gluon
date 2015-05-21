use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::convert::AsRef;
use std::fmt;
use scoped_map::ScopedMap;
use base::ast;
use base::ast::MutVisitor;
use base::interner::InternedStr;

use self::TypeError::*;

pub use base::ast::{TcIdent, TcType, Type};


pub static INT_TYPE: TcType = Type::Builtin(ast::IntType);
pub static FLOAT_TYPE: TcType = Type::Builtin(ast::FloatType);
pub static STRING_TYPE: TcType = Type::Builtin(ast::StringType);
pub static BOOL_TYPE: TcType = Type::Builtin(ast::BoolType);
pub static UNIT_TYPE: TcType = Type::Builtin(ast::UnitType);

pub fn match_types(l: &TcType, r: &TcType) -> bool {
    fn type_eq<'a>(vars: &mut HashMap<TcType, &'a TcType>, l: &'a TcType, r: &'a TcType) -> bool {
        match (l, r) {
            (&Type::Variable(_), _) => var_eq(vars, l.clone(), r),
            (&Type::Generic(_), _) => var_eq(vars, l.clone(), r),
            (&Type::Function(ref l_args, ref l_ret), &Type::Function(ref r_args, ref r_ret)) => {
                if l_args.len() == r_args.len() {
                    l_args.iter()
                        .zip(r_args.iter())
                        .all(|(l, r)| type_eq(vars, l, r))
                        && type_eq(vars, &**l_ret, &**r_ret)
                }
                else {
                    false
                }
            }
            (&Type::Array(ref l), &Type::Array(ref r)) => type_eq(vars, &**l, &**r),
            (&Type::Data(ref l, ref l_args), &Type::Data(ref r, ref r_args)) => {
                l == r
                && l_args.len() == r_args.len()
                && l_args.iter().zip(r_args.iter()).all(|(l, r)| type_eq(vars, l, r))
            }
            (&Type::Trait(ref l, ref l_args), &Type::Trait(ref r, ref r_args)) => {
                l == r
                && l_args.len() == r_args.len()
                && l_args.iter().zip(r_args.iter()).all(|(l, r)| type_eq(vars, l, r))
            }
            (&Type::Builtin(ref l), &Type::Builtin(ref r)) => l == r,
            _ => false
        }
    }

    fn var_eq<'a>(mapping: &mut HashMap<TcType, &'a TcType>, l: TcType, r: &'a TcType) -> bool {
        match mapping.get(&l) {
            Some(x) => return *x == r,
            None => ()
        }
        mapping.insert(l, r);
        true
    }

    let mut vars = HashMap::new();
    type_eq(&mut vars, l, r)
}


fn add_impl_constraints(constraints: &[ast::Constraint], decl: &mut ast::GlobalDeclaration<TcIdent>) {
    //Add all constraints from the impl declaration to the globals declaration
    for constraint in constraints.iter() {
        let exists = {
            decl.typ.constraints.iter()
                .find(|func_constraint| *func_constraint == constraint)
                .is_some()
        };
        if !exists {
            decl.typ.constraints.push(constraint.clone());
        }
    }
}

#[derive(Debug, PartialEq)]
enum TypeError {
    UndefinedVariable(InternedStr),
    NotAFunction(TcType),
    WrongNumberOfArguments(usize, usize),
    TypeMismatch(TcType, TcType),
    UnboundVariable,
    UndefinedStruct(InternedStr),
    UndefinedField(InternedStr, InternedStr),
    UndefinedTrait(InternedStr),
    IndexError(TcType),
    StringError(&'static str)
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", *self)
    }
}

pub type TcResult = Result<TcType, TypeError>;

pub struct TypeInfos {
    pub datas: HashMap<InternedStr, Vec<ast::Constructor<TcIdent>>>,
    pub impls: HashMap<InternedStr, Vec<ast::Constrained<TcType>>>,
    pub traits: HashMap<InternedStr, Vec<(InternedStr, ast::Constrained<TcType>)>>
}

impl TypeInfos {
    pub fn new() -> TypeInfos {
        TypeInfos {
            datas: HashMap::new(),
            traits: HashMap::new(),
            impls: HashMap::new()
        }
    }
    pub fn find_type_info(&self, id: &InternedStr) -> Option<&[ast::Constructor<TcIdent>]> {
        self.datas.get(id)
            .map(|vec| &**vec)
    }
    pub fn find_trait(&self, name: &InternedStr) -> Option<&[(InternedStr, ast::Constrained<TcType>)]> {
        self.traits.get(name).map(|v| &v[..])
    }
    pub fn add_module(&mut self, module: &ast::Module<TcIdent>) {
        for data in module.datas.iter() {
            self.datas.insert(data.name, data.constructors.clone());
        }
        for t in module.traits.iter() {
            let function_types = t.declarations.iter().map(|decl| {
                (decl.name.clone(), decl.typ.clone())
            }).collect();
            self.traits.insert(t.name, function_types);
        }
        for imp in module.impls.iter() {
            let set = match self.impls.entry(imp.trait_name) {
                Entry::Occupied(v) => v.into_mut(),
                Entry::Vacant(v) => v.insert(Vec::new())
            };
            set.push(ast::Constrained { constraints: imp.constraints.clone(), value: imp.typ.clone() });
        }
    }
    pub fn extend(&mut self, other: TypeInfos) {
        let TypeInfos { datas, impls, traits } = other;
        self.datas.extend(datas);
        self.impls.extend(impls);
        self.traits.extend(traits);
    }
}
fn find_trait<'a>(this: &'a TypeInfos, name: &InternedStr) -> Result<&'a [(InternedStr, ast::Constrained<TcType>)], TypeError> {
    this.find_trait(name)
        .map(Ok)
        .unwrap_or_else(|| Err(UndefinedTrait(name.clone())))
}

pub trait TypeEnv {
    fn find_type(&self, id: &InternedStr) -> Option<(&[ast::Constraint], &TcType)>;
    fn find_type_info(&self, id: &InternedStr) -> Option<&[ast::Constructor<TcIdent>]>;
}

pub struct Typecheck<'a> {
    environment: Option<&'a (TypeEnv + 'a)>,
    pub type_infos: TypeInfos,
    module: HashMap<InternedStr, ast::Constrained<TcType>>,
    stack: ScopedMap<InternedStr, TcType>,
    subs: Substitution,
    errors: Errors<ast::Located<TypeError>>
}

#[derive(Debug, PartialEq)]
struct Errors<T> {
    errors: Vec<T>
}

impl <T> Errors<T> {
    fn new() -> Errors<T> {
        Errors { errors: Vec::new() }
    }
    fn has_errors(&self) -> bool {
        self.errors.len() != 0
    }
    fn error(&mut self, t: T) {
        self.errors.push(t);
    }
    fn handle<U>(&mut self, err: Result<U, T>) {
        match err {
            Ok(_) => (),
            Err(e) => self.error(e)
        }
    }
}

impl <T: fmt::Display> fmt::Display for Errors<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for error in self.errors.iter() {
            try!(write!(f, "{}\n", error));
        }
        Ok(())
    }
}

pub type StringErrors = Errors<ast::Located<TypeError>>;

impl <'a> Typecheck<'a> {
    
    pub fn new() -> Typecheck<'a> {
        Typecheck {
            environment: None,
            module: HashMap::new(),
            type_infos: TypeInfos::new(),
            stack: ScopedMap::new(),
            subs: Substitution::new(),
            errors: Errors::new()
        }
    }

    fn find(&mut self, id: &InternedStr) -> TcResult {
        let t: Option<(&[ast::Constraint], &TcType)> = {
            let stack = &self.stack;
            let module = &self.module;
            let environment = &self.environment;
            match stack.find(id).map(|typ| (&[][..], typ)) {
                Some(x) => Some(x),
                None => module.get(id)
                    .map(|c| (&c.constraints[..], &c.value))
                    .or_else(|| environment.and_then(|e| e.find_type(id)))
            }
        };
        match t {
            Some((constraints, typ)) => {
                let x = self.subs.instantiate_constrained(constraints, typ);
                debug!("Find {} : {:?}", id, x);
                Ok(x)
            }
            None => Err(UndefinedVariable(id.clone()))
        }
    }

    fn find_type_info(&self, id: &InternedStr) -> Result<&[ast::Constructor<TcIdent>], TypeError> {
        self.type_infos.find_type_info(id)
            .or_else(|| self.environment.and_then(|e| e.find_type_info(id)))
            .map(|s| Ok(s))
            .unwrap_or_else(|| Err(UndefinedStruct(id.clone())))
    }
    
    fn stack_var(&mut self, id: InternedStr, typ: TcType) {
        self.stack.insert(id, typ);
    }

    pub fn add_environment(&mut self, env: &'a TypeEnv) {
        self.environment = Some(env);
    }

    pub fn typecheck_module(&mut self, module: &mut ast::Module<TcIdent>) -> Result<(), StringErrors> {
        
        for f in module.globals.iter_mut() {
            self.module.insert(f.declaration.name, f.declaration.typ.clone());
        }
        for t in module.traits.iter_mut() {
            for decl in t.declarations.iter_mut() {
                self.module.insert(decl.name, ast::Constrained {
                    constraints: vec![ast::Constraint {
                        type_variable: t.self_variable,
                        name: t.name,
                    }],//The self type should have the trait itself as a constraint
                    value: decl.typ.value.clone()
                });
            }
        }
        for data in module.datas.iter_mut() {
            for ctor in data.constructors.iter_mut() {
                let mut args = Vec::new();
                ctor.arguments.each_type(|t| {
                    args.push(t.clone());
                });
                let variables = data.constraints.iter()
                    .map(|cs| Type::Generic(*cs))
                    .collect();
                ctor.name.typ = Type::Function(args, box Type::Data(ast::TypeConstructor::Data(data.name), variables));
                self.module.insert(ctor.name.name, ast::Constrained {
                    constraints: Vec::new(),
                    value: ctor.name.typ.clone()
                });
            }
        }
        self.type_infos.add_module(module);
        for f in module.globals.iter_mut() {
            self.typecheck_global(f)
        }
        for imp in module.impls.iter_mut() {
            let x = self.typecheck_impl(imp).map_err(ast::no_loc);
            self.errors.handle(x);
        }
        if self.errors.has_errors() {
            Err(::std::mem::replace(&mut self.errors, Errors::new()))
        }
        else {
            Ok(())
        }
    }
    fn typecheck_impl(&mut self, imp: &mut ast::Impl<TcIdent>) -> Result<(), TypeError> {
        {
            let trait_globals = try!(find_trait(&self.type_infos, &imp.trait_name));
            let constraints = &imp.constraints;
            for func in imp.globals.iter_mut() {
                add_impl_constraints(constraints, &mut func.declaration);
                let trait_function_type = try!(trait_globals.iter()
                    .find(|& &(name, _)| name == func.declaration.name)
                    .map(Ok)
                    .unwrap_or_else(|| Err(StringError("Function does not exist in trait"))));
                let tf = self.subs.instantiate(&trait_function_type.1.value);
                try!(self.unify(&tf, func.type_of().clone()));
            }
        }
        for f in imp.globals.iter_mut() {
            self.typecheck_global(f);
        }
        Ok(())
    }

    
    fn typecheck_global(&mut self, global: &mut ast::Global<TcIdent>) {
        debug!("Typecheck global {} :: {:?}", global.declaration.name, global.declaration.typ);
        self.stack.clear();
        self.subs.clear();

        //Cache the generic -> variable mapping for the type of this function
        let mut variables = HashMap::new();
        ::std::mem::swap(&mut variables, &mut self.subs.variables);

        let (real_type, inferred_type) = match (&global.declaration.typ.value, &mut global.expression) {
            (&Type::Function(ref arg_types, ref return_type), &mut ast::Located { value: ast::Expr::Lambda(ref mut lambda), location }) => {
                for (typ, arg) in arg_types.iter().zip(lambda.arguments.iter()) {
                    let typ = self.subs.instantiate_(typ);
                    debug!("{} {:?}", arg.name, typ);
                    self.stack_var(arg.name.clone(), typ);
                }
                for constraint in global.declaration.typ.constraints.iter() {
                    let c = Type::Data(ast::TypeConstructor::Data(constraint.name), Vec::new());
                    let var = self.subs.variable_for(constraint.type_variable);
                    match self.subs.constraints.entry(var) {
                        Entry::Vacant(entry) => {
                            entry.insert(vec![c]);
                        }
                        Entry::Occupied(mut entry) => {
                            entry.get_mut().push(c);
                        }
                    }
                }
                let real_type = self.subs.instantiate_(&**return_type);
                ::std::mem::swap(&mut variables, &mut self.subs.variables);
                let inferred_type = match self.typecheck(&mut *lambda.body) {
                    Ok(typ) => typ,
                    Err(err) => {
                        self.errors.error(ast::Located { location: location, value: err });
                        return;
                    }
                };
                lambda.id.typ = global.declaration.typ.value.clone();
                (real_type, inferred_type)
            }
            (generic_type, expr) => {
                let real_type = self.subs.instantiate_(generic_type);
                ::std::mem::swap(&mut variables, &mut self.subs.variables);
                let inferred_type = match self.typecheck(expr) {
                    Ok(typ) => typ,
                    Err(err) => {
                        self.errors.error(ast::Located { location: expr.location, value: err });
                        return;
                    }
                };
                (real_type, inferred_type)
            }
        };
        match self.merge(real_type, inferred_type) {
            Ok(_) => self.replace_vars(&variables, &mut global.expression),
            Err(err) => {
                debug!("End {} ==> {:?}", global.declaration.name, err);
                self.errors.error(ast::Located { location: global.expression.location, value: err });
            }
        }
    }

    fn replace_vars(&mut self, variables: &HashMap<InternedStr, u32>, expr: &mut ast::LExpr<TcIdent>) {
        //Insert all type variables in the type declaration so that they get replaced by their
        //corresponding generic variable
        for (generic_id, var_id) in variables {
            self.subs.map.insert(*var_id, box Type::Generic(*generic_id));
        }
        //Replace all type variables with their inferred types
        struct ReplaceVisitor<'a, 'b:'a> { tc: &'a mut Typecheck<'b> }
        impl <'a, 'b> ReplaceVisitor<'a, 'b> {
            fn finish_type(&mut self, location: ast::Location, typ: &mut TcType) {
                let mut unbound_variable = false;
                ast::walk_mut_type(typ, &mut |typ| {
                    self.tc.replace_variable(typ);
                    if let Type::Variable(_) = *typ {
                        unbound_variable = true;
                    }
                });
                if unbound_variable {
                    self.tc.errors.error(ast::Located { location: location, value: TypeError::UnboundVariable });
                }
            }
        }
        impl <'a, 'b> MutVisitor for ReplaceVisitor<'a, 'b> {
            type T = TcIdent;
            fn visit_expr(&mut self, e: &mut ast::LExpr<TcIdent>) {
                match e.value {
                    ast::Expr::Identifier(ref mut id) => self.finish_type(e.location, &mut id.typ),
                    ast::Expr::FieldAccess(_, ref mut id) => self.finish_type(e.location, &mut id.typ),
                    ast::Expr::Array(ref mut array) => self.finish_type(e.location, &mut array.id.typ),
                    ast::Expr::Lambda(ref mut lambda) => self.finish_type(e.location, &mut lambda.id.typ),
                    ast::Expr::Match(_, ref mut alts) => {
                        for alt in alts.iter_mut() {
                            match alt.pattern {
                                ast::ConstructorPattern(ref mut id, ref mut args) => {
                                    self.finish_type(e.location, &mut id.typ);
                                    for arg in args.iter_mut() {
                                        self.finish_type(e.location, &mut arg.typ);
                                    }
                                }
                                ast::IdentifierPattern(ref mut id) => self.finish_type(e.location, &mut id.typ)
                            }
                        }
                    }
                    _ => ()
                }
                ast::walk_mut_expr(self, e);
            }
        }
        ReplaceVisitor { tc: self }.visit_expr(expr);
    }

    pub fn typecheck_expr(&mut self, expr: &mut ast::LExpr<TcIdent>) -> Result<TcType, StringErrors> {
        let typ = match self.typecheck(expr) {
            Ok(typ) => typ,
            Err(err) => {
                self.errors.error(ast::Located { location: expr.location, value: err });
                return Err(::std::mem::replace(&mut self.errors, Errors::new()));
            }
        };
        if self.errors.has_errors() {
            Err(::std::mem::replace(&mut self.errors, Errors::new()))
        }
        else {
            self.replace_vars(&HashMap::new(), expr);
            Ok(typ)
        }
    }
    fn typecheck(&mut self, expr: &mut ast::LExpr<TcIdent>) -> TcResult {
        match self.typecheck_(expr) {
            Ok(typ) => Ok(typ),
            Err(err) => {
                self.errors.error(ast::Located { location: expr.location, value: err });
                Ok(self.subs.new_var())
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
                    ast::Integer(_) => INT_TYPE.clone(),
                    ast::Float(_) => FLOAT_TYPE.clone(),
                    ast::String(_) => STRING_TYPE.clone(),
                    ast::Bool(_) => BOOL_TYPE.clone()
                })
            }
            ast::Expr::Call(ref mut func, ref mut args) => {
                let func_type = try!(self.typecheck(&mut**func));
                let a = (0..args.len()).map(|_| self.subs.new_var()).collect();
                let f = Type::Function(a, Box::new(self.subs.new_var()));
                let func_type = try!(self.unify(&f, func_type));
                match func_type {
                    Type::Function(arg_types, return_type) => {
                        if arg_types.len() != args.len() {
                            return Err(WrongNumberOfArguments(arg_types.len(), args.len()));
                        }
                        for (arg_type, arg) in arg_types.iter().zip(args.iter_mut()) {
                            let actual = try!(self.typecheck(arg));
                            try!(self.unify(arg_type, actual));
                        }
                        Ok(*return_type)
                    }
                    t => Err(NotAFunction(t))
                }
            }
            ast::Expr::IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
                let pred_type = try!(self.typecheck(&mut**pred));
                try!(self.unify(&BOOL_TYPE, pred_type));
                let true_type = try!(self.typecheck(&mut**if_true));
                let false_type = match *if_false {
                    Some(ref mut if_false) => try!(self.typecheck(&mut**if_false)),
                    None => UNIT_TYPE.clone()
                };
                self.unify(&true_type, false_type)
            }
            ast::Expr::While(ref mut pred, ref mut expr) => {
                let pred_type = try!(self.typecheck(&mut **pred));
                try!(self.unify(&BOOL_TYPE, pred_type));
                self.typecheck(&mut**expr)
                    .map(|_| UNIT_TYPE.clone())
            }
            ast::Expr::BinOp(ref mut lhs, ref mut op, ref mut rhs) => {
                let lhs_type = try!(self.typecheck(&mut**lhs));
                let rhs_type = try!(self.typecheck(&mut**rhs));
                try!(self.unify(&lhs_type, rhs_type.clone()));
                match AsRef::<str>::as_ref(op) {
                    "+" | "-" | "*" => {
                        let b = {
                            let lt = self.subs.real_type(&lhs_type);
                            *lt == INT_TYPE || *lt == FLOAT_TYPE
                        };
                        if b {
                            Ok(lhs_type)
                        }
                        else {
                            return Err(StringError("Expected numbers in binop"))
                        }
                    }
                    "&&" | "||" => self.unify(&BOOL_TYPE, lhs_type),
                    "=="| "!=" | "<" | ">" | "<=" | ">=" => Ok(BOOL_TYPE.clone()),
                    _ => Err(UndefinedVariable(op.name.clone()))
                }
            }
            ast::Expr::Block(ref mut exprs) => {
                self.stack.enter_scope();
                let mut typ = Type::Builtin(ast::UnitType);
                for expr in exprs.iter_mut() {
                    typ = try!(self.typecheck(expr));
                }
                self.stack.exit_scope();
                Ok(typ)
            }
            ast::Expr::Match(ref mut expr, ref mut alts) => {
                let typ = try!(self.typecheck(&mut**expr));
                self.stack.enter_scope();
                try!(self.typecheck_pattern(&mut alts[0].pattern, typ.clone()));
                let alt1_type = try!(self.typecheck(&mut alts[0].expression));
                self.stack.exit_scope();

                for alt in alts.iter_mut().skip(1) {
                    self.stack.enter_scope();
                    try!(self.typecheck_pattern(&mut alt.pattern, typ.clone()));
                    let alt_type = try!(self.typecheck(&mut alt.expression));
                    self.stack.exit_scope();
                    try!(self.unify(&alt1_type, alt_type));
                }
                Ok(alt1_type)
            }
            ast::Expr::Let(ref mut id, ref mut expr, ref mut body) => {
                let mut typ = try!(self.typecheck(&mut **expr));
                if id.typ != UNIT_TYPE {
                    typ = try!(self.unify(&id.typ, typ));
                }
                self.stack_var(id.name.clone(), typ);
                body.as_mut().map(|body| self.typecheck(&mut **body))
                    .unwrap_or(Ok(UNIT_TYPE.clone()))
            }
            ast::Expr::Assign(ref mut lhs, ref mut rhs) => {
                let rhs_type = try!(self.typecheck(&mut **rhs));
                let lhs_type = try!(self.typecheck(&mut **lhs));
                try!(self.unify(&lhs_type, rhs_type));
                Ok(UNIT_TYPE.clone())
            }
            ast::Expr::FieldAccess(ref mut expr, ref mut id) => {
                let typ = try!(self.typecheck(&mut **expr));
                match typ {
                    Type::Data(ast::TypeConstructor::Data(ref struct_id), _) => {
                        let constructors = try!(self.find_type_info(struct_id));
                        let field_type = match constructors {
                            [ast::Constructor { arguments: ast::ConstructorType::Record(ref fields), .. }] => {
                                fields.iter()
                                    .find(|field| field.name == *id.id())
                                    .map(|field| field.typ.clone())
                            }
                            _ => return Err(StringError("Field access on enum type"))
                        };
                        id.typ = match field_type {
                            Some(typ) => typ,
                            None => return Err(UndefinedField(struct_id.clone(), id.name.clone()))
                        };
                        Ok(id.typ.clone())
                    }
                    Type::Data(ast::TypeConstructor::Builtin(..), _) | Type::Builtin(..) => {
                        Err(StringError("Field access on builtin type"))
                    }
                    Type::Function(..) => Err(StringError("Field access on function")),
                    Type::Variable(..) => Err(StringError("Field acces on type variable")),
                    Type::Generic(..) => Err(StringError("Field acces on generic")),
                    Type::Array(..) => Err(StringError("Field access on array")),
                    Type::Trait(..) => Err(StringError("Field access on trait object"))
                }
            }
            ast::Expr::Array(ref mut a) => {
                let mut expected_type = self.subs.new_var();
                for expr in a.expressions.iter_mut() {
                    let typ = try!(self.typecheck(expr));
                    expected_type = try!(self.unify(&expected_type, typ));
                }
                a.id.typ = Type::Array(box expected_type);
                Ok(a.id.typ.clone())
            }
            ast::Expr::ArrayAccess(ref mut array, ref mut index) => {
                let array_type = try!(self.typecheck(&mut **array));
                let var = self.subs.new_var();
                let array_type = try!(self.unify(&Type::Array(box var), array_type));
                let typ = match array_type {
                    Type::Array(typ) => *typ,
                    typ => return Err(IndexError(typ))
                };
                let index_type = try!(self.typecheck(&mut **index));
                try!(self.unify(&INT_TYPE, index_type));
                Ok(typ)
            }
            ast::Expr::Lambda(ref mut lambda) => {
                self.stack.enter_scope();
                let mut arg_types = Vec::new();
                for arg in lambda.arguments.iter_mut() {
                    arg.typ = self.subs.new_var();
                    arg_types.push(arg.typ.clone());
                    self.stack_var(arg.name.clone(), arg.typ.clone());
                }
                let body_type = try!(self.typecheck(&mut *lambda.body));
                self.stack.exit_scope();
                lambda.id.typ = Type::Function(arg_types, box body_type);
                Ok(lambda.id.typ.clone())
            }
            ast::Expr::Type(_, _, ref mut expr) => {
                try!(self.typecheck(&mut **expr));
                panic!("Not implemented")
            }
        }
    }

    fn typecheck_pattern(&mut self, pattern: &mut ast::Pattern<TcIdent>, match_type: TcType) -> Result<(), TypeError> {
        let typename = match match_type {
            Type::Data(ast::TypeConstructor::Data(id), _) => id,
            _ => return Err(StringError("Pattern matching only works on data types"))
        };
        match *pattern {
            ast::ConstructorPattern(ref name, ref mut args) => {
                //Find the enum constructor and return the types for its arguments
                let ctor_type = {
                    let constructors = try!(self.find_type_info(&typename));
                    match constructors.iter().find(|ctor| ctor.name.id() == name.id()) {
                        Some(ctor) => ctor.name.typ.clone(),
                        None => return Err(StringError("Undefined constructor"))
                    }
                };
                let ctor_type = self.subs.instantiate(&ctor_type);
                let (argument_types, return_type) = match ctor_type {
                    Type::Function(argument_types, return_type) => {
                        (argument_types, *return_type)
                    }
                    _ => return Err(StringError("Enum constructor must be a function type"))
                };
                try!(self.unify(&match_type, return_type));
                for (arg, typ) in args.iter().zip(argument_types.into_iter()) {
                    self.stack_var(arg.id().clone(), typ);
                }
                Ok(())
            }
            ast::IdentifierPattern(ref id) => {
                self.stack_var(id.id().clone(), match_type);
                Ok(())
            }
        }
    }

    fn unify(&self, expected: &TcType, mut actual: TcType) -> TcResult {
        debug!("Unify {:?} <=> {:?}", expected, actual);
        if self.unify_(expected, &actual) {
            self.set_type(&mut actual);
            Ok(actual)
        }
        else {
            let mut expected = expected.clone();
            self.set_type(&mut expected);
            self.set_type(&mut actual);
            Err(TypeMismatch(expected, actual))
        }
    }
    fn unify_(&self, expected: &TcType, actual: &TcType) -> bool {
        let expected = self.subs.real_type(expected);
        let actual = self.subs.real_type(actual);
        debug!("{:?} <=> {:?}", expected, actual);
        match (expected, actual) {
            (&Type::Variable(ref l), _) => {
                if self.check_constraints(*l, actual) {
                    self.subs.union(*l, actual);
                    true
                }
                else {
                    false
                }
            }
            (_, &Type::Variable(ref r)) => {
                if self.check_constraints(*r, expected) {
                    self.subs.union(*r, expected);
                    true
                }
                else {
                    false
                }
            }
            (&Type::Function(ref l_args, ref l_ret), &Type::Function(ref r_args, ref r_ret)) => {
                if l_args.len() == r_args.len() {
                    l_args.iter().zip(r_args.iter()).all(|(l, r)| self.unify_(l, r)) && self.unify_(&**l_ret, &**r_ret)
                }
                else {
                    false
                }
            }
            (&Type::Array(ref l), &Type::Array(ref r)) => self.unify_(&**l, &**r),
            (&Type::Data(ast::TypeConstructor::Data(ref l), _), _) if find_trait(&self.type_infos, l).is_ok() => {
                debug!("Found trait {:?} ", l);
                self.has_impl_of_trait(actual, l)
            }
            (&Type::Trait(ref l, _), _) => {
                debug!("Found trait {:?} ", l);
                self.has_impl_of_trait(actual, l)
            }
            (&Type::Data(ref l, ref l_args), &Type::Data(ref r, ref r_args)) => {
                l == r
                && l_args.len() == r_args.len()
                && l_args.iter().zip(r_args.iter()).all(|(l, r)| self.unify_(l, r))
            }
            _ => expected == actual
        }
    }
    fn merge(&self, mut expected: TcType, mut actual: TcType) -> TcResult {
        if self.merge_(&expected, &actual) {
            Ok(expected)
        }
        else {
            self.set_type(&mut expected);
            self.set_type(&mut actual);
            Err(TypeMismatch(expected, actual))
        }
    }
    fn merge_(&self, expected: &TcType, actual: &TcType) -> bool {
        let expected = self.subs.real_type(expected);
        let actual = self.subs.real_type(actual);
        debug!("Merge {:?} {:?}", expected, actual);
        match (expected, actual) {
            (_, &Type::Variable(ref r)) => {
                self.subs.union(*r, expected);
                true
            }
            (&Type::Function(ref l_args, ref l_ret), &Type::Function(ref r_args, ref r_ret)) => {
                if l_args.len() == r_args.len() {
                    l_args.iter()
                        .zip(r_args.iter())
                        .all(|(l, r)| self.merge_(l, r))
                        && self.merge_(&**l_ret, &**r_ret)
                }
                else {
                    false
                }
            }
            (&Type::Array(ref l), &Type::Array(ref r)) => self.merge_(&**l, &**r),
            (&Type::Data(ast::TypeConstructor::Data(ref l), _), _) if find_trait(&self.type_infos, l).is_ok() => {
                self.has_impl_of_trait(actual, l)
            }
            (&Type::Data(ref l, ref l_args), &Type::Data(ref r, ref r_args)) => {
                l == r
                && l_args.len() == r_args.len()
                && l_args.iter().zip(r_args.iter()).all(|(l, r)| self.merge_(l, r))
            }
            _ => expected == actual
        }
    }
    fn check_impl(&self, constraints: &[ast::Constraint], expected: &TcType, actual: &TcType) -> bool {
        let expected = self.subs.real_type(expected);
        let actual = self.subs.real_type(actual);
        debug!("Check impl {:?} {:?}", expected, actual);
        match (expected, actual) {
            (_, &Type::Variable(_)) => {
                true
            }
            (&Type::Function(ref l_args, ref l_ret), &Type::Function(ref r_args, ref r_ret)) => {
                if l_args.len() == r_args.len() {
                    l_args.iter()
                        .zip(r_args.iter())
                        .all(|(l, r)| self.check_impl(constraints, l, r))
                        && self.check_impl(constraints, &**l_ret, &**r_ret)
                }
                else {
                    false
                }
            }
            (&Type::Array(ref l), &Type::Array(ref r)) => self.merge_(&**l, &**r),
            (&Type::Data(ast::TypeConstructor::Data(ref l), _), _) if find_trait(&self.type_infos, l).is_ok() => {
                self.has_impl_of_trait(actual, l)
            }
            (&Type::Data(ref l, ref l_args), &Type::Data(ref r, ref r_args)) => {
                l == r
                && l_args.len() == r_args.len()
                && l_args.iter().zip(r_args.iter()).all(|(l, r)| self.check_impl(constraints, l, r))
            }
            (&Type::Generic(id), _) => {
                constraints.iter()
                    .find(|constraint| constraint.type_variable == id && self.has_impl_of_trait(actual, &constraint.name))
                    .is_some()
            }
            _ => expected == actual
        }
    }
    fn has_impl_of_trait(&self, typ: &TcType, trait_id: &InternedStr) -> bool {
        debug!("Check impl {:?} {:?}", typ, trait_id);
        //If the type is the trait it self it passes the check
        match *typ {
            Type::Data(ast::TypeConstructor::Data(ref id), _) if id == trait_id => return true,
            _ => ()
        }
        match self.type_infos.impls.get(trait_id) {
            Some(impls) => {
                for impl_type in impls.iter() {
                    if self.check_impl(&impl_type.constraints, &impl_type.value, typ) {
                        return true;
                    }
                }
                false
            }
            _ => true
        }
    }

    fn check_constraints(&self, variable: u32, typ: &TcType) -> bool {
        debug!("Constraint check {:?} {:?} ==> {:?}", variable, self.subs.constraints.get(&variable), typ);
        match *typ {
            Type::Variable(_) => return true,
            _ => ()
        }
        match self.subs.constraints.get(&variable) {
            Some(trait_types) => {
                trait_types.iter()
                    .all(|trait_type| {
                        match *trait_type {
                            Type::Data(ast::TypeConstructor::Data(ref id), _) => self.has_impl_of_trait(typ, id),
                            _ => false
                        }
                    })
            }
            None => true
        }
    }

    fn set_type(&self, t: &mut TcType) {
        ast::walk_mut_type(t, &mut |typ| self.replace_variable(typ) );
    }
    
    fn replace_variable(&self, typ: &mut TcType) {
        let replacement = match *typ {
            Type::Variable(id) => {
                self.subs.find(id)
                    .map(|t| match *t {
                        Type::Data(ast::TypeConstructor::Data(ref id), ref args) if find_trait(&self.type_infos, id).is_ok() => {
                            Type::Trait(id.clone(), args.clone())
                        }
                        _ => t.clone()
                    })
            }
            Type::Data(ast::TypeConstructor::Data(ref id), ref mut args) if find_trait(&self.type_infos, id).is_ok() => {
                let a = ::std::mem::replace(args, Vec::new());
                Some(Type::Trait(*id, a))
            }
            _ => None
        };
        match replacement {
            Some(x) => *typ = x,
            None => ()
        }
    }
}

struct Substitution {
    map: HashMap<u32, Box<TcType>>,
    constraints: HashMap<u32, Vec<TcType>>,
    variables: HashMap<InternedStr, u32>,
    var_id: u32
}
impl Substitution {
    fn new() -> Substitution {
        Substitution {
            map: HashMap::new(),
            constraints: HashMap::new(),
            variables: HashMap::new(),
            var_id: 0
        }
    }

    fn variable_for(&mut self, id: InternedStr) -> u32 {
        match self.variables.entry(id) {
            Entry::Vacant(entry) => {
                self.var_id += 1;
                *entry.insert(self.var_id)
            }
            Entry::Occupied(entry) => *entry.get()
        }
    }

    fn clear(&mut self) {
        self.map.clear();
        self.constraints.clear();
        self.variables.clear();
        self.var_id = 0;
    }

    fn union(&self, id: u32, typ: &TcType) {
        {
            let id_type = self.find(id);
            let other_type = self.real_type(typ);
            if id_type.map(|x| x == other_type).unwrap_or(&Type::Variable(id) == other_type) {
                return
            }
        }
        let this: &mut Substitution = unsafe { let e: *const _ = self; ::std::mem::transmute(e) };
        //Always make sure the mapping is from a higher variable to a lower
        //This way the resulting variables are always equal to any variables in the globals
        //declaration
        match *typ {
            Type::Variable(other_id) if id < other_id => this.assign_union(other_id, Type::Variable(id)),
            _ => this.assign_union(id, typ.clone())
        }
    }
    fn assign_union(&mut self, id: u32, typ: TcType) {
        match self.constraints.remove(&id) {
            Some(constraints) => {
                match typ {
                    Type::Variable(other_id) => {
                        self.constraints.insert(other_id, constraints);
                    }
                    _ => ()
                }
            }
            None => ()
        }
        self.map.insert(id, box typ);
    }

    fn real_type<'a>(&'a self, typ: &'a TcType) -> &'a TcType {
        match *typ {
            Type::Variable(var) => match self.find(var) {
                Some(t) => t,
                None => typ
            },
            _ => typ
        }
    }

    fn find(&self, var: u32) -> Option<&TcType> {
        //Use unsafe so that we can hold a reference into the map and continue
        //to look for parents
        //Since we never have a cycle in the map we will never hold a &mut
        //to the same place
        let this: &mut Substitution = unsafe { let s: *const _ = self; ::std::mem::transmute(s) };
        this.map.get_mut(&var).map(|typ| {
            match **typ {
                Type::Variable(parent_var) if parent_var != var => {
                    match self.find(parent_var) {
                        Some(other) => { **typ = other.clone(); }
                        None => ()
                    }
                    &**typ
                }
                _ => &**typ
            }
        })
    }

    fn new_var(&mut self) -> TcType {
        self.var_id += 1;
        Type::Variable(self.var_id)
    }

    fn instantiate_constrained(&mut self, constraints: &[ast::Constraint], typ: &TcType) -> TcType {
        self.variables.clear();
        for constraint in constraints.iter() {
            let c = Type::Data(ast::TypeConstructor::Data(constraint.name), Vec::new());
            let var = self.variable_for(constraint.type_variable);
            match self.constraints.entry(var) {
                Entry::Vacant(entry) => {
                    entry.insert(vec![c]);
                }
                Entry::Occupied(entry) => {
                    entry.into_mut().push(c);
                }
            }
        }
        self.instantiate_(typ)
    }
    fn instantiate(&mut self, typ: &TcType) -> TcType {
        self.variables.clear();
        self.instantiate_(typ)
    }
    fn instantiate_(&mut self, typ: &TcType) -> TcType {
        match *typ {
            Type::Generic(x) => {
                let var = self.variable_for(x);
                debug!("Bind generic {} -> {}", x, var);
                Type::Variable(var)
            }
            Type::Function(ref args, ref return_type) => {
                let args2 = args.iter().map(|a| self.instantiate_(a)).collect();
                Type::Function(args2, box self.instantiate_(&**return_type))
            }
            Type::Array(ref typ) => Type::Array(box self.instantiate_(&**typ)),
            Type::Data(ref id, ref args) => {
                let args2 = args.iter().map(|a| self.instantiate_(a)).collect();
                Type::Data(id.clone(), args2)
            }
            Type::Trait(ref id, ref args) => {
                let args2 = args.iter().map(|a| self.instantiate_(a)).collect();
                Type::Trait(*id, args2)
            }
            ref x => x.clone()
        }
    }
}

pub trait Typed {
    type Id;
    fn type_of(&self) -> &Type<Self::Id>;
}
impl <Id> Typed for TcIdent<Id> {
    type Id = Id;
    fn type_of(&self) -> &Type<Id> {
        &self.typ
    }
}
impl <Id> Typed for ast::Expr<Id>
    where Id: Typed<Id=InternedStr> + AsRef<str> + ast::AstId<Untyped=InternedStr> {
    type Id = Id::Id;
    fn type_of(&self) -> &Type<Id::Untyped> {
        match *self {
            ast::Expr::Identifier(ref id) => id.type_of(),
            ast::Expr::Literal(ref lit) => {
                match *lit {
                    ast::Integer(_) => &INT_TYPE,
                    ast::Float(_) => &FLOAT_TYPE,
                    ast::String(_) => &STRING_TYPE,
                    ast::Bool(_) => &BOOL_TYPE
                }
            }
            ast::Expr::IfElse(_, ref arm, _) => arm.type_of(),
            ast::Expr::Block(ref exprs) => {
                match exprs.last() {
                    Some(last) => last.type_of(),
                    None => &UNIT_TYPE
                }
            }
            ast::Expr::BinOp(ref lhs, ref op, _) => {
                match AsRef::<str>::as_ref(op) {
                    "+" | "-" | "*" => lhs.type_of(),
                    "<" | ">" | "<=" | ">=" | "==" | "!=" | "&&" | "||" => &BOOL_TYPE,
                    _ => panic!()
                }
            }
            ast::Expr::Let(..) | ast::Expr::While(..) | ast::Expr::Assign(..) => &UNIT_TYPE,
            ast::Expr::Call(ref func, _) => {
                match func.type_of() {
                    &Type::Function(_, ref return_type) => &**return_type,
                    x => panic!("{:?}", x)
                }
            }
            ast::Expr::Match(_, ref alts) => alts[0].expression.type_of(),
            ast::Expr::FieldAccess(_, ref id) => id.type_of(),
            ast::Expr::Array(ref a) => a.id.type_of(),
            ast::Expr::ArrayAccess(ref array, _) => match array.type_of() {
                &Type::Array(ref t) => &**t,
                t => panic!("Not an array type {:?}", t)
            },
            ast::Expr::Lambda(ref lambda) => lambda.id.type_of(),
            ast::Expr::Type(_, _, ref expr) => expr.type_of()
        }
    }
}

impl <T: Typed + ast::AstId> Typed for ast::Global<T> {
    type Id = T::Untyped;
    fn type_of(&self) -> &Type<T::Untyped> {
        &self.declaration.typ.value
    }
}

impl Typed for Option<Box<ast::Located<ast::Expr<TcIdent>>>> {
    type Id = InternedStr;
    fn type_of(&self) -> &TcType {
        match *self {
            Some(ref t) => t.type_of(),
            None => &UNIT_TYPE
        }
    }
}


#[cfg(test)]
mod tests {
    use super::{Typecheck, Typed, TcIdent, INT_TYPE, BOOL_TYPE, FLOAT_TYPE, Type};
    use base::ast;
    use parser::{Parser, ParseResult};
    use super::super::tests::{get_local_interner, intern};

    pub fn parse<F, T>(s: &str, f: F) -> T
        where F: FnOnce(&mut Parser<TcIdent>) -> ParseResult<T> {
        use std::io::BufReader;
        let mut buffer = BufReader::new(s.as_bytes());
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();
        let &mut (ref mut interner, ref mut gc) = &mut *interner;
        let mut parser = Parser::new(interner, gc, &mut buffer);
        f(&mut parser)
            .unwrap_or_else(|err| panic!("{:?}", err))
    }

    pub fn parse_new(s: &str) -> ast::LExpr<TcIdent> {
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();
        let &mut(ref mut interner, ref mut gc) = &mut *interner;
        let x = ::parser_new::parse_tc(gc, interner, s)
            .unwrap_or_else(|err| panic!("{:?}", err));
        x
    }


    #[test]
    fn function_type_new() {
        let text = 
r"
\x -> x
";
        let mut expr = parse_new(text);
        let mut tc = Typecheck::new();
        let result = tc.typecheck_expr(&mut expr);
        assert!(result.is_ok());
        match result.unwrap() {
            Type::Function(_, _) => {
                assert!(true);
            }
            _ => assert!(false)
        }
    }


    #[test]
    fn while_() {
        let text =
r"
main : () -> ();
main = \ -> { let x = 2; while x < 10 { x } }";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| panic!("{:?}", err))

    }
    #[test]
    fn enums() {
        let text = 
r"
data AB = A(Int) | B(Float)

main : () -> Int;
main = \ -> {
    match A(1) {
        A(x) => { x }
        B(x) => { 0 }
    }
}";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| panic!("{:?}", err))

    }
    #[test]
    fn trait_function() {
        let text = 
r"
data Vec = Vec {
    x: Int,
    y: Int
}

trait Add a {
    add : (a, a) -> a;
}

impl Add for Vec {
    add : (Vec, Vec) -> Vec;
    add = \l r -> {
        Vec(l.x + r.x, l.y + r.y)
    }
}

test : (Vec) -> Vec;
test = \v -> {
    add(v, Vec(1, 1))
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| panic!("{:?}", err))

    }
    #[test]
    ///Check that implementations with its types wrong are not allowed
    fn traits_wrong_self() {
        let text = 
r"
data Vec = Vec {
    x: Int,
    y: Int
}

trait Add a {
    add : (a, a) -> a;
}

impl Add for Vec {
    add : (Vec, Vec) -> Int;
    add = \x y -> {
        2
    }
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        let result = tc.typecheck_module(&mut module);
        assert!(result.is_err());
    }
    #[test]
    fn function_type() {
        let text = 
r"
test : (Int) -> Float;
test = \x -> {
    1.0
}

higher_order : (Int, (Int) -> Float) -> Float;
higher_order = \x f -> {
    f(x)
}

test2 : () -> ();
test2 = \ -> {
    higher_order(1, test);
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        let result = tc.typecheck_module(&mut module);
        assert!(result.is_err());
    }
    #[test]
    fn array_type() {
        let text = 
r"
test : (Int) -> [Int];
test = \x -> {
    [1,2,x]
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| panic!("{:?}", err));
    }
    #[test]
    fn array_unify() {
        let text = 
r"
test : () -> [Int];
test = \ -> [];
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| panic!("{:?}", err));
    }
    #[test]
    fn lambda() {
        let text = 
r"
main : () -> Int;
main = \ -> {
    let f = adder(2);
    f(3)
}
adder : (Int) -> (Int) -> Int;
adder = \x -> {
    \y -> x + y
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| panic!("{:?}", err));
    }
    #[test]
    fn generic_function() {
        let text = 
r"
main : () -> Int;
main = \ -> {
    let x = 1;
    id(x)
}
id : (a) -> a;
id = \x -> x;
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| panic!("{:?}", err));
    }
    #[test]
    fn generic_function_map() {
        let text = 
r"
main : () -> Float;
main = \ -> {
    let xs = [1,2,3,4];
    transform(xs, \x -> [x]);
    transform(1, \x -> 1.0)
}
transform : (a, (a) -> b) -> b;
transform = \x f -> {
    f(x)
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| panic!("{:?}", err));
        match module.globals[0].expression.value {
            ast::Expr::Lambda(ref lambda) => {
                match lambda.body.value {
                    ast::Expr::Block(ref exprs) => {
                        assert_eq!(exprs[2].value.type_of(), &FLOAT_TYPE);
                    }
                    _ => panic!()
                }
            }
            _ => panic!()
        }
    }
    #[test]
    fn specialized_generic_function_error() {
        let text = 
r"
id : (a) -> a;
id = \x -> 2;
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .err()
            .unwrap();
    }
    #[test]
    fn unify_parameterized_types() {
        let text = 
r"
data Option a = Some(a) | None()

is_positive : (Float) -> Option Float;
is_positive = \x -> {
    if x < 0.0 {
        None()
    }
    else {
        Some(x)
    }
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| panic!("{:?}", err));
        match module.globals[0].expression.value {
            ast::Expr::Lambda(ref lambda) => {
                match lambda.body.value {
                    ast::Expr::Block(ref exprs) => {
                        match exprs[0].value {
                            ast::Expr::IfElse(_, ref if_true, ref if_false) => {
                                assert_eq!(if_true.type_of(), if_false.type_of());
                                assert_eq!(if_false.type_of(), &Type::Data(ast::TypeConstructor::Data(intern("Option")), vec![FLOAT_TYPE.clone()]));
                            }
                            _ => panic!()
                        }
                    }
                    _ => panic!()
                }
            }
            _ => panic!()
        }
    }
    #[test]
    fn paramter_mismatch() {
        let text = 
r"
data Option a = Some(a) | None()

test: (Float) -> Option Int;
test = \x -> {
    if x < 0.0 {
        None()
    }
    else {
        Some(y)
    }
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .err()
            .unwrap();
    }


    #[test]
    fn typecheck_trait_for_generic_types() {
        let text = 
r"
trait Eq a {
    eq : (a, a) -> Bool;
}
data Option a = Some(a) | None()

impl Eq for Int {
    eq : (Int, Int) -> Bool;
    eq = \l r -> {
        l == r
    }
}
impl <Eq a> Eq for Option a {
    eq : (Option a, Option a) -> Bool;
    eq = \l r -> {
        match l {
            Some(l_val) => {
                match r {
                    Some(r_val) => { eq(l_val, r_val) }
                    None() => { false }
                }
            }
            None() => {
                match r {
                    Some(_) => { false }
                    None() => { true }
                }
            }
        }
    }
}
test : () -> Bool;
test = \ -> {
    eq(Some(2), None())
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| panic!("{:?}", err));
        match module.globals[0].expression.value {
            ast::Expr::Lambda(ref lambda) => {
                match lambda.body.value {
                    ast::Expr::Block(ref exprs) => {
                        match exprs[0].value {
                            ast::Expr::Call(ref f, ref args) => {
                                let int_opt = Type::Data(ast::TypeConstructor::Data(intern("Option")), vec![INT_TYPE.clone()]);
                                assert_eq!(f.type_of(), &(Type::Function(vec![int_opt.clone(), int_opt.clone()], box BOOL_TYPE.clone())));
                                assert_eq!(args[0].type_of(), &int_opt);
                                assert_eq!(args[1].type_of(), &int_opt);
                            }
                            ref x => panic!("{:?}", x)
                        }
                    }
                    ref x => panic!("{:?}", x)
                }
            }
            ref x => panic!("{:?}", x)
        }
    }
    #[test]
    fn error_no_impl_for_parameter() {
        let text = 
r"
trait Eq a {
    eq : (a, a) -> Bool;
}
data Option a = Some(a) | None()

impl <Eq a> Eq for Option a {
    eq : (Option a, Option a) -> Bool;
    eq = \l r -> false
}
test : () -> Bool;
test = \ -> eq(Some(2), None());

";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        let result = tc.typecheck_module(&mut module);
        assert!(result.is_err());
    }

    #[test]
    fn and_or() {
        let text = 
r"
test : (Float) -> Bool;
test = \x -> x < 0.0 && true || x > 1.0;
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| panic!("{:?}", err));
    }
    #[test]
    fn and_type_error() {
        let text = 
r"
test : () -> Bool;
test = \ -> {
    1 && true
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .err()
            .unwrap();
    }
    #[test]
    fn global_variable() {
        let text = 
r#"

global : Int;
global = { 123 }

main : () -> Int;
main = \ -> { global + 2 }

"#;
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| panic!("{:?}", err));
    }
    #[test]
    fn global_variable_error() {
        let text = 
r#"

global : Int;
global = { "" }

"#;
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .err()
            .unwrap();
    }
    #[test]
    fn unbound_variable_error() {
        let text = 
r#"

test : Int;
test = { let x = []; 1 }

"#;
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .err()
            .unwrap();
    }
}
