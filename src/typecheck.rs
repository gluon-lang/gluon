use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt;
use scoped_map::ScopedMap;
use ast;
use ast::MutVisitor;
use interner::InternedStr;

use self::TypeError::*;

pub use ast::TypeEnum::{Type, FunctionType, TraitType, TypeVariable, BuiltinType, Generic, ArrayType};


pub static INT_TYPE: TcType = BuiltinType(ast::IntType);
pub static FLOAT_TYPE: TcType = BuiltinType(ast::FloatType);
pub static STRING_TYPE: TcType = BuiltinType(ast::StringType);
pub static BOOL_TYPE: TcType = BuiltinType(ast::BoolType);
pub static UNIT_TYPE: TcType = BuiltinType(ast::UnitType);


#[derive(Clone, Eq, PartialEq, Debug)]
pub struct TcIdent {
    pub typ: TcType,
    pub name: InternedStr
}
impl TcIdent {
    pub fn id(&self) -> &InternedStr {
        &self.name
    }
}

impl Str for TcIdent {
    fn as_slice(&self) -> &str {
        self.name.as_slice()
    }
}

pub type TcType = ast::TypeEnum<InternedStr>;

pub fn match_types(l: &TcType, r: &TcType) -> bool {
    fn type_eq<'a>(vars: &mut HashMap<TcType, &'a TcType>, l: &'a TcType, r: &'a TcType) -> bool {
        match (l, r) {
            (&TypeVariable(_), _) => var_eq(vars, l.clone(), r),
            (&Generic(_), _) => var_eq(vars, l.clone(), r),
            (&FunctionType(ref l_args, ref l_ret), &FunctionType(ref r_args, ref r_ret)) => {
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
            (&ArrayType(ref l), &ArrayType(ref r)) => type_eq(vars, &**l, &**r),
            (&Type(ref l, ref l_args), &Type(ref r, ref r_args)) => {
                l == r
                && l_args.len() == r_args.len()
                && l_args.iter().zip(r_args.iter()).all(|(l, r)| type_eq(vars, l, r))
            }
            (&TraitType(ref l, ref l_args), &TraitType(ref r, ref r_args)) => {
                l == r
                && l_args.len() == r_args.len()
                && l_args.iter().zip(r_args.iter()).all(|(l, r)| type_eq(vars, l, r))
            }
            (&BuiltinType(ref l), &BuiltinType(ref r)) => l == r,
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


impl fmt::Debug for TcType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fn fmt_type(f: &mut fmt::Formatter, t: &InternedStr, args: &[TcType]) -> fmt::Result {
            try!(write!(f, "{:?}", t));
            match args {
                [ref first, rest..] => {
                    try!(write!(f, "<"));
                    try!(write!(f, "{:?}", first));
                    for arg in rest.iter() {
                        try!(write!(f, ", {:?}", arg));
                    }
                    try!(write!(f, ">"));
                }
                [] => ()
            }
            Ok(())
        }
        match *self {
            Type(ref t, ref args) => fmt_type(f, t, args.as_slice()),
            TraitType(ref t, ref args) => {
                try!(write!(f, "$"));
                fmt_type(f, t, args.as_slice())
            }
            TypeVariable(ref x) => x.fmt(f),
            Generic(x) => write!(f, "#{:?}", x),
            FunctionType(ref args, ref return_type) => write!(f, "fn {:?} -> {:?}", args, return_type),
            BuiltinType(ref t) => t.fmt(f),
            ArrayType(ref t) => write!(f, "[{:?}]", t)
        }
    }
}

#[derive(Debug)]
pub struct Constrained<T, I = InternedStr> {
    pub constraints: Vec<ast::Constraint<I>>,
    pub value: T
}

fn from_impl_type(constraints: &[ast::Constraint], decl: &mut ast::FunctionDeclaration<TcIdent>) -> Constrained<TcType> {
    //Add all constraints from the impl declaration to the functions declaration
    for constraint in constraints.iter() {
        let exists = {
            decl.type_variables.iter()
                .find(|func_constraint| *func_constraint == constraint)
                .is_some()
        };
        if !exists {
            decl.type_variables.push(constraint.clone());
        }
    }
    from_declaration(decl)
}

fn from_declaration_with_self(decl: &ast::FunctionDeclaration<TcIdent>, self_var: InternedStr) -> Constrained<TcType> {
    let variables = decl.type_variables.as_slice();
    let type_handler = |&mut: type_id: InternedStr| {
        if type_id == self_var {
            Some(Generic(self_var))
        }
        else {
            variables.iter()
                .find(|v| v.type_variable == type_id)
                .map(|v| Generic(v.type_variable))
        }
    };
    from_declaration_(type_handler, decl)
}
fn from_declaration(decl: &ast::FunctionDeclaration<TcIdent>) -> Constrained<TcType> {
    let variables = decl.type_variables.as_slice();
    let type_handler = |&mut: type_id| {
        variables.iter()
            .find(|v| v.type_variable == type_id)
            .map(|v| Generic(v.type_variable))
    };
    from_declaration_(type_handler, decl)
}
fn from_declaration_<F>(mut type_handler: F, decl: &ast::FunctionDeclaration<TcIdent>) -> Constrained<TcType>
    where F: FnMut(InternedStr) -> Option<TcType> {
    let args = decl.arguments.iter()
        .map(|f| from_generic_type(&mut type_handler, f))
        .collect();
    Constrained {
        constraints: decl.type_variables.clone(),
        value: FunctionType(args, box from_generic_type(&mut type_handler, &decl.return_type))
    }
}

pub fn from_constrained_type(variables: &[ast::Constraint], typ: &ast::VMType) -> TcType {
    let mut type_handler = |&mut: type_id| {
        variables.iter()
            .find(|v| v.type_variable == type_id)
            .map(|v| Generic(v.type_variable))
    };
    from_generic_type(&mut type_handler, typ)
}
fn from_generic_type<F>(type_handler: &mut F, typ: &ast::VMType) -> TcType
    where F: FnMut(InternedStr) -> Option<TcType> {
    match *typ {
        ast::Type(ref type_id, ref args) => {
            match (*type_handler)(*type_id) {
                Some(typ) => typ,
                None => {
                    let args2 = args.iter().map(|a| from_generic_type(type_handler, a)).collect();
                    Type(*type_id, args2)
                }
            }
        }
        ast::FunctionType(ref args, ref return_type) => {
            let args2 = args.iter()
                .map(|a| from_generic_type(type_handler, a))
                .collect();
            FunctionType(args2, box from_generic_type(type_handler, &**return_type))
        }
        ast::BuiltinType(ref id) => BuiltinType(*id),
        ast::ArrayType(ref typ) => ArrayType(box from_generic_type(type_handler, &**typ)),
        ast::TraitType(ref id, ref args) => {
            let args2 = args.iter()
                .map(|a| from_generic_type(type_handler, a))
                .collect();
            Type(*id, args2)
        }
        ast::TypeVariable(ref id) => TypeVariable(*id),
        ast::Generic(ref id) => Generic(*id),
    }
}

#[derive(Debug)]
enum TypeError {
    UndefinedVariable(InternedStr),
    NotAFunction(TcType),
    WrongNumberOfArguments(usize, usize),
    TypeMismatch(TcType, TcType),
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
    pub impls: HashMap<InternedStr, Vec<Constrained<TcType>>>,
    pub traits: HashMap<InternedStr, Vec<(InternedStr, Constrained<TcType>)>>
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
    pub fn find_trait(&self, name: &InternedStr) -> Option<&[(InternedStr, Constrained<TcType>)]> {
        self.traits.get(name).map(|v| v.as_slice())
    }
    pub fn add_module(&mut self, module: &ast::Module<TcIdent>) {
        for data in module.datas.iter() {
            self.datas.insert(data.name.name, data.constructors.clone());
        }
        for t in module.traits.iter() {
            let function_types = t.declarations.iter().map(|f| {
                let typ = from_declaration_with_self(f, t.self_variable);
                (f.name.id().clone(), typ)
            }).collect();
            self.traits.insert(t.name.id().clone(), function_types);
        }
        for imp in module.impls.iter() {
            let imp_type = from_constrained_type(imp.type_variables.as_slice(), &imp.typ);
            let trait_name = imp.trait_name.id().clone();
            let set = match self.impls.entry(trait_name) {
                Entry::Occupied(v) => v.into_mut(),
                Entry::Vacant(v) => v.insert(Vec::new())
            };
            set.push(Constrained { constraints: imp.type_variables.clone(), value: imp_type });
        }
    }
    pub fn extend(&mut self, other: TypeInfos) {
        let TypeInfos { datas, impls, traits } = other;
        for (id, data) in datas.into_iter() {
            self.datas.insert(id, data);
        }
        for (id, impl_) in impls.into_iter() {
            self.impls.insert(id, impl_);
        }
        for (id, trait_) in traits.into_iter() {
            self.traits.insert(id, trait_);
        }
    }
}
fn find_trait<'a>(this: &'a TypeInfos, name: &InternedStr) -> Result<&'a [(InternedStr, Constrained<TcType>)], TypeError> {
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
    module: HashMap<InternedStr, Constrained<TcType>>,
    stack: ScopedMap<InternedStr, TcType>,
    subs: Substitution,
    errors: Errors<ast::Located<TypeError>>
}

#[derive(Debug)]
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
            match stack.find(id).map(|typ| ([].as_slice(), typ)) {
                Some(x) => Some(x),
                None => module.get(id)
                    .map(|c| (c.constraints.as_slice(), &c.value))
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
        
        for f in module.functions.iter_mut() {
            let decl = &mut f.declaration;
            let constrained_type = from_declaration(decl);
            decl.name.typ = constrained_type.value.clone();
            self.module.insert(decl.name.name, constrained_type);
        }
        for t in module.traits.iter_mut() {
            for func in t.declarations.iter_mut() {
                let constrained_type = from_declaration_with_self(func, t.self_variable);
                func.name.typ = constrained_type.value.clone();
                self.module.insert(func.name.id().clone(), Constrained {
                    constraints: vec![ast::Constraint {
                        type_variable: t.self_variable,
                        name: t.name.name,
                    }],//The self type should have the trait itself as a constraint
                    value: func.name.typ.clone()
                });
            }
        }
        for data in module.datas.iter_mut() {
            let type_variables = data.type_variables.as_slice();
            for ctor in data.constructors.iter_mut() {
                let mut args = Vec::new();
                let mut type_handler = |&mut: type_id| {
                    type_variables.iter()
                        .find(|v| **v == type_id)
                        .map(|v| Generic(*v))
                };
                ctor.arguments.each_type(|t| {
                    args.push(from_generic_type(&mut type_handler, t));
                });
                let variables = data.type_variables.iter()
                    .map(|cs| Generic(*cs))
                    .collect();
                ctor.name.typ = FunctionType(args, box Type(data.name.name, variables));
                self.module.insert(ctor.name.name, Constrained {
                    constraints: Vec::new(),
                    value: ctor.name.typ.clone()
                });
            }
        }
        self.type_infos.add_module(module);
        for f in module.functions.iter_mut() {
            self.typecheck_function(f)
        }
        for imp in module.impls.iter_mut() {
            imp.typ = from_constrained_type(imp.type_variables.as_slice(), &imp.typ);
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
            let trait_functions = try!(find_trait(&self.type_infos, imp.trait_name.id()));
            let type_variables = imp.type_variables.as_slice();
            for func in imp.functions.iter_mut() {
                let c_type = from_impl_type(type_variables, &mut func.declaration);
                func.declaration.name.typ = c_type.value;
                let trait_function_type = try!(trait_functions.iter()
                    .find(|& &(ref name, _)| name == func.declaration.name.id())
                    .map(Ok)
                    .unwrap_or_else(|| Err(StringError("Function does not exist in trait"))));
                let tf = self.subs.instantiate(&trait_function_type.1.value);
                try!(self.unify(&tf, func.type_of().clone()));
            }
        }
        for f in imp.functions.iter_mut() {
            self.typecheck_function(f);
        }
        Ok(())
    }

    
    fn typecheck_function(&mut self, function: &mut ast::Function<TcIdent>) {
        debug!("Typecheck function {} :: {:?}", function.declaration.name.id(), function.declaration.name.typ);
        self.stack.clear();
        self.subs.clear();
        let (arguments, body) = match function.expression.value {
            ast::Lambda(ref mut lambda) => (&mut *lambda.arguments, &mut *lambda.body),
            _ => panic!("Not a lambda in function declaration")
        };
        let return_type = match function.declaration.name.typ {
            FunctionType(ref arg_types, ref return_type) => {
                for (typ, arg) in arg_types.iter().zip(arguments.iter()) {
                    let typ = self.subs.instantiate(typ);
                    debug!("{} {:?}", arg.name, typ);
                    self.stack_var(arg.name.clone(), typ);
                }
                for constraint in function.declaration.type_variables.iter() {
                    let c = Type(constraint.name, Vec::new());
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
                self.subs.instantiate(&**return_type)
            }
            _ => {
                let e = ast::located(function.expression.location, StringError("Non function type for function"));
                self.errors.error(e);
                return
            }                
        };
        let inferred_return_type = match self.typecheck(body) {
            Ok(typ) => typ,
            Err(err) => {
                self.errors.error(ast::Located { location: function.expression.location, value: err });
                return;
            }
        };
        match self.merge(return_type, inferred_return_type) {
            Ok(_) => self.replace_vars(body),
            Err(err) => {
                debug!("End {} ==> {:?}", function.declaration.name.id(), err);
                self.errors.error(ast::Located { location: function.expression.location, value: err });
            }
        }
    }

    fn replace_vars(&mut self, expr: &mut ast::LExpr<TcIdent>) {
        //Replace all type variables with their inferred types
        struct ReplaceVisitor<'a, 'b:'a> { tc: &'a mut Typecheck<'b> }
        impl <'a, 'b> MutVisitor for ReplaceVisitor<'a, 'b> {
            type T = TcIdent;
            fn visit_expr(&mut self, e: &mut ast::LExpr<TcIdent>) {
                match e.value {
                    ast::Identifier(ref mut id) => self.tc.set_type(&mut id.typ),
                    ast::FieldAccess(_, ref mut id) => self.tc.set_type(&mut id.typ),
                    ast::Array(ref mut array) => self.tc.set_type(&mut array.id.typ),
                    ast::Lambda(ref mut lambda) => self.tc.set_type(&mut lambda.id.typ),
                    ast::Match(_, ref mut alts) => {
                        for alt in alts.iter_mut() {
                            match alt.pattern {
                                ast::ConstructorPattern(ref mut id, ref mut args) => {
                                    self.tc.set_type(&mut id.typ);
                                    for arg in args.iter_mut() {
                                        self.tc.set_type(&mut arg.typ);
                                    }
                                }
                                ast::IdentifierPattern(ref mut id) => self.tc.set_type(&mut id.typ)
                            }
                        }
                    }
                    _ => ()
                }
                ast::walk_mut_expr(self, e);
            }
        }
        let mut v = ReplaceVisitor { tc: self };
        v.visit_expr(expr);
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
            self.replace_vars(expr);
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
            ast::Identifier(ref mut id) => {
                id.typ = try!(self.find(id.id()));
                Ok(id.typ.clone())
            }
            ast::Literal(ref lit) => {
                Ok(match *lit {
                    ast::Integer(_) => INT_TYPE.clone(),
                    ast::Float(_) => FLOAT_TYPE.clone(),
                    ast::String(_) => STRING_TYPE.clone(),
                    ast::Bool(_) => BOOL_TYPE.clone()
                })
            }
            ast::Call(ref mut func, ref mut args) => {
                let func_type = try!(self.typecheck(&mut**func));
                match func_type {
                    FunctionType(arg_types, return_type) => {
                        if arg_types.len() != args.len() {
                            return Err(WrongNumberOfArguments(arg_types.len(), args.len()));
                        }
                        for i in range(0, arg_types.len()) {
                            let actual = try!(self.typecheck(&mut args[i]));
                            try!(self.unify(&arg_types[i], actual));
                        }
                        Ok(*return_type)
                    }
                    t => Err(NotAFunction(t))
                }
            }
            ast::IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
                let pred_type = try!(self.typecheck(&mut**pred));
                try!(self.unify(&BOOL_TYPE, pred_type));
                let true_type = try!(self.typecheck(&mut**if_true));
                let false_type = match *if_false {
                    Some(ref mut if_false) => try!(self.typecheck(&mut**if_false)),
                    None => UNIT_TYPE.clone()
                };
                self.unify(&true_type, false_type)
            }
            ast::While(ref mut pred, ref mut expr) => {
                let pred_type = try!(self.typecheck(&mut **pred));
                try!(self.unify(&BOOL_TYPE, pred_type));
                self.typecheck(&mut**expr)
                    .map(|_| UNIT_TYPE.clone())
            }
            ast::BinOp(ref mut lhs, ref mut op, ref mut rhs) => {
                let lhs_type = try!(self.typecheck(&mut**lhs));
                let rhs_type = try!(self.typecheck(&mut**rhs));
                try!(self.unify(&lhs_type, rhs_type.clone()));
                match op.as_slice() {
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
            ast::Block(ref mut exprs) => {
                self.stack.enter_scope();
                let mut typ = BuiltinType(ast::UnitType);
                for expr in exprs.iter_mut() {
                    typ = try!(self.typecheck(expr));
                }
                self.stack.exit_scope();
                Ok(typ)
            }
            ast::Match(ref mut expr, ref mut alts) => {
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
            ast::Let(ref mut id, ref mut expr) => {
                let typ = try!(self.typecheck(&mut **expr));
                self.stack_var(id.name.clone(), typ);
                Ok(UNIT_TYPE.clone())
            }
            ast::Assign(ref mut lhs, ref mut rhs) => {
                let rhs_type = try!(self.typecheck(&mut **rhs));
                let lhs_type = try!(self.typecheck(&mut **lhs));
                try!(self.unify(&lhs_type, rhs_type));
                Ok(UNIT_TYPE.clone())
            }
            ast::FieldAccess(ref mut expr, ref mut id) => {
                let typ = try!(self.typecheck(&mut **expr));
                match typ {
                    Type(ref struct_id, _) => {
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
                    FunctionType(..) => Err(StringError("Field access on function")),
                    BuiltinType(..) => Err(StringError("Field acces on primitive")),
                    TypeVariable(..) => Err(StringError("Field acces on type variable")),
                    Generic(..) => Err(StringError("Field acces on generic")),
                    ArrayType(..) => Err(StringError("Field access on array")),
                    TraitType(..) => Err(StringError("Field access on trait object"))
                }
            }
            ast::Array(ref mut a) => {
                let mut expected_type = self.subs.new_var();
                for expr in a.expressions.iter_mut() {
                    let typ = try!(self.typecheck(expr));
                    expected_type = try!(self.unify(&expected_type, typ));
                }
                a.id.typ = ArrayType(box expected_type);
                Ok(a.id.typ.clone())
            }
            ast::ArrayAccess(ref mut array, ref mut index) => {
                let array_type = try!(self.typecheck(&mut **array));
                let var = self.subs.new_var();
                let array_type = try!(self.unify(&ArrayType(box var), array_type));
                let typ = match array_type {
                    ArrayType(typ) => *typ,
                    typ => return Err(IndexError(typ))
                };
                let index_type = try!(self.typecheck(&mut **index));
                try!(self.unify(&INT_TYPE, index_type));
                Ok(typ)
            }
            ast::Lambda(ref mut lambda) => {
                self.stack.enter_scope();
                let mut arg_types = Vec::new();
                for arg in lambda.arguments.iter_mut() {
                    arg.typ = self.subs.new_var();
                    arg_types.push(arg.typ.clone());
                    self.stack_var(arg.name.clone(), arg.typ.clone());
                }
                let body_type = try!(self.typecheck(&mut *lambda.body));
                self.stack.exit_scope();
                lambda.id.typ = FunctionType(arg_types, box body_type);
                Ok(lambda.id.typ.clone())
            }
        }
    }

    fn typecheck_pattern(&mut self, pattern: &mut ast::Pattern<TcIdent>, match_type: TcType) -> Result<(), TypeError> {
        let typename = match match_type {
            Type(id, _) => id,
            _ => return Err(StringError("Pattern matching only works on enums"))
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
                    FunctionType(argument_types, return_type) => {
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
            (&TypeVariable(ref l), _) => {
                if self.check_constraints(*l, actual) {
                    self.subs.union(*l, actual);
                    true
                }
                else {
                    false
                }
            }
            (_, &TypeVariable(ref r)) => {
                if self.check_constraints(*r, expected) {
                    self.subs.union(*r, expected);
                    true
                }
                else {
                    false
                }
            }
            (&FunctionType(ref l_args, ref l_ret), &FunctionType(ref r_args, ref r_ret)) => {
                if l_args.len() == r_args.len() {
                    l_args.iter().zip(r_args.iter()).all(|(l, r)| self.unify_(l, r)) && self.unify_(&**l_ret, &**r_ret)
                }
                else {
                    false
                }
            }
            (&ArrayType(ref l), &ArrayType(ref r)) => self.unify_(&**l, &**r),
            (&Type(ref l, _), _) if find_trait(&self.type_infos, l).is_ok() => {
                debug!("Found trait {:?} ", l);
                self.has_impl_of_trait(actual, l)
            }
            (&Type(ref l, ref l_args), &Type(ref r, ref r_args)) => {
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
            (_, &TypeVariable(ref r)) => {
                self.subs.union(*r, expected);
                true
            }
            (&FunctionType(ref l_args, ref l_ret), &FunctionType(ref r_args, ref r_ret)) => {
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
            (&ArrayType(ref l), &ArrayType(ref r)) => self.merge_(&**l, &**r),
            (&Type(ref l, _), _) if find_trait(&self.type_infos, l).is_ok() => {
                self.has_impl_of_trait(actual, l)
            }
            (&Type(ref l, ref l_args), &Type(ref r, ref r_args)) => {
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
            (_, &TypeVariable(_)) => {
                true
            }
            (&FunctionType(ref l_args, ref l_ret), &FunctionType(ref r_args, ref r_ret)) => {
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
            (&ArrayType(ref l), &ArrayType(ref r)) => self.merge_(&**l, &**r),
            (&Type(ref l, _), _) if find_trait(&self.type_infos, l).is_ok() => {
                self.has_impl_of_trait(actual, l)
            }
            (&Type(ref l, ref l_args), &Type(ref r, ref r_args)) => {
                l == r
                && l_args.len() == r_args.len()
                && l_args.iter().zip(r_args.iter()).all(|(l, r)| self.check_impl(constraints, l, r))
            }
            (&Generic(id), _) => {
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
            Type(ref id, _) if id == trait_id => return true,
            _ => ()
        }
        match self.type_infos.impls.get(trait_id) {
            Some(impls) => {
                for impl_type in impls.iter() {
                    if self.check_impl(impl_type.constraints.as_slice(), &impl_type.value, typ) {
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
            TypeVariable(_) => return true,
            _ => ()
        }
        match self.subs.constraints.get(&variable) {
            Some(trait_types) => {
                trait_types.iter()
                    .all(|trait_type| {
                        match *trait_type {
                            Type(ref id, _) => self.has_impl_of_trait(typ, id),
                            _ => false
                        }
                    })
            }
            None => true
        }
    }

    fn set_type(&self, t: &mut TcType) {
        let replacement = match *t {
            TypeVariable(id) => self.subs.find(id)
                .map(|t| match *t {
                    Type(ref id, ref args) if find_trait(&self.type_infos, id).is_ok() => {
                        TraitType(id.clone(), args.clone())
                    }
                    _ => {
                        let mut t = t.clone();
                        self.set_type(&mut t);
                        t
                    }
                }),
            FunctionType(ref mut args, ref mut return_type) => {
                for arg in args.iter_mut() {
                    self.set_type(arg);
                }
                self.set_type(&mut **return_type);
                None
            }
            Type(ref id, ref mut args) => {
                for arg in args.iter_mut() {
                    self.set_type(arg);
                }
                if find_trait(&self.type_infos, id).is_ok() {
                    let a = ::std::mem::replace(args, Vec::new());
                    Some(TraitType(*id, a))
                }
                else {
                    None
                }
            }
            ArrayType(ref mut typ) => { self.set_type(&mut **typ); None }
            _ => None
        };
        match replacement {
            Some(x) => *t = x,
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
        Substitution { map: HashMap::new(), constraints: HashMap::new(), variables: HashMap::new(), var_id: 0 }
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
        self.constraints = HashMap::new();//TODO Check if there is a bug in hashmap when calling clear
        self.variables.clear();
        self.var_id = 0;
    }

    fn union(&self, id: u32, typ: &TcType) {
        {
            let id_type = self.find(id);
            let other_type = self.real_type(typ);
            if id_type.map(|x| x == other_type).unwrap_or(&TypeVariable(id) == other_type) {
                return
            }
        }
        let this: &mut Substitution = unsafe { ::std::mem::transmute(self) };
        //Always make sure the mapping is from a higher variable to a lower
        //This way the resulting variables are always equal to any variables in the functions
        //declaration
        match *typ {
            TypeVariable(other_id) if id < other_id => this.assign_union(other_id, TypeVariable(id)),
            _ => this.assign_union(id, typ.clone())
        }
    }
    fn assign_union(&mut self, id: u32, typ: TcType) {
        match self.constraints.remove(&id) {
            Some(constraints) => {
                match typ {
                    TypeVariable(other_id) => {
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
            TypeVariable(var) => match self.find(var) {
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
        let this: &mut Substitution = unsafe { ::std::mem::transmute(&*self) };
        this.map.get_mut(&var).map(|typ| {
            match **typ {
                TypeVariable(parent_var) if parent_var != var => {
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
        TypeVariable(self.var_id)
    }

    fn instantiate_constrained(&mut self, constraints: &[ast::Constraint], typ: &TcType) -> TcType {
        self.var_id += 1;
        let mut map = HashMap::new();
        let base = self.var_id;
        for constraint in constraints.iter() {
            let c = Type(constraint.name, Vec::new());
            let next = base + map.len() as u32;
            match map.entry(constraint.type_variable) {
                Entry::Vacant(entry) => {
                    entry.insert(next);
                    debug!("aaaaaaa {} ---- {:?}", next, c);
                    self.constraints.insert(next, vec![c]);
                    self.var_id = ::std::cmp::max(next, self.var_id);
                }
                Entry::Occupied(entry) => {
                    self.constraints[*entry.get()].push(c);
                }
            }
        }
        self.instantiate_(base, typ, &mut map)
    }
    fn instantiate(&mut self, typ: &TcType) -> TcType {
        self.var_id += 1;
        let base = self.var_id;
        let mut map = HashMap::new();
        self.instantiate_(base, typ, &mut map)
    }
    fn instantiate_(&mut self, base: u32, typ: &TcType, vars: &mut HashMap<InternedStr, u32>) -> TcType {
        match *typ {
            Generic(x) => {
                let offset = vars.len() as u32;
                let var = match vars.entry(x) {
                    Entry::Vacant(entry) => *entry.insert(base + offset),
                    Entry::Occupied(entry) => *entry.get()
                };
                self.var_id = ::std::cmp::max(var, self.var_id);
                debug!("bbbbbb {} {}", x, var);
                TypeVariable(var)
            }
            FunctionType(ref args, ref return_type) => {
                let args2 = args.iter().map(|a| self.instantiate_(base, a, vars)).collect();
                FunctionType(args2, box self.instantiate_(base, &**return_type, vars))
            }
            ArrayType(ref typ) => ArrayType(box self.instantiate_(base, &**typ, vars)),
            Type(ref id, ref args) => {
                let args2 = args.iter().map(|a| self.instantiate_(base, a, vars)).collect();
                Type(*id, args2)
            }
            TraitType(ref id, ref args) => {
                let args2 = args.iter().map(|a| self.instantiate_(base, a, vars)).collect();
                TraitType(*id, args2)
            }
            ref x => x.clone()
        }
    }
}

pub trait Typed {
    fn type_of(&self) -> &TcType;
}
impl Typed for TcIdent {
    fn type_of(&self) -> &TcType {
        &self.typ
    }
}
impl <Id: Typed + Str> Typed for ast::Expr<Id> {
    fn type_of(&self) -> &TcType {
        match *self {
            ast::Identifier(ref id) => id.type_of(),
            ast::Literal(ref lit) => {
                match *lit {
                    ast::Integer(_) => &INT_TYPE,
                    ast::Float(_) => &FLOAT_TYPE,
                    ast::String(_) => &STRING_TYPE,
                    ast::Bool(_) => &BOOL_TYPE
                }
            }
            ast::IfElse(_, ref arm, _) => arm.type_of(),
            ast::Block(ref exprs) => {
                match exprs.last() {
                    Some(last) => last.type_of(),
                    None => &UNIT_TYPE
                }
            }
            ast::BinOp(ref lhs, ref op, _) => {
                match op.as_slice() {
                    "+" | "-" | "*" => lhs.type_of(),
                    "<" | ">" | "<=" | ">=" | "==" | "!=" | "&&" | "||" => &BOOL_TYPE,
                    _ => panic!()
                }
            }
            ast::Let(..) | ast::While(..) | ast::Assign(..) => &UNIT_TYPE,
            ast::Call(ref func, _) => {
                match func.type_of() {
                    &FunctionType(_, ref return_type) => &**return_type,
                    x => panic!("{:?}", x)
                }
            }
            ast::Match(_, ref alts) => alts[0].expression.type_of(),
            ast::FieldAccess(_, ref id) => id.type_of(),
            ast::Array(ref a) => a.id.type_of(),
            ast::ArrayAccess(ref array, _) => match array.type_of() {
                &ArrayType(ref t) => &**t,
                t => panic!("Not an array type {:?}", t)
            },
            ast::Lambda(ref lambda) => lambda.id.type_of()
        }
    }
}

impl <T: Typed> Typed for ast::Function<T> {
    fn type_of(&self) -> &TcType {
        self.declaration.name.type_of()
    }
}

impl Typed for Option<Box<ast::Located<ast::Expr<TcIdent>>>> {
    fn type_of(&self) -> &TcType {
        match *self {
            Some(ref t) => t.type_of(),
            None => &UNIT_TYPE
        }
    }
}


#[cfg(test)]
mod tests {
    use super::{Typecheck, Typed, TcIdent, UNIT_TYPE, INT_TYPE, BOOL_TYPE, FLOAT_TYPE, Type, FunctionType};
    use ast;
    use parser::{Parser, ParseResult};
    use interner::tests::{get_local_interner, intern};

    pub fn parse<F, T>(s: &str, f: F) -> T
        where F: FnOnce(&mut Parser<TcIdent>) -> ParseResult<T> {
        use std::io::BufReader;
        let mut buffer = BufReader::new(s.as_bytes());
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();
        let &mut (ref mut interner, ref mut gc) = &mut *interner;
        let mut parser = Parser::new(interner, gc, &mut buffer, |s| TcIdent { typ: UNIT_TYPE.clone(), name: s });
        f(&mut parser)
            .unwrap_or_else(|err| panic!("{:?}", err))
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

higher_order : (Int, fn (Int) -> Float) -> Float;
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
adder : (Int) -> fn (Int) -> Int;
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
    transform(xs, \x -> []);
    transform(1, \x -> 1.0)
}
transform : (a, fn (a) -> b) -> b;
transform = \x f -> {
    f(x)
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| panic!("{:?}", err));
        match module.functions[0].expression.value {
            ast::Lambda(ref lambda) => {
                match lambda.body.value {
                    ast::Block(ref exprs) => {
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
        match module.functions[0].expression.value {
            ast::Lambda(ref lambda) => {
                match lambda.body.value {
                    ast::Block(ref exprs) => {
                        match exprs[0].value {
                            ast::IfElse(_, ref if_true, ref if_false) => {
                                assert_eq!(if_true.type_of(), if_false.type_of());
                                assert_eq!(if_false.type_of(), &Type(intern("Option"), vec![FLOAT_TYPE.clone()]));
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
impl <a:Eq> Eq for Option a {
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
        match module.functions[0].expression.value {
            ast::Lambda(ref lambda) => {
                match lambda.body.value {
                    ast::Block(ref exprs) => {
                        match exprs[0].value {
                            ast::Call(ref f, ref args) => {
                                let int_opt = Type(intern("Option"), vec![INT_TYPE.clone()]);
                                assert_eq!(f.type_of(), &(FunctionType(vec![int_opt.clone(), int_opt.clone()], box BOOL_TYPE.clone())));
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

impl <a:Eq> Eq for Option a {
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
}
