use std::collections::HashMap;
use std::fmt;
use scoped_map::ScopedMap;
use ast;
use ast::MutVisitor;
use interner::*;

pub use ast::{Type, FunctionType, TraitType, TypeVariable, BuiltinType, Generic, ArrayType};


pub static int_type_tc: TcType = BuiltinType(ast::IntType);
pub static float_type_tc: TcType = BuiltinType(ast::FloatType);
pub static string_type_tc: TcType = BuiltinType(ast::StringType);
pub static bool_type_tc: TcType = BuiltinType(ast::BoolType);
pub static unit_type_tc: TcType = BuiltinType(ast::UnitType);


#[deriving(Clone, Eq, PartialEq, Show)]
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

pub type TcType = ast::Type<InternedStr>;

pub fn match_types(l: &TcType, r: &TcType) -> bool {
    fn type_eq<'a>(vars: &mut HashMap<uint, &'a TcType>, l: &'a TcType, r: &'a TcType) -> bool {
        match (l, r) {
            (&TypeVariable(l), _) => var_eq(vars, l, r),
            (&Generic(l), _) => var_eq(vars, l, r),
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
            (&BuiltinType(l), &BuiltinType(r)) => l == r,
            _ => false
        }
    }

    fn var_eq<'a>(mapping: &mut HashMap<uint, &'a TcType>, l: uint, r: &'a TcType) -> bool {
        match mapping.find(&l) {
            Some(x) => return *x == r,
            None => ()
        }
        mapping.insert(l, r);
        true
    }

    let mut vars = HashMap::new();
    type_eq(&mut vars, l, r)
}


impl fmt::Show for TcType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fn fmt_type(f: &mut fmt::Formatter, t: &InternedStr, args: &[TcType]) -> fmt::Result {
            try!(write!(f, "{}", t));
            if args.len() != 0 {
                try!(write!(f, "<"));
                let mut args_iter = args.iter();
                try!(write!(f, "{}", args_iter.next().unwrap()));
                for arg in args_iter {
                    try!(write!(f, ", {}", arg));
                }
                try!(write!(f, ">"));
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
            Generic(x) => write!(f, "#{}", x),
            FunctionType(ref args, ref return_type) => write!(f, "fn {} -> {}", args, return_type),
            BuiltinType(t) => t.fmt(f),
            ArrayType(ref t) => write!(f, "[{}]", t)
        }
    }
}

#[deriving(Show)]
pub struct Constrained<T> {
    pub constraints: Vec<ast::Constraints>,
    pub value: T
}

fn from_impl_type(constraints: &[ast::Constraints], decl: &mut ast::FunctionDeclaration<TcIdent>) -> Constrained<TcType> {
    //Add all constraints from the impl declaration to the functions declaration
    for constraint in constraints.iter() {
        let exists = {
            let x = decl.type_variables.mut_iter()
                .find(|func_constraint| func_constraint.type_variable == constraint.type_variable);
            match x {
                Some(c) => {
                    for trait_type in constraint.constraints.iter() {
                        if c.constraints.iter().find(|t| *t == trait_type).is_none() {
                            c.constraints.push(trait_type.clone());
                        }
                    }
                    true
                }
                None => false
            }
        };
        if !exists {
            decl.type_variables.push(constraint.clone());
        }
    }
    from_declaration(decl)
}

fn from_declaration(decl: &ast::FunctionDeclaration<TcIdent>) -> Constrained<TcType> {
    let variables = decl.type_variables.as_slice();
    let args = decl.arguments.iter()
        .map(|f| from_generic_type(variables, &f.typ))
        .collect();
    let constraints = variables.iter()
        .map(|constraints| {
            let cs = constraints.constraints.iter()
                .map(|typ| from_generic_type(variables, typ))
                .collect();
            ast::Constraints { type_variable: constraints.type_variable, constraints: cs }
        }
        ).collect();
    Constrained {
        constraints: constraints,
        value: FunctionType(args, box from_generic_type(variables, &decl.return_type))
    }
}

pub fn from_generic_type(variables: &[ast::Constraints], typ: &ast::VMType) -> TcType {
    match *typ {
        ast::Type(ref id, ref args) => {
            match variables.iter().enumerate().find(|v| v.ref1().type_variable == *id).map(|v| v.val0()) {
                Some(index) => {//TODO type parameters
                    Generic(index)
                }
                None => {
                    let args2 = args.iter().map(|a| from_generic_type(variables, a)).collect();
                    Type(*id, args2)
                }
            }
        }
        ast::FunctionType(ref args, ref return_type) => {
            let args2 = args.iter().map(|a| from_generic_type(variables, a)).collect();
            FunctionType(args2, box from_generic_type(variables, &**return_type))
        }
        ast::BuiltinType(ref id) => BuiltinType(*id),
        ast::ArrayType(ref typ) => ArrayType(box from_generic_type(variables, &**typ)),
        ast::TraitType(ref id, ref args) => {
            let args2 = args.iter().map(|a| from_generic_type(variables, a)).collect();
            Type(*id, args2)
        }
        ast::TypeVariable(id) => TypeVariable(id),
        ast::Generic(id) => Generic(id),
    }
}

#[deriving(Show)]
enum TypeError {
    UndefinedVariable(InternedStr),
    NotAFunction(TcType),
    WrongNumberOfArguments(uint, uint),
    TypeMismatch(TcType, TcType),
    UndefinedStruct(InternedStr),
    UndefinedField(InternedStr, InternedStr),
    UndefinedTrait(InternedStr),
    IndexError(TcType),
    TypeError(&'static str)
}

pub type TcResult = Result<TcType, TypeError>;


pub enum TypeInfo<'a> {
    Struct(&'a [(InternedStr, TcType)]),
    Enum(&'a [ast::Constructor<TcIdent>])
}

pub struct TypeInfos {
    pub structs: HashMap<InternedStr, Vec<(InternedStr, TcType)>>,
    pub enums: HashMap<InternedStr, Vec<ast::Constructor<TcIdent>>>,
    impls: HashMap<InternedStr, Vec<(Vec<Vec<TcType>>, TcType)>>,
    traits: HashMap<InternedStr, Vec<(InternedStr, TcType)>>
}

impl TypeInfos {
    pub fn new() -> TypeInfos {
        TypeInfos {
            structs: HashMap::new(),
            enums: HashMap::new(),
            traits: HashMap::new(),
            impls: HashMap::new()
        }
    }
    pub fn find_type_info(&self, id: &InternedStr) -> Option<TypeInfo> {
        self.structs.find(id)
            .map(|s| Struct(s.as_slice()))
            .or_else(|| self.enums.find(id).map(|e| Enum(e.as_slice())))
    }
    pub fn find_trait(&self, name: &InternedStr) -> Option<&[(InternedStr, TcType)]> {
        self.traits.find(name).map(|v| v.as_slice())
    }
    pub fn add_module(&mut self, module: &ast::Module<TcIdent>) {
        for s in module.structs.iter() {
            let fields = s.fields.iter()
                .map(|field| (field.name, from_generic_type(s.type_variables.as_slice(), &field.typ)))
                .collect();
            self.structs.insert(s.name.name, fields);
        }
        for e in module.enums.iter() {
            self.enums.insert(e.name.name, e.constructors.clone());
        }
        for t in module.traits.iter() {
            let function_types = t.declarations.iter().map(|f| {
                (f.name.id().clone(), f.name.typ.clone())
            }).collect();
            self.traits.insert(t.name.id().clone(), function_types);
        }
        for imp in module.impls.iter() {
            let imp_type = from_generic_type(imp.type_variables.as_slice(), &imp.typ);
            let set = self.impls.find_or_insert(imp.trait_name.id().clone(), Vec::new());
            let constraints = imp.type_variables.iter()
                .map(|constraints| constraints.constraints.iter()
                    .map(|typ| from_generic_type(imp.type_variables.as_slice(), typ))
                    .collect())
                .collect();
            set.push((constraints, imp_type));
        }
    }
}
fn find_trait<'a>(this: &'a TypeInfos, name: &InternedStr) -> Result<&'a [(InternedStr, TcType)], TypeError> {
    this.find_trait(name)
        .map(Ok)
        .unwrap_or_else(|| Err(UndefinedTrait(name.clone())))
}

pub trait TypeEnv {
    fn find_type(&self, id: &InternedStr) -> Option<&Constrained<TcType>>;
    fn find_type_info(&self, id: &InternedStr) -> Option<TypeInfo>;
}

pub struct Typecheck<'a> {
    environment: Option<&'a TypeEnv>,
    pub type_infos: TypeInfos,
    module: HashMap<InternedStr, Constrained<TcType>>,
    stack: ScopedMap<InternedStr, TcType>,
    subs: Substitution,
    errors: Errors<ast::Located<TypeError>>
}

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

impl <T: fmt::Show> fmt::Show for Errors<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for error in self.errors.iter() {
            try!(write!(f, "{}\n", error));
        }
        Ok(())
    }
}

pub type TypeErrors = Errors<ast::Located<TypeError>>;

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
        let t: Option<(&[ast::Constraints], &TcType)> = {
            let stack = &self.stack;
            let module = &self.module;
            let environment = &self.environment;
            match stack.find(id).map(|typ| (&[], typ)) {
                Some(x) => Some(x),
                None => module.find(id)
                    .or_else(|| environment.and_then(|e| e.find_type(id)))
                    .map(|c| (c.constraints.as_slice(), &c.value))
            }
        };
        debug!("Find {} : {}", id, t);
        match t {
            Some(t) => Ok(self.subs.instantiate_constrained(t.val0(), t.val1())),
            None => Err(UndefinedVariable(id.clone()))
        }
    }

    fn find_type_info(&self, id: &InternedStr) -> Result<TypeInfo, TypeError> {
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

    pub fn typecheck_module(&mut self, module: &mut ast::Module<TcIdent>) -> Result<(), TypeErrors> {
        
        for f in module.functions.mut_iter() {
            let decl = &mut f.declaration;
            let constrained_type = from_declaration(decl);
            decl.name.typ = constrained_type.value.clone();
            self.module.insert(decl.name.name, constrained_type);
        }
        for t in module.traits.mut_iter() {
            for func in t.declarations.mut_iter() {
                let args = func.arguments.iter()
                    .map(|f| self.subs.from_trait_function_type(&f.typ))
                    .collect();
                func.name.typ = FunctionType(args, box self.subs.from_trait_function_type(&func.return_type));
                self.module.insert(func.name.id().clone(), Constrained {
                    constraints: vec![ast::Constraints {
                        type_variable: func.name.id().clone(),//TODO
                        constraints: vec![Type(t.name.name, Vec::new())]
                    }],//Self, ie Generic(0) should have the trait itself as a constraint
                    value: func.name.typ.clone()
                });
            }
        }
        for s in module.structs.mut_iter() {
            let args = s.fields.iter()
                .map(|f| from_generic_type(s.type_variables.as_slice(), &f.typ))
                .collect();
            let variables = range(0, s.type_variables.len())
                .map(|i| Generic(i))
                .collect();
            s.name.typ = FunctionType(args, box Type(s.name.name, variables));
            self.module.insert(s.name.name, Constrained {
                constraints: Vec::new(),
                value: s.name.typ.clone()
            });
        }
        for e in module.enums.mut_iter() {
            let type_variables = e.type_variables.as_slice();
            for ctor in e.constructors.mut_iter() {
                let args = ctor.arguments.iter()
                    .map(|t| from_generic_type(type_variables, t))
                    .collect();
                let variables = range(0, e.type_variables.len())
                    .map(|i| Generic(i))
                    .collect();
                ctor.name.typ = FunctionType(args, box Type(e.name.name, variables));
                self.module.insert(ctor.name.name, Constrained {
                    constraints: Vec::new(),
                    value: ctor.name.typ.clone()
                });
            }
        }
        self.type_infos.add_module(module);
        for f in module.functions.mut_iter() {
            self.typecheck_function(f)
        }
        for imp in module.impls.mut_iter() {
            imp.typ = from_generic_type(imp.type_variables.as_slice(), &imp.typ);
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
            for func in imp.functions.mut_iter() {
                let c_type = from_impl_type(type_variables, &mut func.declaration);
                func.declaration.name.typ = c_type.value;
                let trait_function_type = try!(trait_functions.iter()
                    .find(|& &(ref name, _)| name == func.declaration.name.id())
                    .map(Ok)
                    .unwrap_or_else(|| Err(TypeError("Function does not exist in trait"))));
                let tf = self.subs.instantiate(trait_function_type.ref1());
                try!(self.unify(&tf, func.type_of().clone()));
            }
        }
        for f in imp.functions.mut_iter() {
            self.typecheck_function(f);
        }
        Ok(())
    }

    
    fn typecheck_function(&mut self, function: &mut ast::Function<TcIdent>) {
        debug!("Typecheck function {}", function.declaration.name.id());
        self.stack.clear();
        self.subs.clear();
        let return_type = match function.declaration.name.typ {
            FunctionType(ref arg_types, ref return_type) => {
                self.subs.var_id += 1;
                let base = self.subs.var_id;
                for (typ, arg) in arg_types.iter().zip(function.declaration.arguments.iter()) {
                    let typ = self.subs.instantiate_(base, typ);
                    debug!("{} {}", arg.name, typ);
                    self.stack_var(arg.name.clone(), typ);
                }
                let vars = function.declaration.type_variables.as_slice();
                for (i, constraint) in function.declaration.type_variables.iter().enumerate() {
                    let var_id = base + i;
                    let types = constraint.constraints.iter()
                        .map(|typ| from_generic_type(vars, typ))
                        .collect();
                    self.subs.constraints.insert(var_id, types);
                }
                self.subs.instantiate(&**return_type)
            }
            _ => fail!("Non function type for function")
        };
        let inferred_return_type = match self.typecheck(&mut function.expression) {
            Ok(typ) => typ,
            Err(err) => {
                self.errors.error(ast::Located { location: function.expression.location, value: err });
                return;
            }
        };
        match self.merge(return_type, inferred_return_type) {
            Ok(_) => self.replace_vars(&mut function.expression),
            Err(err) => {
                debug!("End {} ==> {}", function.declaration.name.id(), err);
                self.errors.error(ast::Located { location: function.expression.location, value: err });
            }
        }
    }

    fn replace_vars(&mut self, expr: &mut ast::LExpr<TcIdent>) {
        //Replace all type variables with their inferred types
        struct ReplaceVisitor<'a, 'b> { tc: &'a mut Typecheck<'b> }
        impl <'a, 'b> MutVisitor<TcIdent> for ReplaceVisitor<'a, 'b> {
            fn visit_expr(&mut self, e: &mut ast::LExpr<TcIdent>) {
                match e.value {
                    ast::Identifier(ref mut id) => self.tc.set_type(&mut id.typ),
                    ast::FieldAccess(_, ref mut id) => self.tc.set_type(&mut id.typ),
                    ast::Array(ref mut array) => self.tc.set_type(&mut array.id.typ),
                    ast::Lambda(ref mut lambda) => self.tc.set_type(&mut lambda.id.typ),
                    ast::Match(_, ref mut alts) => {
                        for alt in alts.mut_iter() {
                            match alt.pattern {
                                ast::ConstructorPattern(ref mut id, ref mut args) => {
                                    self.tc.set_type(&mut id.typ);
                                    for arg in args.mut_iter() {
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

    pub fn typecheck_expr(&mut self, expr: &mut ast::LExpr<TcIdent>) -> Result<TcType, TypeErrors> {
        let typ = match self.typecheck(expr) {
            Ok(typ) => typ,
            Err(err) => {
                self.errors.error(ast::Located { location: expr.location, value: err });
                return Err(::std::mem::replace(&mut self.errors, Errors::new()))
            }
        };
        self.replace_vars(expr);
        Ok(typ)
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
                    ast::Integer(_) => int_type_tc.clone(),
                    ast::Float(_) => float_type_tc.clone(),
                    ast::String(_) => string_type_tc.clone(),
                    ast::Bool(_) => bool_type_tc.clone()
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
                            let actual = try!(self.typecheck(args.get_mut(i)));
                            try!(self.unify(&arg_types[i], actual));
                        }
                        Ok(*return_type)
                    }
                    t => Err(NotAFunction(t))
                }
            }
            ast::IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
                let pred_type = try!(self.typecheck(&mut**pred));
                try!(self.unify(&bool_type_tc, pred_type));
                let true_type = try!(self.typecheck(&mut**if_true));
                let false_type = try!(self.typecheck(&mut**if_false));
                self.unify(&true_type, false_type)
            }
            ast::While(ref mut pred, ref mut expr) => {
                let pred_type = try!(self.typecheck(&mut **pred));
                try!(self.unify(&bool_type_tc, pred_type));
                self.typecheck(&mut**expr)
                    .map(|_| unit_type_tc.clone())
            }
            ast::BinOp(ref mut lhs, ref mut op, ref mut rhs) => {
                let lhs_type = try!(self.typecheck(&mut**lhs));
                let rhs_type = try!(self.typecheck(&mut**rhs));
                try!(self.unify(&lhs_type, rhs_type.clone()));
                match op.as_slice() {
                    "+" | "-" | "*" => {
                        let b = {
                            let lt = self.subs.real_type(&lhs_type);
                            *lt == int_type_tc || *lt == float_type_tc
                        };
                        if b {
                            Ok(lhs_type)
                        }
                        else {
                            return Err(TypeError("Expected numbers in binop"))
                        }
                    }
                    "=="| "!=" | "<" | ">" | "<=" | ">="  => Ok(bool_type_tc.clone()),
                    _ => Err(UndefinedVariable(op.name.clone()))
                }
            }
            ast::Block(ref mut exprs) => {
                self.stack.enter_scope();
                let mut typ = BuiltinType(ast::UnitType);
                for expr in exprs.mut_iter() {
                    typ = try!(self.typecheck(expr));
                }
                self.stack.exit_scope();
                Ok(typ)
            }
            ast::Match(ref mut expr, ref mut alts) => {
                let typ = try!(self.typecheck(&mut**expr));
                self.stack.enter_scope();
                try!(self.typecheck_pattern(&mut alts.get_mut(0).pattern, typ.clone()));
                let alt1_type = try!(self.typecheck(&mut alts.get_mut(0).expression));
                self.stack.exit_scope();

                for alt in alts.mut_iter().skip(1) {
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
                Ok(unit_type_tc.clone())
            }
            ast::Assign(ref mut lhs, ref mut rhs) => {
                let rhs_type = try!(self.typecheck(&mut **rhs));
                let lhs_type = try!(self.typecheck(&mut **lhs));
                self.unify(&lhs_type, rhs_type)
            }
            ast::FieldAccess(ref mut expr, ref mut id) => {
                let typ = try!(self.typecheck(&mut **expr));
                match typ {
                    Type(ref struct_id, _) => {
                        let type_info = try!(self.find_type_info(struct_id));
                        match type_info {
                            Struct(ref fields) => {
                                id.typ = try!(fields.iter()
                                    .find(|& &(name, _)| name == id.name)
                                    .map(|&(_, ref typ)| Ok(typ.clone()))
                                    .unwrap_or_else(|| Err(UndefinedField(struct_id.clone(), id.name.clone()))));
                                Ok(id.typ.clone())
                            }
                            Enum(_) => Err(TypeError("Field access on enum type"))
                        }
                    }
                    FunctionType(..) => Err(TypeError("Field access on function")),
                    BuiltinType(..) => Err(TypeError("Field acces on primitive")),
                    TypeVariable(..) => Err(TypeError("Field acces on type variable")),
                    Generic(..) => Err(TypeError("Field acces on generic")),
                    ArrayType(..) => Err(TypeError("Field access on array")),
                    TraitType(..) => Err(TypeError("Field access on trait object"))
                }
            }
            ast::Array(ref mut a) => {
                let mut expected_type = self.subs.new_var();
                for expr in a.expressions.mut_iter() {
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
                try!(self.unify(&int_type_tc, index_type));
                Ok(typ)
            }
            ast::Lambda(ref mut lambda) => {
                self.stack.enter_scope();
                let mut arg_types = Vec::new();
                for arg in lambda.arguments.mut_iter() {
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
            _ => return Err(TypeError("Pattern matching only works on enums"))
        };
        match *pattern {
            ast::ConstructorPattern(ref name, ref mut args) => {
                //Find the enum constructor and return the types for its arguments
                let ctor_type = match try!(self.find_type_info(&typename)) {
                    Enum(ref ctors) => {
                        match ctors.iter().find(|ctor| ctor.name.id() == name.id()) {
                            Some(ctor) => ctor.name.typ.clone(),
                            None => return Err(TypeError("Undefined constructor"))
                        }
                    }
                    Struct(..) => return Err(TypeError("Pattern match on struct"))
                };
                let ctor_type = self.subs.instantiate(&ctor_type);
                let (argument_types, return_type) = match ctor_type {
                    FunctionType(argument_types, return_type) => {
                        (argument_types, *return_type)
                    }
                    _ => return Err(TypeError("Enum constructor must be a function type"))
                };
                try!(self.unify(&match_type, return_type));
                for (arg, typ) in args.iter().zip(argument_types.move_iter()) {
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
        debug!("Unify {} <=> {}", expected, actual);
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
        debug!("{} <=> {}", expected, actual);
        match (expected, actual) {
            (&TypeVariable(ref l), _) => {
                if self.check_constraints(l, actual) {
                    self.subs.union(*l, actual);
                    true
                }
                else {
                    false
                }
            }
            (_, &TypeVariable(ref r)) => {
                if self.check_constraints(r, expected) {
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
                debug!("Found trait {} ", l);
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
        debug!("Merge {} {}", expected, actual);
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
    fn check_impl(&self, constraints: &[Vec<TcType>], expected: &TcType, actual: &TcType) -> bool {
        let expected = self.subs.real_type(expected);
        let actual = self.subs.real_type(actual);
        debug!("Merge {} {}", expected, actual);
        match (expected, actual) {
            (_, &TypeVariable(ref r)) => {
                self.subs.union(*r, expected);
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
            (&Generic(index), _) => {
                if index < constraints.len() {
                    constraints[index].iter()
                        .all(|constraint_type| {
                            match *constraint_type {
                                Type(ref trait_id, _) => self.has_impl_of_trait(actual, trait_id),
                                _ => false
                            }
                        })
                }
                else {
                    true
                }
            }
            _ => expected == actual
        }
    }
    fn has_impl_of_trait(&self, typ: &TcType, trait_id: &InternedStr) -> bool {
        debug!("Check impl {} {}", typ, trait_id);
        //If the type is the trait it self it passes the check
        match *typ {
            Type(ref id, _) if id == trait_id => return true,
            _ => ()
        }
        match self.type_infos.impls.find(trait_id) {
            Some(impls) => {
                for &(ref constraints, ref impl_type) in impls.iter() {
                    if self.check_impl(constraints.as_slice(), impl_type, typ) {
                        return true;
                    }
                }
                false
            }
            _ => true
        }
    }

    fn check_constraints(&self, variable: &uint, typ: &TcType) -> bool {
        debug!("Constraint check {} {} ==> {}", variable, self.subs.constraints.find(variable), typ);
        match *typ {
            TypeVariable(_) => return true,
            _ => ()
        }
        match self.subs.constraints.find(variable) {
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
                for arg in args.mut_iter() {
                    self.set_type(arg);
                }
                self.set_type(&mut **return_type);
                None
            }
            Type(id, ref mut args) => {
                for arg in args.mut_iter() {
                    self.set_type(arg);
                }
                if find_trait(&self.type_infos, &id).is_ok() {
                    let a = ::std::mem::replace(args, Vec::new());
                    Some(TraitType(id, a))
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
    map: HashMap<uint, Box<TcType>>,
    constraints: HashMap<uint, Vec<TcType>>,
    var_id: uint
}
impl Substitution {
    fn new() -> Substitution {
        Substitution { map: HashMap::new(), constraints: HashMap::new(), var_id: 0 }
    }

    fn clear(&mut self) {
        self.map.clear();
        self.constraints = HashMap::new();//TODO Check if there is a bug in hashmap when calling clear
        self.var_id = 0;
    }

    fn union(&self, id: uint, typ: &TcType) {
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
    fn assign_union(&mut self, id: uint, typ: TcType) {
        match self.constraints.pop(&id) {
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

    fn find(&self, var: uint) -> Option<&TcType> {
        //Use unsafe so that we can hold a reference into the map and continue
        //to look for parents
        //Since we never have a cycle in the map we will never hold a &mut
        //to the same place
        let this: &mut Substitution = unsafe { ::std::mem::transmute(&*self) };
        this.map.find_mut(&var).map(|typ| {
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

    fn instantiate_constrained(&mut self, constraints: &[ast::Constraints], typ: &TcType) -> TcType {
        self.var_id += 1;
        let base = self.var_id;
        for (i, constraint) in constraints.iter().enumerate() {
            self.constraints.insert(base + i, constraint.constraints.clone());
        }
        self.instantiate_(base, typ)
    }
    fn instantiate(&mut self, typ: &TcType) -> TcType {
        self.var_id += 1;
        let base = self.var_id;
        self.instantiate_(base, typ)
    }
    fn instantiate_(&mut self, base: uint, typ: &TcType) -> TcType {
        match *typ {
            Generic(x) => {
                self.var_id = ::std::cmp::max(base + x, self.var_id);
                TypeVariable(base + x)
            }
            FunctionType(ref args, ref return_type) => {
                let args2 = args.iter().map(|a| self.instantiate_(base, a)).collect();
                FunctionType(args2, box self.instantiate_(base, &**return_type))
            }
            ArrayType(ref typ) => ArrayType(box self.instantiate_(base, &**typ)),
            Type(id, ref args) => {
                let args2 = args.iter().map(|a| self.instantiate_(base, a)).collect();
                Type(id, args2)
            }
            TraitType(id, ref args) => {
                let args2 = args.iter().map(|a| self.instantiate_(base, a)).collect();
                TraitType(id, args2)
            }
            ref x => x.clone()
        }
    }

    fn from_trait_function_type(&mut self, typ: &ast::VMType) -> TcType {
        match *typ {
            ast::Type(ref id, _) if id.as_slice() == "Self" => Generic(0),
            ast::Type(ref id, ref args) => {
                let args2 = args.iter().map(|a| self.from_trait_function_type(a)).collect();
                Type(*id, args2)
            }
            ast::TraitType(ref id, ref args) => {
                let args2 = args.iter().map(|a| self.from_trait_function_type(a)).collect();
                Type(*id, args2)
            }
            ast::TypeVariable(id) => TypeVariable(id),
            ast::Generic(id) => Generic(id),
            ast::FunctionType(ref args, ref return_type) => {
                let args2 = args.iter().map(|a| self.from_trait_function_type(a)).collect();
                FunctionType(args2, box self.from_trait_function_type(&**return_type))
            }
            ast::BuiltinType(ref id) => BuiltinType(*id),
            ast::ArrayType(ref t) => ArrayType(box self.from_trait_function_type(&**t))
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
                    ast::Integer(_) => &int_type_tc,
                    ast::Float(_) => &float_type_tc,
                    ast::String(_) => &string_type_tc,
                    ast::Bool(_) => &bool_type_tc
                }
            }
            ast::IfElse(_, ref arm, _) => arm.type_of(),
            ast::Block(ref exprs) => {
                if exprs.len() == 0 {
                    &unit_type_tc
                }
                else {
                    exprs.last().unwrap().type_of()
                }
            }
            ast::BinOp(ref lhs, ref op, _) => {
                match op.as_slice() {
                    "+" | "-" | "*" => lhs.type_of(),
                    "<" | ">" | "<=" | ">=" => &bool_type_tc,
                    _ => fail!()
                }
            }
            ast::Let(..) | ast::While(..) | ast::Assign(..) => &unit_type_tc,
            ast::Call(ref func, _) => {
                match func.type_of() {
                    &FunctionType(_, ref return_type) => &**return_type,
                    x => fail!("{}", x)
                }
            }
            ast::Match(_, ref alts) => alts[0].expression.type_of(),
            ast::FieldAccess(_, ref id) => id.type_of(),
            ast::Array(ref a) => a.id.type_of(),
            ast::ArrayAccess(ref array, _) => match array.type_of() {
                &ArrayType(ref t) => &**t,
                t => fail!("Not an array type {}", t)
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


#[cfg(test)]
mod tests {
    use super::*;
    use ast;
    use parser::*;
    use interner::tests::{get_local_interner, intern};

    pub fn parse<T>(s: &str, f: |&mut Parser<TcIdent>|:'static -> ParseResult<T>) -> T {
        use std::io::BufReader;
        let mut buffer = BufReader::new(s.as_bytes());
        let interner = get_local_interner();
        let mut interner = interner.borrow_mut();
        let mut parser = Parser::new(&mut *interner, &mut buffer, |s| TcIdent { typ: unit_type_tc.clone(), name: s });
        f(&mut parser)
            .unwrap_or_else(|err| fail!(err))
    }
    #[test]
    fn while_() {
        let text = "fn main() { let x = 2; while x < 10 { x } }";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| fail!(err))

    }
    #[test]
    fn enums() {
        let text = 
r"
enum AB {
    A(int),
    B(float)
}
fn main() -> int {
    match A(1) {
        A(x) => { x }
        B(x) => { 0 }
    }
}";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| fail!("{}", err))

    }
    #[test]
    fn trait_function() {
        let text = 
r"
struct Vec {
    x: int,
    y: int
}

trait Add {
    fn add(l: Self, r: Self) -> Self;
}

impl Add for Vec {
    fn add(l: Vec, r: Vec) -> Vec {
        Vec(l.x + r.x, l.y + r.y)
    }
}

fn test(v: Vec) -> Vec {
    add(v, Vec(1, 1))
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| fail!("{}", err))

    }
    #[test]
    ///Check that implementations with its types wrong are not allowed
    fn traits_wrong_self() {
        let text = 
r"
struct Vec {
    x: int,
    y: int
}

trait Add {
    fn add(l: Self, r: Self) -> Self;
}

impl Add for Vec {
    fn add(l: Vec, r: Vec) -> int {
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
fn test(x: int) -> float {
    1.0
}

fn higher_order(x: int, f: fn (int) -> float) -> float {
    f(x)
}

fn test2() {
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
fn test(x: int) -> [int] {
    [1,2,x]
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| fail!("{}", err));
    }
    #[test]
    fn array_unify() {
        let text = 
r"
fn test() -> [int] {
    []
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| fail!("{}", err));
    }
    #[test]
    fn lambda() {
        let text = 
r"
fn main() -> int {
    let f = adder(2);
    f(3)
}
fn adder(x: int) -> fn (int) -> int {
    \y -> x + y
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| fail!("{}", err));
    }
    #[test]
    fn generic_function() {
        let text = 
r"
fn main() -> int {
    let x = 1;
    id(x)
}
fn id<T>(x: T) -> T {
    x
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| fail!("{}", err));
    }
    #[test]
    fn generic_function_map() {
        let text = 
r"
fn main() -> float {
    let xs = [1,2,3,4];
    transform(xs, \x -> []);
    transform(1, \x -> 1.0)
}
fn transform<A, B>(x: A, f: fn (A) -> B) -> B {
    f(x)
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| fail!("{}", err));
        match module.functions[0].expression.value {
            ::ast::Block(ref exprs) => {
                assert_eq!(exprs[2].value.type_of(), &float_type_tc);
            }
            _ => fail!()
        }
    }
    #[test]
    fn specialized_generic_function_error() {
        let text = 
r"
fn id<T>(x: T) -> T {
    2
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_err();
    }
    #[test]
    fn unify_parameterized_types() {
        let text = 
r"
enum Option<T> {
    Some(T),
    None()
}
fn is_positive(x: float) -> Option<float> {
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
            .unwrap_or_else(|err| fail!("{}", err));
        match module.functions[0].expression.value {
            ast::Block(ref exprs) => {
                match exprs[0].value {
                    ast::IfElse(_, ref if_true, ref if_false) => {
                        assert_eq!(if_true.type_of(), if_false.type_of());
                        assert_eq!(if_false.type_of(), &Type(intern("Option"), vec![float_type_tc.clone()]));
                    }
                    _ => fail!()
                }
            }
            _ => fail!()
        }
    }
    #[test]
    fn paramter_mismatch() {
        let text = 
r"
enum Option<T> {
    Some(T),
    None()
}
fn test(x: float) -> Option<int> {
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
            .unwrap_err();
    }


    #[test]
    fn typecheck_trait_for_generic_types() {
        let text = 
r"
trait Eq {
    fn eq(l: Self, r: Self) -> bool;
}
enum Option<T> {
    Some(T),
    None()
}
impl Eq for int {
    fn eq(l: int, r: int) -> bool {
        l == r
    }
}
impl <T:Eq> Eq for Option<T> {
    fn eq(l: Option<T>, r: Option<T>) -> bool {
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
fn test() -> bool {
    eq(Some(2), None())
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_or_else(|err| fail!("{}", err));
        match module.functions[0].expression.value {
            ast::Block(ref exprs) => {
                match exprs[0].value {
                    ast::Call(ref f, ref args) => {
                        let int_opt = Type(intern("Option"), vec![int_type_tc.clone()]);
                        assert_eq!(f.type_of(), &(FunctionType(vec![int_opt.clone(), int_opt.clone()], box bool_type_tc.clone())));
                        assert_eq!(args[0].type_of(), &int_opt);
                        assert_eq!(args[1].type_of(), &int_opt);
                    }
                    _ => fail!()
                }
            }
            _ => fail!()
        }
    }
    #[test]
    fn error_no_impl_for_parameter() {
        let text = 
r"
trait Eq {
    fn eq(l: Self, r: Self) -> bool;
}
enum Option<T> {
    Some(T),
    None()
}
impl <T:Eq> Eq for Option<T> {
    fn eq(l: Option<T>, r: Option<T>) -> bool {
        false
    }
}
fn test() -> bool {
    eq(Some(2), None())
}
";
        let mut module = parse(text, |p| p.module());
        let mut tc = Typecheck::new();
        tc.typecheck_module(&mut module)
            .unwrap_err();
    }
}
