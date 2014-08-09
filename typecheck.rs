use std::collections::HashMap;
use std::collections::HashSet;
use scoped_map::ScopedMap;
use ast::*;
use ast;
use interner::*;


pub static int_type_tc: TcType = BuiltinType(IntType);
pub static float_type_tc: TcType = BuiltinType(FloatType);
pub static string_type_tc: TcType = BuiltinType(StringType);
pub static bool_type_tc: TcType = BuiltinType(BoolType);
pub static unit_type_tc: TcType = BuiltinType(UnitType);


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

#[deriving(Clone, Eq, PartialEq, Hash, Show)]
pub enum TcType {
    Type(InternedStr),
    TypeVariable(uint),
    FunctionType(Vec<TcType>, Box<TcType>),
    BuiltinType(LiteralType)
}

fn from_vm_type(typ: &VMType) -> TcType {
    match *typ {
        ast::Type(ref id) => Type(*id),
        ast::FunctionType(ref args, ref return_type) => {
            let args2 = args.iter().map(|a| from_vm_type(a)).collect();
            FunctionType(args2, box from_vm_type(&**return_type))
        }
        ast::LiteralType(ref id) => BuiltinType(*id),
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
    TypeError(&'static str)
}

type TcResult = Result<TcType, TypeError>;


pub enum TypeInfo<'a> {
    Struct(&'a [Field]),
    Enum(&'a [Constructor<TcIdent>])
}

pub struct TypeInfos {
    pub structs: HashMap<InternedStr, Vec<Field>>,
    pub enums: HashMap<InternedStr, Vec<Constructor<TcIdent>>>,
    impls: HashMap<TcType, HashSet<TcType>>,
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
    pub fn has_impl_of_trait(&self, typ: &TcType, trait_id: &TcType) -> bool {
        self.impls.find(typ)
            .map(|set| set.contains(trait_id))
            .unwrap_or(false)
    }
    pub fn find_trait(&self, name: &InternedStr) -> Option<&[(InternedStr, TcType)]> {
        self.traits.find(name).map(|v| v.as_slice())
    }
    pub fn add_module(&mut self, module: &Module<TcIdent>) {
        for s in module.structs.iter() {
            let fields = s.fields.clone();
            self.structs.insert(s.name.name, fields);
        }
        for e in module.enums.iter() {
            self.enums.insert(e.name.name, e.constructors.clone());
        }
        for t in module.traits.iter() {
            let function_types = t.declarations.iter().map(|f| {
                let arg_types = f.arguments.iter().map(|f| from_vm_type(&f.typ)).collect();
                (f.name.id().clone(), FunctionType(arg_types, box from_vm_type(&f.return_type)))
            }).collect();
            self.traits.insert(t.name.id().clone(), function_types);
        }
        for imp in module.impls.iter() {
            let set = self.impls.find_or_insert(Type(imp.type_name.id().clone()), HashSet::new());
            set.insert(Type(imp.trait_name.id().clone()));
        }
    }
}

pub trait TypeEnv {
    fn find_type(&self, id: &InternedStr) -> Option<&TcType>;
    fn find_type_info(&self, id: &InternedStr) -> Option<TypeInfo>;
}

pub struct Typecheck<'a> {
    environment: Option<&'a TypeEnv>,
    type_infos: TypeInfos,
    module: HashMap<InternedStr, TcType>,
    stack: ScopedMap<InternedStr, TcType>,
}

impl <'a> TypeEnv for Typecheck<'a> {
    
    fn find_type(&self, id: &InternedStr) -> Option<&TcType> {
        self.stack.find(id)
            .or_else(|| self.module.find(id))
            .or_else(|| self.environment.and_then(|e| e.find_type(id)))
    }

    fn find_type_info(&self, id: &InternedStr) -> Option<TypeInfo> {
        self.type_infos.find_type_info(id)
            .or_else(|| self.environment.and_then(|e| e.find_type_info(id)))
    }
}

impl <'a> Typecheck<'a> {
    
    pub fn new() -> Typecheck<'a> {
        Typecheck {
            environment: None,
            module: HashMap::new(),
            type_infos: TypeInfos::new(),
            stack: ScopedMap::new(),
        }
    }
    
    fn find(&self, id: &InternedStr) -> TcResult {
        self.find_type(id)
            .map(|t| t.clone())
            .map(Ok)
            .unwrap_or_else(|| Err(UndefinedVariable(id.clone())))
    }

    fn find_type_info(&self, id: &InternedStr) -> Result<TypeInfo, TypeError> {
        (self as &TypeEnv).find_type_info(id)
            .map(|s| Ok(s))
            .unwrap_or_else(|| Err(UndefinedStruct(id.clone())))
    }
    
    fn find_trait(&self, name: &InternedStr) -> Result<&[(InternedStr, TcType)], TypeError> {
        self.type_infos.find_trait(name)
            .map(Ok)
            .unwrap_or_else(|| Err(UndefinedTrait(name.clone())))
    }
    fn has_trait(&self, typ: &TcType) -> bool {
        match *typ {
            Type(ref id) => self.find_trait(id).is_ok(),
            _ => false
        }
    }

    fn stack_var(&mut self, id: InternedStr, typ: TcType) {
        self.stack.insert(id, typ);
    }

    pub fn add_environment(&mut self, env: &'a TypeEnv) {
        self.environment = Some(env);
    }

    pub fn typecheck_module(&mut self, module: &mut Module<TcIdent>) -> Result<(), TypeError> {
        
        for f in module.functions.mut_iter() {
            f.name.typ = FunctionType(f.arguments.iter().map(|f| from_vm_type(&f.typ)).collect(), box from_vm_type(&f.return_type));
            self.module.insert(f.name.name, f.name.typ.clone());
        }
        self.type_infos.add_module(module);
        for s in module.structs.mut_iter() {
            let args = s.fields.iter().map(|f| from_vm_type(&f.typ)).collect();
            s.name.typ = FunctionType(args, box Type(s.name.name));
            self.module.insert(s.name.name, s.name.typ.clone());
        }
        for e in module.enums.iter() {
            for ctor in e.constructors.iter() {
                let args = ctor.arguments.iter().map(|t| from_vm_type(t)).collect();
                let typ = FunctionType(args, box Type(e.name.name));
                self.module.insert(ctor.name.name, typ);
            }
        }
        for f in module.functions.mut_iter() {
            try!(self.typecheck_function(f));
        }
        for imp in module.impls.mut_iter() {
            {
                let trait_functions = try!(self.find_trait(imp.trait_name.id()));
                for f in imp.functions.iter() {
                    let trait_function_type = try!(trait_functions.iter()
                        .find(|& &(ref name, _)| name == f.name.id())
                        .map(Ok)
                        .unwrap_or_else(|| Err(TypeError("Function does not exist in trait"))));
                    try!(self.unify_trait_function(&Type(imp.type_name.id().clone()), trait_function_type.ref1(), f));
                }
            }
            for f in imp.functions.mut_iter() {
                try!(self.typecheck_function(f));
            }
        }
        Ok(())
    }

    ///Checks that a function implemented for a trait has the correct type
    ///The special Self type in the trait is replaced with the type which implements that trait and is then unified
    ///with the actual type
    fn unify_trait_function(&self, self_type: &TcType, trait_function_type: &TcType, actual: &Function<TcIdent>) -> Result<(), TypeError> {
        use std::result;
        debug!("Unify trait {} ==>\n{} <=> {}", self_type, trait_function_type, actual);
        match *trait_function_type {
            FunctionType(ref args, ref return_type) => {
                try!(result::fold(args.iter()
                    .zip(actual.arguments.iter())
                    .map(|(e, a)| self.unify_self(self_type, e, &from_vm_type(&a.typ))), (), |_, _| ()));
                self.unify_self(self_type, &**return_type, &actual.name.typ)
            }
            _ => Err(TypeError("Trait function has non function type"))
        }
    }
    
    ///Unifies a type which might have 'Self' types in its type
    fn unify_self(&self, self_type: &TcType, trait_function_type: &TcType, actual: &TcType) -> Result<(), TypeError> {
        let mut x = trait_function_type.clone();
        replace_self(&mut x, self_type);
        self.unify(&x, actual.clone())
            .map(|_| ())
    }

    fn typecheck_function(&mut self, function: &mut Function<TcIdent>) -> Result<(), TypeError> {
        self.stack.clear();
        for arg in function.arguments.iter() {
            self.stack_var(arg.name.clone(), from_vm_type(&arg.typ));
        }
        let return_type = try!(self.typecheck(&mut function.expression));
        self.unify(&from_vm_type(&function.return_type), return_type)
            .map(|_| ())
    }

    pub fn typecheck(&mut self, expr: &mut Expr<TcIdent>) -> TcResult {
        match *expr {
            Identifier(ref mut id) => {
                self.find(id.id())
            }
            Literal(ref lit) => {
                Ok(match *lit {
                    Integer(_) => int_type_tc.clone(),
                    Float(_) => float_type_tc.clone(),
                    String(_) => string_type_tc.clone(),
                    Bool(_) => bool_type_tc.clone()
                })
            }
            Call(ref mut func, ref mut args) => {
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
            IfElse(ref mut pred, ref mut if_true, ref mut if_false) => {
                let pred_type = try!(self.typecheck(&mut**pred));
                try!(self.unify(&bool_type_tc, pred_type));
                let true_type = try!(self.typecheck(&mut**if_true));
                let false_type = try!(self.typecheck(&mut**if_false));
                self.unify(&true_type, false_type)
            }
            While(ref mut pred, ref mut expr) => {
                let pred_type = try!(self.typecheck(&mut **pred));
                try!(self.unify(&bool_type_tc, pred_type));
                self.typecheck(&mut**expr)
                    .map(|_| unit_type_tc.clone())
            }
            BinOp(ref mut lhs, ref mut op, ref mut rhs) => {
                let lhs_type = try!(self.typecheck(&mut**lhs));
                let rhs_type = try!(self.typecheck(&mut**rhs));
                try!(self.unify(&lhs_type, rhs_type.clone()));
                match op.as_slice() {
                    "+" | "-" | "*" => {
                        if lhs_type == int_type_tc || lhs_type == float_type_tc {
                            Ok(lhs_type)
                        }
                        else {
                            return Err(TypeError("Expected numbers in binop"))
                        }
                    }
                    "<" | ">" | "<=" | ">=" => Ok(bool_type_tc.clone()),
                    _ => Err(UndefinedVariable(op.name.clone()))
                }
            }
            Block(ref mut exprs) => {
                self.stack.enter_scope();
                let mut typ = BuiltinType(UnitType);
                for expr in exprs.mut_iter() {
                    typ = try!(self.typecheck(expr));
                }
                self.stack.exit_scope();
                Ok(typ)
            }
            Match(ref mut expr, ref mut alts) => {
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
            Let(ref mut id, ref mut expr) => {
                let typ = try!(self.typecheck(&mut **expr));
                self.stack_var(id.name.clone(), typ);
                Ok(unit_type_tc.clone())
            }
            Assign(ref mut lhs, ref mut rhs) => {
                let rhs_type = try!(self.typecheck(&mut **rhs));
                let lhs_type = try!(self.typecheck(&mut **lhs));
                self.unify(&lhs_type, rhs_type)
            }
            FieldAccess(ref mut expr, ref mut id) => {
                let typ = try!(self.typecheck(&mut **expr));
                match typ {
                    Type(ref struct_id) => {
                        let type_info = try!(self.find_type_info(struct_id));
                        match type_info {
                            Struct(ref fields) => {
                                id.typ = try!(fields.iter()
                                    .find(|field| field.name == id.name)
                                    .map(|field| Ok(from_vm_type(&field.typ)))
                                    .unwrap_or_else(|| Err(UndefinedField(struct_id.clone(), id.name.clone()))));
                                Ok(id.typ.clone())
                            }
                            Enum(_) => Err(TypeError("Field access on enum type"))
                        }
                    }
                    FunctionType(..) => Err(TypeError("Field access on function")),
                    BuiltinType(..) => Err(TypeError("Field acces on primitive")),
                    TypeVariable(..) => Err(TypeError("Field acces on type variable"))
                }
            }
        }
    }

    fn typecheck_pattern(&mut self, pattern: &mut Pattern<TcIdent>, match_type: TcType) -> Result<(), TypeError> {
        let typename = match match_type {
            Type(id) => id,
            _ => return Err(TypeError("Pattern matching only works on enums"))
        };
        match *pattern {
            ConstructorPattern(ref name, ref mut args) => {
                //Find the enum constructor and return the types for its arguments
                let argument_types: Vec<TcType> = match try!(self.find_type_info(&typename)) {
                    Enum(ref ctors) => {
                        match ctors.iter().find(|ctor| ctor.name.id() == name.id()) {
                            Some(ctor) => ctor.arguments.iter().map(|t| from_vm_type(t)).collect(),
                            None => return Err(TypeError("Undefined constructor"))
                        }
                    }
                    Struct(..) => return Err(TypeError("Pattern match on struct"))
                };
                for (arg, typ) in args.iter().zip(argument_types.move_iter()) {
                    self.stack_var(arg.id().clone(), typ);
                }
                Ok(())
            }
            IdentifierPattern(ref id) => {
                self.stack_var(id.id().clone(), match_type);
                Ok(())
            }
        }
    }

    fn unify(&self, expected: &TcType, actual: TcType) -> TcResult {
        debug!("Unify {} <=> {}", expected, actual);
        if *expected == actual {
            Ok(actual)
        }
        else if self.has_trait(expected) && self.type_infos.has_impl_of_trait(expected, &actual) {
            Ok(actual)
        }
        else {
            Err(TypeMismatch(expected.clone(), actual))
        }
    }
}

fn replace_self(replace_in: &mut TcType, typ: &TcType) {
    let replace = match *replace_in {
        Type(ref id) if id.as_slice() == "Self" => true,
        FunctionType(ref mut args, ref mut return_type) => {
            for a in args.mut_iter() {
                replace_self(a, typ);
            }
            replace_self(&mut **return_type, typ);
            false
        }
        _ => false
    };
    if replace {
        *replace_in = typ.clone();
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
impl <Id: Typed + Str> Typed for Expr<Id> {
    fn type_of(&self) -> &TcType {
        match *self {
            Identifier(ref id) => id.type_of(),
            Literal(ref lit) => {
                match *lit {
                    Integer(_) => &int_type_tc,
                    Float(_) => &float_type_tc,
                    String(_) => &string_type_tc,
                    Bool(_) => &bool_type_tc
                }
            }
            IfElse(_, ref arm, _) => arm.type_of(),
            Block(ref exprs) => {
                if exprs.len() == 0 {
                    &unit_type_tc
                }
                else {
                    exprs.last().unwrap().type_of()
                }
            }
            BinOp(ref lhs, ref op, _) => {
                match op.as_slice() {
                    "+" | "-" | "*" => lhs.type_of(),
                    "<" | ">" | "<=" | ">=" => &bool_type_tc,
                    _ => fail!()
                }
            }
            Let(..) | While(..) | Assign(..) => &unit_type_tc,
            Call(ref func, _) => {
                match func.type_of() {
                    &FunctionType(_, ref return_type) => &**return_type,
                    _ => fail!()
                }
            }
            Match(_, ref alts) => alts[0].expression.type_of(),
            FieldAccess(_, ref id) => id.type_of()
        }
    }
}

impl <T: Typed> Typed for Function<T> {
    fn type_of(&self) -> &TcType {
        self.name.type_of()
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use super::TcIdent;
    use ast::*;
    use parser::*;

    pub fn parse<T>(s: &str, f: |&mut Parser<TcIdent>|:'static -> ParseResult<T>) -> T {
        use std::io::BufReader;
        let mut buffer = BufReader::new(s.as_bytes());
        let mut parser = Parser::new(&mut buffer, |s| TcIdent { typ: unit_type_tc.clone(), name: s });
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
    fn traits() {
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
}
