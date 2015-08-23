
pub use self::Instruction::*;

pub type VMIndex = u32;
pub type VMTag = u32;

#[derive(Copy, Clone, Debug)]
pub enum Instruction {
    PushInt(isize),
    PushFloat(f64),
    PushString(VMIndex),
    Push(VMIndex),
    PushGlobal(VMIndex),
    Call(VMIndex),
    TailCall(VMIndex),
    Construct(VMIndex, VMIndex),
    GetField(VMIndex),
    Split,
    TestTag(VMTag),
    Jump(VMIndex),
    CJump(VMIndex),
    Pop(VMIndex),
    Slide(VMIndex),

    //Creates a closure with 'n' upvariables
    //Pops the 'n' values on top of the stack and creates a closure
    MakeClosure(VMIndex, VMIndex),
    //Creates a closure but does not fill its environment
    NewClosure(VMIndex, VMIndex),
    //Fills the previously allocated closure with `n` upvariables
    CloseClosure(VMIndex),
    PushUpVar(VMIndex),

    GetIndex,
    SetIndex,

    AddInt,
    SubtractInt,
    MultiplyInt,
    IntLT,
    IntEQ,

    AddFloat,
    SubtractFloat,
    MultiplyFloat,
    FloatLT,
    FloatEQ,
}


impl Instruction {
    pub fn adjust(&self) -> i32 {
        match *self {
            PushInt(_) | PushFloat(_) | PushString(_) | Push(_) | PushGlobal(_) => 1,
            Call(n) => -(n as i32),
            TailCall(n) => -(n as i32),
            Construct(_, n) => 1 - n as i32,
            GetField(_) => 0,
            Split => -1,//The number of added stack slots are handled separately as the type is needed
            TestTag(_) => 1,
            Jump(_) => 0,
            CJump(_) => -1,
            Pop(n) => -(n as i32),
            Slide(n) => -(n as i32),
            MakeClosure(_, _) => 1,
            NewClosure(_, _) => 1,
            CloseClosure(_) => -1,
            PushUpVar(_) => 1,
            GetIndex => 0,
            SetIndex => -1,
            AddInt | SubtractInt | MultiplyInt | IntLT | IntEQ |
            AddFloat | SubtractFloat | MultiplyFloat | FloatLT | FloatEQ => -1
        }
    }
}
