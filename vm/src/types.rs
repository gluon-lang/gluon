
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
    Store(VMIndex),
    StoreGlobal(VMIndex),
    Call(VMIndex),
    TailCall(VMIndex),
    Construct(VMIndex, VMIndex),
    GetField(VMIndex),
    SetField(VMIndex),
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
    InstantiateConstrained(VMIndex),
    PushUpVar(VMIndex),
    StoreUpVar(VMIndex),

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

