// Opcode guidelines:
// - Names should be first and foremost self-describing, so:
//   - Try to name with a verb (e.g. `Add`) or a verb+noun (e.g. `PushTrue`)
//   - If there is an unambigous, shorter name, then it can be used, even if it does
//     not follow the pattern (e.g. `LessThan`)
// QQQ(moscow): maybe we *should* store struct-like variants instead of tuple-like variants?
// - Since the opcode enum variants with values store numeric types, it is necessary to
//   include a comment describing the value's meaning or intended usage

#[derive(Clone, Copy, PartialEq, PartialOrd, Debug)]
#[repr(u32)]
pub enum Opcode {
    /// Get a value from the constants buffer
    GetConst(/* constant index */ u32),
    /// Get a value at specified stack address
    GetLocal(/* stack slot */ u32),
    /// Set a value at specified stack address
    SetLocal(/* stack slot */ u32),
    /// Get a global value
    GetGlobal(/* global slot */ u32),
    /// Set a global value
    SetGlobal(/* global slot */ u32),
    /// Instruction for pushing numeric values which fit within f32 onto the stack
    PushNum32(/* value */ f32),
    /// Push `true` onto the stack
    PushTrue,
    /// Push `false` onto the stack
    PushFalse,
    /// Push `none` onto the stack
    PushNone,
    /// Add operands
    Add,
    /// Subtract operands
    Subtract,
    /// Multiply operands
    Multiply,
    /// Divide operands
    Divide,
    /// Divide operands, returning the remainder
    Remainder,
    /// Bring one operand to the power of another
    Power,
    /// Negate an operand
    Negate,
    /// Logical '&&'
    And,
    /// Logical '||'
    Or,
    /// Logical '!'
    Not,
    /// Check if operands are equal
    Equal,
    /// Check if operands are not equal
    NotEqual,
    /// Check if left operand has a value lower than right operand
    LessThan,
    /// Check if left operand has a value lower than or equal to right operand
    LessEqual,
    /// Check if left operand has a value greater than right operand
    GreaterThan,
    /// Check if left operand has a value greater than or equal to right operand
    GreaterEqual,
    /// Check if type of operand is `num`
    IsNum,
    /// Check if type of operand is `str`
    IsStr,
    /// Check if type of operand is `bool`
    IsBool,
    /// Check if type of operand is `map`
    IsMap,
    /// Check if type of operand is `array`
    IsArray,
    /// Check if type of operand is `none`
    IsNone,
    /// Check if type of operand is not `none`
    IsSome,
    /// Compare types of operands
    CompareType,
    /// Check if right operand has field or method with name evaluated from left operand
    HasProperty,
    /// If `expr` is an error, return `expr` from the current function (`expr` should stay wrapped in a Result),
    /// otherwise unwrap `expr`
    Try,
    /// Wrap operand in Ok
    WrapOk,
    /// Wrap operand in Err
    WrapErr,
    /// Print a single value
    Print,
    /// Print N values
    PrintN(/* count */ u32),
    /// Pop a value off the stack
    Pop,
    /// Pop N values off the stack
    PopN(/* count */ u32),
    /// Unconditional jump to a specific address
    Jump(/* address */ u32),
    /// Return from a call
    Return,
    /// A compile-time label for one or more jumps.
    Label(/* label id */ u32),
}

static_assertions::assert_eq_size!(Opcode, u64);
