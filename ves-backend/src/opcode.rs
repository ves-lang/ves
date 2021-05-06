// Opcode guidelines:
// - Names should be first and foremost self-describing, so:
//   - Try to name with a verb (e.g. `Add`) or a verb+noun (e.g. `PushTrue`)
//   - If there is an unambigous, shorter name, then it can be used, even if it does
//     not follow the pattern (e.g. `LessThan`)
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
    /// Get a closure's upvalue
    GetUpvalue(/* index */ u32),
    /// Set a closure's upvalue
    SetUpvalue(/* index */ u32),
    /// Get a global value
    GetGlobal(/* global slot */ u32),
    /// Set a global value
    SetGlobal(/* global slot */ u32),
    /// Get a property
    ///
    /// Top of the stack should be: [object]
    GetProp(/* name constant index */ u32),
    /// Get a property
    ///
    /// Top of the stack should be: [object]
    TryGetProp(/* name constant index */ u32),
    /// Set a property
    ///
    /// Top of the stack should be: [object, value]
    SetProp(/* name constant index */ u32),
    /// Get an item
    ///
    /// Top of the stack should be: [object, key]
    GetItem,
    /// Set an item
    ///
    /// Top of the stack should be: [object, key, value]
    SetItem,
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
    /// Add `1` to operand
    AddOne,
    /// Subtract operands
    Subtract,
    /// Subtract `1` from operand
    SubtractOne,
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
    /// Unwrap an Ok
    ///
    /// If the operand is `Ok`, this should evaluate to `true`
    /// and set the local at `stack slot` to the inner value.
    /// If the operand is not `Ok`, this should only evaluate to `false`
    UnwrapOk(/* stack slot */ u32),
    /// Unwrap an Err
    ///
    /// If the operand is `Err`, this should evaluate to `true`
    /// and set the local at `stack slot` to the inner value.
    /// If the operand is not `Err`, this should only evaluate to `false`
    UnwrapErr(/* stack slot */ u32),
    /// Mark the operand as `spread`, which means:
    /// - It must be iterable (conform to the iterator protocol)
    /// - In an array literal, the values of this iterator are all pushed into the array
    /// - In a call, the values of this iterator are pushed into an the rest argument array
    Spread,
    /// Call the operand with `count` arguments
    ///
    /// The stack should look like: [<function>, <receiver>, <arg 0>, <arg 1>, <arg 2>, ..., <arg [count]>]
    ///
    /// The `receiver` stack slot is reserved and it's value is `none` if there is no receiver
    Call(/* count */ u32),
    /// Defer a call
    ///
    /// This checks if the call is valid, and pushes it onto the current call's defer stack.
    ///
    /// When the call stack is unwound or the function returns, any deferred calls from
    /// the defer stack are executed.
    Defer,
    /// Join `count` fragments on the stack into a single string
    Interpolate(/* count */ u32),
    /// Create an array from `count` items on the stack
    CreateArray(/* count */ u32),
    /// Create an empty map
    CreateEmptyMap,
    /// Insert a key/value pair into the map
    MapInsert,
    /// Extend a map with all entries of another map
    MapExtend,
    /// Create a closure from a closure descriptor in the constants pool
    CreateClosure(/* descriptor constant index */ u32),
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
    /// Jump to a specific address if operand is false
    JumpIfFalse(/* address */ u32),
    /// Return from a call
    Return,
    /// A compile-time label for one or more jumps.
    Label(/* label id */ u32),
}

static_assertions::assert_eq_size!(Opcode, u64);
