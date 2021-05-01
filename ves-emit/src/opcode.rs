#[derive(Clone, Copy, PartialEq, PartialOrd, Debug)]
pub enum Opcode {
    /// Get a value from the constants buffer
    GetConst(u16),
    /// Get a value at specified stack address
    GetLocal(u8),
    /// Set a value at specified stack address
    SetLocal(u8),

    /// Push a number onto the stack
    PushNumber(f64),

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

    /// Pop a value off the stack
    Pop,
    /// Pop N values off the stack
    PopN(u8),

    /// Return from a call
    Return,
}
