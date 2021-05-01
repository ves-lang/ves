#[derive(Clone, Copy, PartialEq, PartialOrd, Debug)]
#[repr(u32)]
pub enum Opcode {
    /// Get a value from the constants buffer
    GetConst(u16),
    /// Get a value at specified stack address
    GetLocal(u8),
    /// Set a value at specified stack address
    SetLocal(u8),

    /// Instruction for pushing numeric values which fit within f32 onto the stack
    PushFloat32(f32),

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

static_assertions::assert_eq_size!(Opcode, u64);
