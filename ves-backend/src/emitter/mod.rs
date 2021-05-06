pub mod builder;
pub mod emit;
pub mod opcode;

pub type Result<T> = std::result::Result<T, ves_error::VesError>;
