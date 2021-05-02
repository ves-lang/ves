#![feature(box_syntax, box_patterns)]
#![allow(clippy::new_without_default, clippy::comparison_chain)]
pub mod builder;
pub mod emit;
pub mod opcode;

pub type Span = core::ops::Range<usize>;
type Result<T> = std::result::Result<T, ves_error::VesError>;
