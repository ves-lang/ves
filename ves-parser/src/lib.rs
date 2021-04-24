#![feature(box_syntax)]
#[macro_use]
mod macros;

pub mod ast;
pub mod lexer;
pub mod parser;

pub use lexer::Span;
