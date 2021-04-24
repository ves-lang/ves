#![feature(box_syntax, string_remove_matches)]
#[macro_use]
mod macros;

pub mod ast;
pub mod lexer;
pub mod parser;

pub use lexer::Span;
