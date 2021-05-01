#![feature(box_syntax, string_remove_matches)]
#[macro_use]
mod macros;

pub mod ast;
pub mod lexer;
pub mod parser;

pub use lexer::Lexer;
pub use lexer::Span;
pub use parser::Parser;

pub use ast2str::AstToStr;
use ves_error::Files;

pub fn parse<N, S>(
    file_id: ves_error::FileId,
    db: &ves_error::VesFileDatabase<N, S>,
) -> Result<ast::AST<'_>, ves_error::ErrCtx>
where
    N: AsRef<str> + Clone + std::fmt::Display,
    S: AsRef<str>,
{
    Parser::new(
        Lexer::new(db.source(file_id).expect("Expected a valid file id")),
        file_id,
        &db,
    )
    .parse()
}
