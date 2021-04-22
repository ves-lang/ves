use logos::{Logos, Span};

pub struct Token<'a> {
    /// Slice of the source from which this token was parsed
    pub lexeme: &'a str,
    /// Start+end range of this token in the line where it was parsed
    pub span: Span,
    /// Line in the source where this token was parsed
    ///
    /// Line starts at 1
    pub line: usize,
    pub kind: TokenKind,
}

impl<'a> Token<'a> {
    pub fn new(lexeme: &'a str, span: Span, line: usize, kind: TokenKind) -> Token<'a> {
        Token {
            lexeme,
            span,
            line,
            kind,
        }
    }
}

pub enum TokenKind {
    // Simple (1 char) tokens
    Plus,         // +
    Minus,        // -
    Star,         // *
    Slash,        // /
    Percent,      // %
    Equal,        // =
    Bang,         // !
    Less,         // <
    More,         // >
    LeftParen,    // (
    RightParen,   // )
    LeftBracket,  // {
    RightBracket, // }
    LeftBrace,    // [
    RightBrace,   // ]
    Comma,        // ,
    Dot,          // .
    Semi,         // ;

    // Compound (2+ char) tokens
    // Arithmetic operation + assignment
    PlusEqual,    // +=
    MinusEqual,   // -=
    StarEqual,    // *=
    SlashEqual,   // /=
    PercentEqual, // %=
    // Comparison
    EqualEqual, // ==
    BangEqual,  // !=
    LessEqual,  // <=
    MoreEqual,  // >=
    /// Power operator
    Power, // **
    /// Optional chaining
    MaybeDot, // ?.
    /// For declaring ranges
    DoubleDot, // ..
    /// End-inclusive range
    DoubleDotEqual, // ..=
    /// Spread operator
    Ellipsis, // ...
    /// Function shorthand syntax
    Arrow, // =>

    // Literals
    Identifier, // [a-zA-Z_][a-zA-Z0-9_]*
    // TODO: string interpolation
    // InterpolatedString,
    String, // "([^\"\\\\]|\\\\.)*"
    // '([^'\\\\]|\\\\.)*'
    Number,

    // Keywords
    /// No value (same as nil/null)
    None,
    /// Boolean 'true'
    True,
    /// Boolean 'false'
    False,
    /// Result 'ok' variant
    Ok,
    /// Result 'err' variant
    Err,
    /// Immutable variable
    Let,
    /// Mutable variable
    Mut,
    /// Field existence check
    In,
    /// Type comparison
    Is,
    If,
    Else,
    /// Infinite 'loop'
    Loop,
    /// For loop
    For,
    /// While loop
    While,
    /// Break out of loop
    Break,
    /// Continue in loop
    Continue,
    /// Return from function
    Return,
    /// Block expression
    Do,
    /// Error propagation
    Try,
    /// Defer call until end of current block scope
    Defer,
    /// Print values
    Print,
    /// Function
    Fn,
    /// Struct
    Struct,

    // Whitespace or ignored tokens
    Comment,    // //[^\n]*
    // TODO: multi-line comments
    // They should be nestable, e.g. /*/**/*/
    // MultiLineComment,
    EOL,        // \n
    Whitespace, // space, \n, \r, \t, \f
    Error,
    EOF,
}
