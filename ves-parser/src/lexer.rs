use logos::{
    internal::{CallbackResult, LexerInternal},
    Logos,
};
use std::borrow::Cow;
use std::convert::Into;

use ast2str::AstToStr;

pub use logos::Span;

pub type Lexer<'a> = logos::Lexer<'a, TokenKind<'a>>;

#[derive(Clone, Debug, PartialEq, AstToStr)]
pub struct Token<'a> {
    #[forward]
    /// Slice of the source from which this token was parsed
    pub lexeme: Cow<'a, str>,
    /// Start+end range of this token in the line where it was parsed
    pub span: Span,
    /// The token kind which optionally also contains extra
    pub kind: TokenKind<'a>,
}

impl<'a> Token<'a> {
    pub fn new<S: Into<Cow<'a, str>>>(lexeme: S, span: Span, kind: TokenKind<'a>) -> Token<'a> {
        Token {
            lexeme: lexeme.into(),
            span,
            kind,
        }
    }
}

pub trait NextTokenExt<'a> {
    fn next_token(&mut self) -> Option<Token<'a>>;
}

impl<'a> NextTokenExt<'a> for logos::Lexer<'a, TokenKind<'a>> {
    fn next_token(&mut self) -> Option<Token<'a>> {
        self.next()
            .map(|next| Token::new(self.slice(), self.span(), next))
    }
}

#[derive(Clone, Debug, PartialEq, Logos)]
pub enum TokenKind<'a> {
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    #[token("%")]
    Percent,
    #[token("!")]
    Bang,
    #[token("<")]
    Less,
    #[token(">")]
    More,
    #[token("(")]
    LeftParen,
    #[token(")")]
    RightParen,
    #[token("{")]
    LeftBracket,
    #[token("}")]
    RightBracket,
    #[token("[")]
    LeftBrace,
    #[token("]")]
    RightBrace,
    #[regex("@")]
    At,
    #[token(":")]
    Colon,
    #[token(",")]
    Comma,
    #[token(";")]
    Semi,
    #[token("=")]
    Equal,
    #[token("**")]
    Power,
    #[token("&&")]
    And,
    #[token("||")]
    Or,
    #[token("&&=")]
    AndEqual,
    #[token("||=")]
    OrEqual,
    #[token("+=")]
    PlusEqual,
    #[token("-=")]
    MinusEqual,
    #[token("*=")]
    StarEqual,
    #[token("/=")]
    SlashEqual,
    #[token("%=")]
    PercentEqual,
    #[token("**=")]
    PowerEqual,
    #[token("==")]
    EqualEqual,
    #[token("!=")]
    BangEqual,
    #[token("<=")]
    LessEqual,
    #[token(">=")]
    MoreEqual,
    #[token(".")]
    Dot,
    /// Optional chaining
    #[token("?.")]
    MaybeDot,
    /// Spread operator
    #[token("...")]
    Ellipsis,
    /// Function shorthand syntax
    #[token("=>")]
    Arrow,
    // TODO: unicode identifiers
    // after we've identified whether or not it will heavily bring down performance
    /// ASCII identifier
    ///
    /// May contain numbers except for the first character
    #[regex("[a-zA-Z_][a-zA-Z0-9_]*")]
    Identifier,
    #[regex("[0-9]+\\.\\.=?[0-9]+", priority = 3)]
    #[token("..")]
    #[token("..=")]
    Range,
    /// Interpolated string
    ///
    /// e.g. `f"fragment {expr}"` `f"\{escaped}"`
    #[regex("f\"([^\"\\\\]|\\\\.)*\"", interpolated_string)]
    #[regex("f'([^'\\\\]|\\\\.)*'", interpolated_string)]
    InterpolatedString(Vec<Frag<'a>>),
    /// String literal
    #[regex("\"([^\"\\\\]|\\\\.)*\"")]
    #[regex("'([^'\\\\]|\\\\.)*'")]
    String,
    /// Floating point (IEEE754) numeric literal
    /// TODO: underscores
    #[regex("-?((((([0-9]+)(\\.[0-9]*)?)|(\\.[0-9]+))([Ee][+-]?[0-9]+)?)|(NaN)|(inf))", priority = 2)]
    Number,
    /// No value (same as nil/null)
    #[token("none")]
    None,
    /// Boolean 'true'
    #[token("true")]
    True,
    /// Boolean 'false'
    #[token("false")]
    False,
    /// Result 'ok' variant
    #[token("ok")]
    Ok,
    /// Result 'err' variant
    #[token("err")]
    Err,
    /// Immutable variable
    #[token("let")]
    Let,
    /// Mutable variable
    #[token("mut")]
    Mut,
    /// Field existence check
    #[token("in")]
    In,
    /// Type comparison
    #[token("is")]
    Is,
    #[token("if")]
    If,
    #[token("else")]
    Else,
    /// Infinite 'loop'
    #[token("loop")]
    Loop,
    /// For loop
    #[token("for")]
    For,
    /// While loop
    #[token("while")]
    While,
    /// Break out of loop
    #[token("break")]
    Break,
    /// Continue in loop
    #[token("continue")]
    Continue,
    /// Return from function
    #[token("return")]
    Return,
    /// Block expression
    #[token("do")]
    Do,
    /// Error propagation
    #[token("try")]
    Try,
    /// Defer call until end of current block scope
    #[token("defer")]
    Defer,
    /// Print
    #[token("print")]
    Print,
    /// Function
    #[token("fn")]
    Fn,
    /// Struct
    #[token("struct")]
    Struct,
    /// The reserved self identifier.
    #[token("self")]
    Self_,
    // Whitespace or ignored tokens
    #[regex("//[^\n]*", logos::skip)]
    Comment,
    /// Multi-line comment (they can be nested)
    #[regex("/\\*", multi_line_comment)]
    MultiLineComment,
    #[regex("[ \n\r\t]+", logos::skip)]
    Whitespace,
    #[error]
    Error,
    EOF,
}

#[derive(Debug, Clone, Copy)]
pub enum SkipOnSuccess {
    Success,
    Error,
}

impl<'a> CallbackResult<'a, (), TokenKind<'a>> for SkipOnSuccess {
    fn construct<Constructor>(self, _: Constructor, lex: &mut logos::Lexer<'a, TokenKind<'a>>)
    where
        Constructor: Fn(()) -> TokenKind<'a>,
    {
        match self {
            SkipOnSuccess::Success => {
                // Taken from the callback for Filter::Skip
                lex.trivia();
                TokenKind::lex(lex);
            }
            SkipOnSuccess::Error => {
                // Taken from the callback for bool
                lex.set(TokenKind::ERROR)
            }
        }
    }
}

fn multi_line_comment<'a>(lex: &mut logos::Lexer<'a, TokenKind<'a>>) -> SkipOnSuccess {
    // how many characters we went through
    let mut n = 0;
    // how many multi-line comment opening tokens we found
    // this starts at one, because the initial /* is already consumed
    let mut opening_count = 1;
    let mut previous_was_star = false;
    for ch in lex.remainder().bytes() {
        n += 1;
        match ch {
            b'*' => previous_was_star = true,
            b'/' if previous_was_star => {
                // closing
                previous_was_star = false;
                opening_count -= 1;
                if opening_count == 0 {
                    break;
                }
            }
            b'/' => {
                // opening
                opening_count += 1;
                previous_was_star = false;
            }
            _ => previous_was_star = false,
        }
    }

    if opening_count == 0 {
        lex.bump(n);
        SkipOnSuccess::Success
    } else {
        SkipOnSuccess::Error
    }
}

/// A fragment of an interpolated string.
#[derive(Clone)]
pub enum Frag<'a> {
    /// A string fragment.
    Str(Token<'a>),
    /// An unterminated interpolation fragment.
    UnterminatedFragment(Token<'a>),
    /// An executable interpolated fragment.
    Sublexer(logos::Lexer<'a, TokenKind<'a>>),
}

impl<'a> std::fmt::Debug for Frag<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Str(tok) | Self::UnterminatedFragment(tok) =>
                    if f.alternate() {
                        format!("{:#?}", tok)
                    } else {
                        format!("{:?}", tok)
                    },
                Self::Sublexer(_) => "Frag::Lexer(*)".to_owned(),
            }
        )
    }
}

impl<'a> PartialEq for Frag<'a> {
    fn eq(&self, other: &Frag<'a>) -> bool {
        match (self, other) {
            (Self::Str(l), Self::Str(r)) => l.lexeme == r.lexeme,
            (Self::UnterminatedFragment(l), Self::UnterminatedFragment(r)) => l.lexeme == r.lexeme,
            (_, _) => true,
        }
    }
}

fn interpolated_string<'a>(lex: &mut logos::Lexer<'a, TokenKind<'a>>) -> Vec<Frag<'a>> {
    let global_start = lex.span().start;
    let source = lex.source();

    let mut frags = vec![];

    let bytes = lex.slice().bytes().collect::<Vec<_>>();

    // Skip the `f` and the opening quote.
    let mut i = 2;
    let mut prev_fragment_end = 2;

    while i < bytes.len() - 1 {
        if bytes[i] == b'{' {
            // An unescaped fragment
            if bytes.get(i - 1) != Some(&b'\\') {
                let span = Span {
                    start: global_start + prev_fragment_end,
                    end: global_start + i,
                };
                frags.push(Frag::Str(Token::new(
                    &source[span.clone()],
                    span,
                    TokenKind::String,
                )));

                let frag_start = i + 1;
                while i < bytes.len() && bytes[i] != b'}' {
                    i += 1;
                }

                let span = Span {
                    start: global_start + frag_start,
                    end: global_start + i,
                };

                if i == bytes.len() && bytes[i - 1] != b'}' {
                    frags.push(Frag::UnterminatedFragment(Token::new(
                        &source[Span {
                            start: span.start - 1, // include the opening bracket
                            end: span.end - 1,     // exclude the closing quote
                        }],
                        span,
                        TokenKind::Error,
                    )))
                } else {
                    frags.push(Frag::Sublexer(TokenKind::lexer(&source[span])));
                }

                prev_fragment_end = i + 1;
            } else {
                let span = Span {
                    start: global_start + prev_fragment_end,
                    end: global_start + i - 1, // exclude the escape
                };

                if !source[span.clone()].is_empty() {
                    frags.push(Frag::Str(Token::new(
                        &source[span.clone()],
                        span,
                        TokenKind::String,
                    )));
                }
                prev_fragment_end = i;
            }
        }
        i += 1;
    }

    if prev_fragment_end < bytes.len() - 1 {
        let span = Span {
            start: global_start + prev_fragment_end,
            end: global_start + bytes.len() - 1,
        };
        frags.push(Frag::Str(Token::new(
            &source[span.clone()],
            span,
            TokenKind::String,
        )));
    }

    frags
}

#[rustfmt::skip]
#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    struct TestToken<'a>(Token<'a>);
    impl<'a> std::convert::From<Token<'a>> for TestToken<'a> {
        fn from(token: Token<'a>) -> Self {
            TestToken(token)
        }
    }
    impl<'a> std::ops::Deref for TestToken<'a> {
        type Target = Token<'a>;
        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }
    impl<'a> std::ops::DerefMut for TestToken<'a> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.0
        }
    }
    impl<'a> PartialEq<TestToken<'a>> for TestToken<'a> {
        fn eq(&self, other: &TestToken<'a>) -> bool {
            self.0.kind == other.0.kind && self.0.lexeme == other.0.lexeme
        }
    }
    impl<'a> std::fmt::Debug for TestToken<'a> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.0.fmt(f)
        }
    }

    fn test_tokenize_inner<'a>(lex: &mut logos::Lexer<'a, TokenKind<'a>>) -> Vec<TestToken<'a>> {
        let mut out = Vec::new();
        while let Some(token) = lex.next_token() {
            out.push(token.into());
        }
        out
    }
    fn test_tokenize(src: &'_ str) -> Vec<TestToken<'_>> {
        test_tokenize_inner(&mut TokenKind::lexer(src))
    }
    macro_rules! token {
        ($kind:ident, $lexeme:literal) => (TestToken(Token::new($lexeme, 0..1, TokenKind::$kind)));
        ($kind:expr, $lexeme:literal) => (TestToken(Token::new($lexeme, 0..1, $kind)));
    }


    #[test]
    fn arithmetic() {
        const SOURCE: &str = r#"+-*/%**"#;
        assert_eq!(
            test_tokenize(SOURCE),
            vec![
                token!(Plus, "+"), token!(Minus, "-"), token!(Star, "*"),
                token!(Slash, "/"), token!(Percent, "%"), token!(Power, "**")
            ]
        );
    }

    #[test]
    fn boolean() {
        const SOURCE: &str = r#"! < > == != <= >="#;
        assert_eq!(
            test_tokenize(SOURCE),
            vec![
                token!(Bang, "!"), token!(Less, "<"), token!(More, ">"),
                token!(EqualEqual, "=="), token!(BangEqual, "!="),
                token!(LessEqual, "<="), token!(MoreEqual, ">=")
            ]
        );
    }

    #[test]
    fn dot_tokens() {
        const SOURCE: &str = r#"ident.ident ident?.ident 0..0 0..=0 ...ident"#;
        assert_eq!(
            test_tokenize(SOURCE),
            vec![
                token!(Identifier, "ident"), token!(Dot, "."), token!(Identifier, "ident"),
                token!(Identifier, "ident"), token!(MaybeDot, "?."), token!(Identifier, "ident"),
                token!(Range, "0..0"), token!(Range, "0..=0"),
                token!(Ellipsis, "..."), token!(Identifier, "ident")
            ]
        );
    }

    #[test]
    fn field_access_range() {
        const SOURCE: &str = r#"ident.ident..ident.ident"#;
        assert_eq!(
            test_tokenize(SOURCE),
            vec![
                token!(Identifier, "ident"), token!(Dot, "."), token!(Identifier, "ident"),
                token!(Range, ".."),
                token!(Identifier, "ident"), token!(Dot, "."), token!(Identifier, "ident"),
            ]
        );
    }

    #[test]
    fn float_range() {
        const SOURCE: &str = r#"0.0..1.0"#;
        assert_eq!(
            test_tokenize(SOURCE),
            vec![
                token!(Number, "0.0"), token!(Range, ".."), token!(Number, "1.0")
            ]
        );
    }

    #[test]
    fn simple_range() {
        const SOURCE: &str = r#"0..1"#;
        assert_eq!(
            test_tokenize(SOURCE),
            vec![
                token!(Range, "0..1")
            ]
        );
    }

    #[test]
    fn comment() {
        const SOURCE: &str = "// asdfasdfasdfasdfasdfasdfasdf\nident";
        assert_eq!(
            test_tokenize(SOURCE),
            vec![
                token!(Identifier, "ident")
            ]
        );
    }

    #[test]
    fn multi_comment() {
        const SOURCE: &str = "/* */ /* /* /* /******afhišuhůů§ßß×××$$ůĐ[đĐ[đĐ[đ*/ */ */ */ ident";
        assert_eq!(
            test_tokenize(SOURCE),
            vec![
                token!(Identifier, "ident")
            ]
        );
    }

    #[test]
    fn unterminated_multi_comment() {
        const SOURCE: &str = "/* ident";
        assert_eq!(
            test_tokenize(SOURCE),
            vec![
                token!(TokenKind::Error, "/*"),
                token!(Identifier, "ident")
            ]
        );
    }

    #[test]
    fn labeled_loop() {
        const SOURCE: &str = "@label: loop {}";
        assert_eq!(
            test_tokenize(SOURCE),
            vec![
                token!(At, "@"), token!(Identifier, "label"), token!(Colon, ":"),
                token!(Loop, "loop"), token!(LeftBracket, "{"), token!(RightBracket, "}"),
            ]
        );
    }

    #[test]
    fn bad_tokens() {
        const SOURCE: &str = "ß$÷×";
        assert_eq!(
            test_tokenize(SOURCE),
            vec![
                token!(Error, "ß"), token!(Error, "$"), token!(Error, "÷"), token!(Error, "×")
            ]
        );
    }

    #[test]
    fn string_interpolation() {
        const SOURCE: &str = r#"f"1 + 1 = {1 + 1}""#;
        let mut actual = test_tokenize(SOURCE);
        assert_eq!(actual.len(), 1);
        if let TokenKind::InterpolatedString(fragments) = &mut actual[0].kind {
            assert_eq!(fragments.len(), 2);
            if let Frag::Str(token) = &fragments[0] {
                assert_eq!(TestToken(token.clone()), token!(String, "1 + 1 = "));
            }
            if let Frag::Sublexer(lex) = &mut fragments[1] {
                assert_eq!(
                    test_tokenize_inner(lex),
                    vec![
                        token!(Number, "1"), token!(Plus, "+"), token!(Number, "1"),
                    ]
                );
            }
        } else {
            assert_eq!("TokenKind was not InterpolatedString", "");
        }
    }

    #[test]
    fn string_interpolation_escape() {
        const SOURCE: &str = r#"f"\{escaped}""#;
        assert_eq!(
            test_tokenize(SOURCE),
            vec![
                TestToken(Token::new(r#"f"\{escaped}""#, 0..1, TokenKind::InterpolatedString(
                    vec![
                        Frag::Str(Token::new(r#"{escaped}"#, 0..1, TokenKind::String))
                    ]
                )))
            ]
        );
    }

    #[test]
    fn bad_string_interpolation() {
        const SOURCE: &str = r#"f"an {unterminated fragment""#;
        assert_eq!(
            test_tokenize(SOURCE),
            vec![
                TestToken(Token::new(r#"f"an {unterminated fragment""#, 0..28, TokenKind::InterpolatedString(
                    vec![
                        Frag::Str(Token::new(r#"an "#, 2..5, TokenKind::String)),
                        Frag::UnterminatedFragment(Token::new(r#"{unterminated fragment"#, 6..28, TokenKind::Error))
                    ]
                )))
            ]
        );
    }

    #[test]
    fn unicode_string() {
        const SOURCE: &str = r#""😂""#;
        assert_eq!(
            test_tokenize(SOURCE),
            vec![
                token!(String, "\"😂\"")
            ]
        );
    }
}
