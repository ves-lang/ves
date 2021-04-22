use logos::{Logos, Span};

#[derive(Clone, Debug, PartialEq)]
pub struct Token<'a> {
    /// Slice of the source from which this token was parsed
    pub lexeme: &'a str,
    /// Start+end range of this token in the line where it was parsed
    pub span: Span,
    /// The token kind which optionally also contains extra
    pub kind: TokenKind<'a>,
}

impl<'a> Token<'a> {
    pub fn new(lexeme: &'a str, span: Span, kind: TokenKind<'a>) -> Token<'a> {
        Token { lexeme, span, kind }
    }
}

pub trait NextTokenExt<'a> {
    fn next_token(&mut self) -> Option<Token<'a>>;
}

impl<'a> NextTokenExt<'a> for logos::Lexer<'a, TokenKind<'a>> {
    fn next_token(&mut self) -> Option<Token<'a>> {
        match self.next() {
            Some(next) => Some(Token::new(self.slice(), self.span(), next)),
            None => None,
        }
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
    #[regex(r#"f"([^"\\\\]|\\\\.)*""#, interpolated_string)]
    #[regex(r#"f'([^'\\\\]|\\\\.)*'"#, interpolated_string)]
    InterpolatedString(Vec<Frag<'a>>),
    /// String literal
    #[regex(r#""([^"\\\\]|\\\\.)*""#)]
    #[regex(r#"'([^'\\\\]|\\\\.)*'"#)]
    String,
    /// Floating point (IEEE754) numeric literal
    /// TODO: ignore underscores
    #[regex("-?(((((([0-9]|([0-9][0-9]|_[0-9]))+)(\\.[0-9]*)?)|(\\.[0-9]+))([Ee][+-]?[0-9]+)?)|(NaN)|(inf))", priority = 2)]
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
    /// Print values
    #[token("print")]
    Print,
    /// Function
    #[token("fn")]
    Fn,
    /// Struct
    #[token("struct")]
    Struct,

    // Whitespace or ignored tokens
    #[regex("//[^\n]*")]
    Comment,
    /// Multi-line comment (they can be nested)
    #[regex("/\\*", multi_line_comment)]
    MultiLineComment,
    #[regex("[ \n\r\t]+", logos::skip)]
    Whitespace,
    #[error]
    Error,
    //EOF,
}

fn multi_line_comment<'a>(lex: &mut logos::Lexer<'a, TokenKind<'a>>) -> bool {
    // how many characters we went through
    let mut n = 0;
    // how many multi-line comment opening tokens we found
    // this starts at one, because the initial /* causes this
    // function to be called
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
        lex.bump(n - 1);
        true
    } else {
        false
    }
}

/// A fragment of an interpolated string.
#[derive(Clone)]
pub enum Frag<'a> {
    /// A string fragment.
    Str(Token<'a>),
    /// An executable interpolated fragment.
    Sublexer(logos::Lexer<'a, TokenKind<'a>>),
}

impl<'a> std::fmt::Debug for Frag<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Str(tok) =>
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
            _ => false,
        }
    }
}

fn interpolated_string<'a>(
    lex: &mut logos::Lexer<'a, TokenKind<'a>>,
) -> Result<Vec<Frag<'a>>, String> {
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

                frags.push(Frag::Sublexer(TokenKind::lexer(&source[span])));

                prev_fragment_end = i + 1;
            } else {
                let span = Span {
                    start: global_start + prev_fragment_end,
                    end: global_start + i - 1, // exclude the escape
                };

                frags.push(Frag::Str(Token::new(
                    &source[span.clone()],
                    span,
                    TokenKind::String,
                )));
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
        )))
    }

    Ok(frags)
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

    fn test_tokenize<'a>(src: &'a str) -> Vec<TestToken<'a>> {
        let mut out = Vec::new();
        let mut lex = TokenKind::lexer(src);
        while let Some(token) = lex.next_token() {
            out.push(token.into());
        }
        out
    }
    macro_rules! token {
        ($kind:ident, $lexeme:literal) => (TestToken(Token::new($lexeme, 0..1, TokenKind::$kind)))
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

}
