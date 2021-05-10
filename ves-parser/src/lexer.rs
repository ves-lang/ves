use logos::{
    internal::{CallbackResult, LexerInternal},
    Logos,
};
use std::borrow::Cow;
use std::convert::Into;

use ast2str::AstToStr;

pub use logos::Span;

pub type Lexer<'a> = logos::Lexer<'a, TokenKind<'a>>;

#[derive(Clone, Debug, PartialEq, Eq, AstToStr)]
pub struct Token<'a> {
    #[forward]
    /// Slice of the source from which this token was parsed
    pub lexeme: Cow<'a, str>,
    /// Start+end range of this token in the line where it was parsed
    pub span: Span,
    /// The token kind which optionally also contains extra
    pub kind: TokenKind<'a>,
}

impl<'a> std::hash::Hash for Token<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.lexeme.hash(state);
        self.span.hash(state);
    }
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

#[derive(Clone, Debug, PartialEq, Eq, Hash, Logos)]
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
    LeftBrace,
    #[token("}")]
    RightBrace,
    #[token("[")]
    LeftBracket,
    #[token("]")]
    RightBracket,
    #[token(":")]
    Colon,
    #[token(",")]
    Comma,
    #[token(";")]
    Semi,
    #[token("=")]
    Equal,
    #[token("++")]
    Increment,
    #[token("--")]
    Decrement,
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
    /// An normal identifier prefixed with an `@` sign.
    #[regex("@[a-zA-Z_][a-zA-Z0-9_]*")]
    AtIdentifier,
    #[token("..")]
    #[token("..=")]
    Range,
    /// Interpolated string
    ///
    /// e.g. `f"fragment {expr}"` `f"\{escaped}"`
    #[regex(r#"f""#, interpolated_string)]
    #[regex(r#"f'"#, interpolated_string)]
    InterpolatedString(InterpolatedString<'a>),
    /// String literal
    #[regex("\"([^\"\\\\]|\\\\.)*\"")]
    #[regex("'([^'\\\\]|\\\\.)*'")]
    String,
    /// Floating point (IEEE754) numeric literal
    /// TODO: underscores
    /// TODO: allow '0.' and '.0' in a way that is not ambiguous with ranges
    #[regex(
        "([0-9]+[Ee][+-]?[0-9]+|([0-9]+\\.[0-9]+([Ee][+-]?[0-9]+)?))f?|NaN|inf",
        priority = 2
    )]
    #[regex("[0-9]+f")]
    Float,
    /// A hexadecimal integer literal, e.g. `0x123_ABC`.
    #[regex("0[xX][0-9a-fA-F][0-9a-fA-F_]*[0-9aA-fF]?")]
    HexInt,
    /// A binary integer literal, e.g. `0b010_110_111`.
    #[regex("0[bB][01][01_]*[01]?")]
    BinInt,
    /// A normal integer literal, e.g. `111_222_777`.
    #[regex("[0-9]([0-9_]*[0-9])?")]
    #[regex("[0-9]([0-9_]*[0-9])?i")]
    Integer,
    /// An arbitrary-length integer literal, e.g. `111_222_777n`.
    #[regex("[0-9]([0-9_]*[0-9])?n")]
    BigInt,
    /// An arbitrary-length binary integer literal, e.g. `0b000100101n`.
    #[regex("0[xX][0-9a-fA-F][0-9a-fA-F_]*[0-9aA-fF]?n")]
    BigHexInt,
    /// An arbitrary-length hexadecimal integer literal, e.g. `0xFFFFFFFFn`.
    #[regex("0[bB][01][01_]*[01]?n")]
    BigBinInt,
    /// No value (same as nil/null)
    #[token("none")]
    None,
    /// Represents the concept of any value other than `none`
    ///
    /// Not an actual value, only used in `is some` checks
    #[token("some")]
    Some,
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
    /// Alias
    #[token("as")]
    As,
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
    /// Import
    #[token("import")]
    Import,
    /// Export
    #[token("export")]
    Export,
    /// Destructured import paths
    #[token("from")]
    From,
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
    let mut previous_two = [b'/', b'*'];
    for ch in lex.remainder().bytes() {
        n += 1;
        previous_two[0] = previous_two[1];
        previous_two[1] = ch;
        match previous_two {
            [b'/', b'*'] => opening_count += 1,
            [b'*', b'/'] => {
                // closing
                opening_count -= 1;
                if opening_count == 0 {
                    break;
                }
            }
            _ => (),
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
    /// An executable interpolated fragment.
    Sublexer(logos::Lexer<'a, TokenKind<'a>>),
}

impl<'a> std::hash::Hash for Frag<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Frag::Str(t) => t.hash(state),
            Frag::Sublexer(l) => {
                l.source().hash(state);
                l.span().hash(state);
            }
        }
    }
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
            (_, _) => true,
        }
    }
}
impl<'a> Eq for Frag<'a> {}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum InterpolatedStringState {
    Closed,
    MissingQuote,
    MissingBrace,
}
impl Default for InterpolatedStringState {
    fn default() -> Self {
        InterpolatedStringState::Closed
    }
}

#[derive(Default, Clone, Debug, PartialEq, Eq, Hash)]
pub struct InterpolatedString<'a> {
    /// The fragments that make up this interpolated string.
    pub fragments: Vec<Frag<'a>>,
    /// The state at which the lexer left the string.
    ///
    /// This is used to report a more specific error in case a fragment's
    /// closing brace or the entire string's closing quote is missing
    pub state: InterpolatedStringState,
}

impl<'a> InterpolatedString<'a> {
    #[inline]
    pub fn error(&self) -> Option<&'static str> {
        match self.state {
            InterpolatedStringState::Closed => None,
            InterpolatedStringState::MissingQuote => {
                Some("This interpolated string is missing a closing quote")
            }
            InterpolatedStringState::MissingBrace => {
                Some("One of this interpolated string's fragments is missing a closing brace")
            }
        }
    }
}

fn interpolated_string<'a>(lex: &mut logos::Lexer<'a, TokenKind<'a>>) -> InterpolatedString<'a> {
    let quote_kind = lex.slice().chars().nth(1).unwrap() as u8;
    let mut fragments = vec![];

    let remainder = lex.remainder();
    let bytes = remainder.as_bytes();
    let mut previous_fragment_end = 0;
    let mut state = InterpolatedStringState::MissingQuote;
    let mut bump_count = 0;
    for (i, byte) in bytes.iter().enumerate() {
        // we just parsed a fragment and need to catch up to where it stopped parsing
        if i < previous_fragment_end {
            continue;
        }

        bump_count = i;
        match byte {
            c if c == &quote_kind => {
                if previous_fragment_end < i {
                    // + 1 to skip the backslash (\)
                    let span = (previous_fragment_end + 1)..i;
                    let remainder = &remainder[span.clone()];
                    if !remainder.is_empty() {
                        fragments.push(Frag::Str(Token::new(remainder, span, TokenKind::String)));
                    }
                }
                state = InterpolatedStringState::Closed;
                break;
            }
            b'{' if bytes.get(i - 1) != Some(&b'\\') => {
                let span = if previous_fragment_end != 0 {
                    (previous_fragment_end + 1)..i
                } else {
                    0..i
                };
                fragments.push(Frag::Str(Token::new(
                    &remainder[span.clone()],
                    span,
                    TokenKind::String,
                )));

                let mut unclosed_braces = 1;
                // + 1 to skip opening brace
                let fragment_start = i + 1;
                let fragment_bytes = (&remainder[fragment_start..]).as_bytes();
                let mut fragment_end = 0;
                for (fi, byte) in fragment_bytes.iter().enumerate() {
                    fragment_end = fragment_start + fi;
                    match byte {
                        b'{' => unclosed_braces += 1,
                        b'}' => {
                            unclosed_braces -= 1;
                            if unclosed_braces == 0 {
                                break;
                            }
                        }
                        _ => (),
                    }
                }
                if unclosed_braces != 0 {
                    lex.bump(fragment_end + 1);
                    return InterpolatedString {
                        fragments: vec![],
                        state: InterpolatedStringState::MissingBrace,
                    };
                } else {
                    fragments.push(Frag::Sublexer(TokenKind::lexer(
                        &remainder[fragment_start..fragment_end],
                    )));
                }
                previous_fragment_end = fragment_end;
            }
            _ => (),
        }
    }

    lex.bump(bump_count + 1);

    InterpolatedString {
        fragments: if state == InterpolatedStringState::Closed {
            fragments
        } else {
            vec![]
        },
        state,
    }
}

// Adapted from https://docs.rs/snailquote/0.3.0/x86_64-pc-windows-msvc/src/snailquote/lib.rs.html.
/// Unescapes the given string in-place. Returns `None` if the string contains an invalid escape sequence.
pub(crate) fn unescape_in_place(s: &mut String) -> Option<()> {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(ch) = chars.next() {
        if ch == '\\' {
            if let Some(next) = chars.next() {
                let escape = match next {
                    'a' => Some('\u{07}'),
                    'b' => Some('\u{08}'),
                    'v' => Some('\u{0B}'),
                    'f' => Some('\u{0C}'),
                    'n' => Some('\n'),
                    'r' => Some('\r'),
                    't' => Some('\t'),
                    'e' | 'E' => Some('\u{1B}'),
                    'u' => Some(parse_unicode(&mut chars)?),
                    _ => None,
                };
                match escape {
                    Some(esc) => {
                        out.push(esc);
                    }
                    None => {
                        out.push(ch);
                        out.push(next);
                    }
                }
            }
        } else {
            out.push(ch);
        }
    }
    *s = out;
    Some(())
}

// Adapted from https://docs.rs/snailquote/0.3.0/x86_64-pc-windows-msvc/src/snailquote/lib.rs.html.
fn parse_unicode<I>(chars: &mut I) -> Option<char>
where
    I: Iterator<Item = char>,
{
    match chars.next() {
        Some('{') => {}
        _ => {
            return None;
        }
    }

    let unicode_seq: String = chars.take_while(|&c| c != '}').collect();

    u32::from_str_radix(&unicode_seq, 16)
        .ok()
        .and_then(char::from_u32)
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
                token!(Integer, "0"), token!(Range, ".."), token!(Integer, "0"),
                token!(Integer, "0"), token!(Range, "..="), token!(Integer, "0"),
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
                token!(Float, "0.0"), token!(Range, ".."), token!(Float, "1.0")
            ]
        );
    }

    #[test]
    fn simple_range() {
        const SOURCE: &str = r#"0..1"#;
        assert_eq!(
            test_tokenize(SOURCE),
            vec![
                token!(Integer, "0"), token!(Range, ".."), token!(Integer, "1")
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
                token!(AtIdentifier, "@label"), token!(Colon, ":"),
                token!(Loop, "loop"), token!(LeftBrace, "{"), token!(RightBrace, "}"),
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
        const SOURCE: &str = r#" f"1 + 1 = {1 + 1}""#;
        let mut actual = test_tokenize(SOURCE);
        //println!("{:#?}", actual);
        assert_eq!(actual.len(), 1);
        if let TokenKind::InterpolatedString(fstr) = &mut actual[0].kind {
            assert!(fstr.error().is_none());
            assert_eq!(fstr.fragments.len(), 2);
            if let Frag::Str(token) = &fstr.fragments[0] {
                assert_eq!(TestToken(token.clone()), token!(String, "1 + 1 = "));
            }
            if let Frag::Sublexer(lex) = &mut fstr.fragments[1] {
                let actual_inner = test_tokenize_inner(lex);
                //println!("{:#?}", actual_inner);
                assert_eq!(
                    actual_inner,
                    vec![
                        token!(Integer, "1"), token!(Plus, "+"), token!(Integer, "1"),
                    ]
                );
            }
        } else {
            assert_eq!("TokenKind was not InterpolatedString", "");
        }
    }

    #[test]
    fn string_interpolation_nested_block() {
        const SOURCE: &str = r#"f"a { do { "nested block" } }""#;
        let mut actual = test_tokenize(SOURCE);
        //println!("{:#?}", actual);
        assert_eq!(actual.len(), 1);
        if let TokenKind::InterpolatedString(fstr) = &mut actual[0].kind {
            assert!(fstr.error().is_none());
            assert_eq!(fstr.fragments.len(), 2);
            assert!(matches!(&fstr.fragments[0], Frag::Str(..)));
            if let Frag::Str(token) = &fstr.fragments[0] {
                assert_eq!(TestToken(token.clone()), token!(String, "a "));
            }
            assert!(matches!(&fstr.fragments[1], Frag::Sublexer(..)));
            if let Frag::Sublexer(lex) = &mut fstr.fragments[1] {
                let actual_inner = test_tokenize_inner(lex);
                //println!("{:#?}", actual_inner);
                assert_eq!(
                    actual_inner,
                    vec![
                        token!(Do, "do"), token!(LeftBrace, "{"), token!(String, "\"nested block\""), token!(RightBrace, "}")
                    ]
                );
            }
        } else {
            panic!("TokenKind was not InterpolatedString");
        }
    }

    #[test]
    fn string_interpolation_escape() {
        const SOURCE: &str = r#"f"\{escaped}""#;
        let actual = test_tokenize(SOURCE);
        //println!("{:#?}", actual);
        assert_eq!(
            actual,
            vec![
                TestToken(Token::new(r#"f"\{escaped}""#, 0..1, TokenKind::InterpolatedString(InterpolatedString {
                    fragments: vec![
                        Frag::Str(Token::new(r#"{escaped}"#, 0..1, TokenKind::String))
                    ],
                    state: InterpolatedStringState::Closed
                })))
            ]
        );
    }

    #[test]
    fn string_interpolation_unterminated_fragment() {
        const SOURCE: &str = r#"f"an {unterminated fragment""#;
        let actual = test_tokenize(SOURCE);
        //println!("{:#?}", actual);
        assert_eq!(
            actual,
            vec![
                TestToken(Token::new(r#"f"an {unterminated fragment""#, 0..28, TokenKind::InterpolatedString(InterpolatedString {
                    fragments: vec![],
                    state: InterpolatedStringState::MissingBrace
                })))
            ]
        );
    }

    #[test]
    fn string_interpolation_unclosed_quote() {
        const SOURCE: &str = r#"f"test"#;
        let actual = test_tokenize(SOURCE);
        //println!("{:#?}", actual);
        assert_eq!(
            actual,
            vec![
                TestToken(Token::new(r#"f"test"#, 0..6, TokenKind::InterpolatedString(InterpolatedString {
                    fragments: vec![],
                    state: InterpolatedStringState::MissingQuote
                })))
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

    #[test]
    fn array() {
        const SOURCE: &str = r#"[0, "a", none, a]"#;
        assert_eq!(
            test_tokenize(SOURCE),
            vec![
                token!(LeftBracket, "["),
                token!(Integer, "0"),
                token!(Comma, ","),
                token!(String, "\"a\""),
                token!(Comma, ","),
                token!(None, "none"),
                token!(Comma, ","),
                token!(Identifier, "a"),
                token!(RightBracket, "]"),
            ]
        );
    }

    #[test]
    fn import_and_export() {
        const SOURCE: &str = r#"
        import thing
        export let v = 0
        "#;
        assert_eq!(
            test_tokenize(SOURCE),
            vec![
                token!(Import, "import"),
                token!(Identifier, "thing"),
                token!(Export, "export"),
                token!(Let, "let"),
                token!(Identifier, "v"),
                token!(Equal, "="),
                token!(Integer, "0"),
            ]
        )
    }

    #[test]
    fn numeric_literals() {
        let source: &str = r#"123
        123_321
        1_2_3_4_5
        999_999_999
        999_999_999_999_999
        999_999_999_999_999_999_999

        1.0
        1e300

        1e300f
        100f
        100i
        100n
        
        0xABCDEF
        0xA_B_C_D_E_F
        0xDEAD_CAFE
        0x1_F331_D0D
        
        0b1111_0000_0101_1010_1100_0011
        0b000000
        0b111111

        0b000000000n
        0x000000000n
"#;
        assert_eq!(
            test_tokenize(source),
            vec![
                token!(Integer, "123"),
                token!(Integer, "123_321"),
                token!(Integer, "1_2_3_4_5"),
                token!(Integer, "999_999_999"),
                token!(Integer, "999_999_999_999_999"),
                token!(Integer, "999_999_999_999_999_999_999"),
                token!(Float, "1.0"),
                token!(Float, "1e300"),
                token!(Float, "1e300f"),
                token!(Float, "100f"),
                token!(Integer, "100i"),
                token!(BigInt, "100n"),
                token!(HexInt, "0xABCDEF"),
                token!(HexInt, "0xA_B_C_D_E_F"),
                token!(HexInt, "0xDEAD_CAFE"),
                token!(HexInt, "0x1_F331_D0D"),
                token!(BinInt, "0b1111_0000_0101_1010_1100_0011"),
                token!(BinInt, "0b000000"),
                token!(BinInt, "0b111111"),
                token!(BigBinInt, "0b000000000n"),
                token!(BigHexInt, "0x000000000n"),
            ]
        )
    }
}
