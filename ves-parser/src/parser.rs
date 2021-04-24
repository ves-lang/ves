use crate::{
    ast::{self, StmtKind, AST},
    lexer::{self, Lexer, NextTokenExt, Token, TokenKind},
};
use std::convert::Into;
use ves_error::{ErrCtx, FileId, VesError};

type ParseResult<T> = std::result::Result<T, VesError>;

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    previous: Token<'a>,
    current: Token<'a>,
    eof: Token<'a>,
    ex: ErrCtx,
    fid: FileId,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>, fid: FileId) -> Parser<'a> {
        let source = lexer.source();
        let end = if source.is_empty() {
            0
        } else {
            source.len() - 1
        };
        let eof = Token::new("", end..end, TokenKind::EOF);

        Parser {
            lexer,
            previous: eof.clone(),
            current: eof.clone(),
            eof,
            ex: ErrCtx::new(),
            fid,
        }
    }

    pub fn parse(mut self) -> Result<AST<'a>, ErrCtx> {
        self.advance();
        let mut body = vec![];
        while !self.at_end() {
            match self.stmt() {
                Ok(stmt) => body.push(stmt),
                Err(e) => {
                    self.ex.record(e);
                    self.synchronize();
                }
            }
        }

        if self.ex.had_error() {
            Err(self.ex)
        } else {
            Ok(AST::new(body, self.fid))
        }
    }

    fn stmt(&mut self) -> ParseResult<ast::Stmt<'a>> {
        if self.match_(&TokenKind::LeftBrace) {
            self.block()
            // TODO: here
        }
        /* else if self.match_(&Print) {
            self.print_statement()
        }
        else if self.match_(&Loop) {
            self.loop_statement();
        } else if self.match_(&For) {
            self.for_statement();
        } else if self.match_(&While) {
            self.while_statement();
        } else if self.match_(&Break) {
            self.break_statement();
        } else if self.match_(&Continue) {
            self.continue_statement();
        } else if self.match_(&Defer) {
            self.defer_statement();
        } else if self.match_(&Return) {
            self.return_statement();
        }*/
        else {
            self.expr_stmt()
        }
    }

    fn block(&mut self) -> ParseResult<ast::Stmt<'a>> {
        let span_start = self.previous.span.start;
        let mut body = vec![];
        // if the next token is a RightBrace, the block is empty
        if !self.check(&TokenKind::RightBrace) {
            while !self.at_end() {
                match self.stmt() {
                    Ok(stmt) => body.push(stmt),
                    Err(e) => {
                        self.ex.record(e);
                        self.synchronize();
                    }
                }
            }
        }
        self.consume(&TokenKind::RightBrace, "Expected '}' after a block")?;

        let span_end = self.current.span.end;
        Ok(ast::Stmt {
            kind: StmtKind::Block(body),
            span: span_start..span_end,
        })
    }

    fn expr_stmt(&mut self) -> ParseResult<ast::Stmt<'a>> {
        let span_start = self.previous.span.start;
        let expr = self.comma()?;
        let span_end = self.current.span.end;

        self.skip_semi();

        Ok(ast::Stmt {
            kind: ast::StmtKind::ExprStmt(Box::new(expr)),
            span: span_start..span_end,
        })
    }

    fn comma(&mut self) -> ParseResult<ast::Expr<'a>> {
        let span_start = self.previous.span.start;
        let mut exprs = vec![self.expr()?];
        while self.match_(&TokenKind::Comma) {
            exprs.push(self.expr()?);
        }
        let span_end = self.current.span.end;

        if exprs.len() == 1 {
            Ok(exprs.pop().unwrap())
        } else {
            Ok(ast::Expr {
                kind: ast::ExprKind::Comma(exprs),
                span: span_start..span_end,
            })
        }
    }

    fn expr(&mut self) -> ParseResult<ast::Expr<'a>> {
        match self.current.kind {
            TokenKind::Struct => unimplemented!(), /* self.struct_decl() */
            TokenKind::Fn => unimplemented!(),     /* self.fn_decl() */
            TokenKind::If => unimplemented!(),     /* self.if_expr() */
            TokenKind::Do => unimplemented!(),     /* self.do_block() */
            _ => self.assignment(),
        }
    }

    // TODO: is precedence wrong?
    fn assignment(&mut self) -> ParseResult<ast::Expr<'a>> {
        let expr = self.or()?;
        if self.match_any(&[
            TokenKind::Equal,
            TokenKind::OrEqual,
            TokenKind::AndEqual,
            TokenKind::PlusEqual,
            TokenKind::MinusEqual,
            TokenKind::StarEqual,
            TokenKind::SlashEqual,
            TokenKind::PowerEqual,
            TokenKind::PercentEqual,
        ]) {
            let operator = self.previous.clone();
            let span_start = self.current.span.start;
            return Ok(match expr.kind {
                // x = <expr>
                ast::ExprKind::Variable(ref token) => ast::Expr {
                    kind: ast::ExprKind::Assignment(box ast::Assignment {
                        name: token.clone(),
                        value: desugar_assignment(operator, expr.clone(), self.assignment()?),
                    }),
                    span: span_start..self.current.span.end,
                },
                // x[<expr>] = <expr>
                ast::ExprKind::GetItem(ref get) => ast::Expr {
                    kind: ast::ExprKind::SetItem(box ast::SetItem {
                        node: get.node.clone(),
                        key: get.key.clone(),
                        value: desugar_assignment(operator, expr.clone(), self.assignment()?),
                    }),
                    span: span_start..self.current.span.end,
                },
                // x.key = <expr>
                // except x?.key = <expr>
                ast::ExprKind::GetProp(ref get) if !get.is_optional => ast::Expr {
                    kind: ast::ExprKind::SetProp(box ast::SetProp {
                        node: get.node.clone(),
                        field: get.field.clone(),
                        value: desugar_assignment(operator, expr.clone(), self.assignment()?),
                    }),
                    span: span_start..self.current.span.end,
                },
                _ => {
                    return Err(VesError::parse(
                        "Invalid assignment target",
                        span_start..self.current.span.end,
                        self.fid,
                    ))
                }
            });
        }
        Ok(expr)
    }

    fn or(&mut self) -> ParseResult<ast::Expr<'a>> {
        let mut expr = self.and()?;
        // expr || expr
        while self.match_(&TokenKind::Or) {
            expr = binary!(expr, Or, self.and()?);
        }
        Ok(expr)
    }

    fn and(&mut self) -> ParseResult<ast::Expr<'a>> {
        let mut expr = self.equality()?;
        // expr && expr
        while self.match_(&TokenKind::And) {
            expr = binary!(expr, And, self.equality()?);
        }
        Ok(expr)
    }

    fn equality(&mut self) -> ParseResult<ast::Expr<'a>> {
        let mut expr = self.comparison()?;
        // expr != expr
        // expr == expr
        while self.match_any(&[TokenKind::BangEqual, TokenKind::EqualEqual]) {
            expr = match self.previous.kind {
                TokenKind::EqualEqual => binary!(expr, Eq, self.comparison()?),
                TokenKind::BangEqual => binary!(expr, Ne, self.comparison()?),
                _ => unreachable!(),
            };
        }
        Ok(expr)
    }

    fn comparison(&mut self) -> ParseResult<ast::Expr<'a>> {
        let mut expr = self.term()?;
        // expr > expr
        // expr < expr
        // expr >= expr
        // expr <= expr
        while self.match_any(&[
            TokenKind::More,
            TokenKind::Less,
            TokenKind::MoreEqual,
            TokenKind::LessEqual,
        ]) {
            expr = match self.previous.kind {
                TokenKind::More => binary!(expr, Gt, self.comparison()?),
                TokenKind::Less => binary!(expr, Lt, self.comparison()?),
                TokenKind::MoreEqual => binary!(expr, Ge, self.comparison()?),
                TokenKind::LessEqual => binary!(expr, Le, self.comparison()?),
                _ => unreachable!(),
            };
        }
        Ok(expr)
    }

    fn term(&mut self) -> ParseResult<ast::Expr<'a>> {
        let mut expr = self.factor()?;
        // expr - expr
        // expr + expr
        while self.match_any(&[TokenKind::Minus, TokenKind::Plus]) {
            expr = match self.previous.kind {
                TokenKind::Minus => binary!(expr, Sub, self.factor()?),
                TokenKind::Plus => binary!(expr, Add, self.factor()?),
                _ => unreachable!(),
            };
        }
        Ok(expr)
    }

    fn factor(&mut self) -> ParseResult<ast::Expr<'a>> {
        let mut expr = self.power()?;
        // expr * expr
        // expr / expr
        while self.match_any(&[TokenKind::Star, TokenKind::Slash]) {
            expr = match self.previous.kind {
                TokenKind::Star => binary!(expr, Mul, self.power()?),
                TokenKind::Slash => binary!(expr, Div, self.power()?),
                _ => unreachable!(),
            }
        }
        Ok(expr)
    }

    fn power(&mut self) -> ParseResult<ast::Expr<'a>> {
        let mut expr = self.unary()?;
        // expr ** expr
        while self.match_(&TokenKind::Power) {
            expr = binary!(expr, Pow, self.power()?);
        }
        Ok(expr)
    }

    fn unary(&mut self) -> ParseResult<ast::Expr<'a>> {
        if self.match_any(&[
            TokenKind::Bang,
            TokenKind::Minus,
            TokenKind::Try,
            TokenKind::Ok,
            TokenKind::Err,
            TokenKind::Ellipsis,
            TokenKind::Increment,
            TokenKind::Decrement,
        ]) {
            let op = self.previous.clone();
            return Ok(match self.previous.kind {
                // !<expr>
                TokenKind::Bang => unary!(Not, self.unary()?, op),
                // -<expr>
                TokenKind::Minus => unary!(Neg, self.unary()?, op),
                // try <expr>
                TokenKind::Try => unary!(Try, self.unary()?, op),
                // ok <expr>
                TokenKind::Ok => unary!(Ok, self.unary()?, op),
                // err <expr>
                TokenKind::Err => unary!(Err, self.unary()?, op),
                // ++<expr> or --<expr>
                TokenKind::Increment | TokenKind::Decrement => {
                    let kind = self.previous.kind.clone();
                    let expr = self.call()?;
                    ast::Expr {
                        span: op.span.start..expr.span.end,
                        kind: ast::ExprKind::PrefixIncDec(box ast::IncDec {
                            expr,
                            kind: ast::IncDecKind::from(kind),
                        }),
                    }
                }
                // QQQ(moscow): should this be here?
                // ...<expr>
                TokenKind::Ellipsis => {
                    let expr = self.unary()?;
                    ast::Expr {
                        span: op.span.start..expr.span.end,
                        kind: ast::ExprKind::Spread(box expr),
                    }
                }
                _ => unreachable!(),
            });
        }

        let mut expr = self.call()?;

        if self.match_any(&[TokenKind::Increment, TokenKind::Decrement]) {
            let kind = self.previous.kind.clone();
            expr = ast::Expr {
                span: expr.span.start..self.previous.span.end,
                kind: ast::ExprKind::PostfixIncDec(box ast::IncDec {
                    expr,
                    kind: ast::IncDecKind::from(kind),
                }),
            }
        }

        Ok(expr)
    }

    fn call(&mut self) -> ParseResult<ast::Expr<'a>> {
        let mut expr = self.primary()?;
        while self.match_any(&[
            TokenKind::LeftParen,
            TokenKind::Dot,
            TokenKind::MaybeDot,
            TokenKind::LeftBracket,
            TokenKind::Increment,
            TokenKind::Decrement,
        ]) {
            expr = match self.previous.kind {
                TokenKind::LeftParen => {
                    // TODO: tail call
                    let args = self.arg_list()?;
                    ast::Expr {
                        span: expr.span.start..self.previous.span.end,
                        kind: ast::ExprKind::Call(box ast::Call {
                            callee: box expr,
                            args,
                            tco: false,
                            rest: false,
                        }),
                    }
                }
                TokenKind::Dot => {
                    let field = self.consume(&TokenKind::Identifier, "Expected property name")?;
                    ast::Expr {
                        span: expr.span.start..self.previous.span.end,
                        kind: ast::ExprKind::GetProp(box ast::GetProp {
                            node: expr,
                            field,
                            is_optional: false,
                        }),
                    }
                }
                TokenKind::MaybeDot => {
                    let field = self.consume(&TokenKind::Identifier, "Expected property name")?;
                    ast::Expr {
                        span: expr.span.start..self.previous.span.end,
                        kind: ast::ExprKind::GetProp(box ast::GetProp {
                            node: expr,
                            field,
                            is_optional: true,
                        }),
                    }
                }
                TokenKind::LeftBracket => {
                    let key = self.expr()?;
                    self.consume(&TokenKind::RightBracket, "Expected ']'")?;
                    ast::Expr {
                        span: expr.span.start..self.previous.span.end,
                        kind: ast::ExprKind::GetItem(box ast::GetItem { node: expr, key }),
                    }
                }
                TokenKind::Increment => ast::Expr {
                    span: expr.span.start..self.previous.span.end,
                    kind: ast::ExprKind::PostfixIncDec(box ast::IncDec {
                        expr,
                        kind: ast::IncDecKind::Increment,
                    }),
                },
                TokenKind::Decrement => ast::Expr {
                    span: expr.span.start..self.previous.span.end,
                    kind: ast::ExprKind::PostfixIncDec(box ast::IncDec {
                        expr,
                        kind: ast::IncDecKind::Decrement,
                    }),
                },
                _ => unreachable!(),
            }
        }

        Ok(expr)
    }

    fn arg_list(&mut self) -> ParseResult<ast::Args<'a>> {
        // TODO: spread args
        let span_start = self.previous.span.start;
        let mut args = vec![];
        if !self.check(&TokenKind::RightParen) {
            loop {
                if args.len() == 255 {
                    return Err(VesError::parse(
                        "Too many arguments",
                        span_start..self.current.span.end,
                        self.fid,
                    ));
                }
                args.push(self.expr()?);
                if !self.match_(&TokenKind::Comma) {
                    break;
                }
            }
        }
        self.consume(&TokenKind::RightParen, "Expected ')'")?;
        Ok(args)
    }

    fn primary(&mut self) -> ParseResult<ast::Expr<'a>> {
        if self.match_(&TokenKind::None) {
            return Ok(literal!(self, ast::LitValue::None));
        }
        if self.match_(&TokenKind::True) {
            return Ok(literal!(self, ast::LitValue::Bool(true)));
        }
        if self.match_(&TokenKind::False) {
            return Ok(literal!(self, ast::LitValue::Bool(false)));
        }
        // 'self'
        if self.match_(&TokenKind::Self_) {
            return Ok(ast::Expr {
                span: self.previous.span.clone(),
                kind: ast::ExprKind::Variable(self.previous.clone()),
            });
        }
        // number literal
        if self.match_(&TokenKind::Number) {
            return Ok(literal!(
                self,
                ast::LitValue::Number(self.previous.lexeme.parse::<f64>().map_err(|_| {
                    VesError::parse(
                        "Failed to parse number",
                        self.previous.span.clone(),
                        self.fid,
                    )
                })?)
            ));
        }
        // string literal
        if self.match_(&TokenKind::String) {
            return Ok(literal!(
                self,
                ast::LitValue::Str(
                    self.previous
                        .lexeme
                        .trim_start_matches(|v| v == '"' || v == '\'')
                        .trim_end_matches(|v| v == '"' || v == '\'')
                        // QQQ(moscow): is there a way to avoid the string copy here?
                        .to_string()
                        .into()
                )
            ));
        }
        if self.match_(&TokenKind::InterpolatedString(vec![])) {
            // TODO: interpolated string
            let span_start = self.previous.span.start;
            let mut fragments = vec![];
            let previous = std::mem::replace(&mut self.previous, self.eof.clone());
            if let TokenKind::InterpolatedString(unprocessed) = previous.kind {
                for frag in unprocessed.into_iter() {
                    match frag {
                        lexer::Frag::Str(v) => fragments.push(ast::FStringFrag::Str(ast::Lit {
                            token: v.clone(),
                            value: ast::LitValue::Str(v.lexeme.clone()),
                        })),
                        lexer::Frag::Sublexer(sublexer) => {
                            let mut subparser = Parser::new(sublexer, self.fid);
                            subparser.advance();
                            fragments.push(ast::FStringFrag::Expr(subparser.expr()?));
                        }
                        lexer::Frag::UnterminatedFragment(frag) => {
                            return Err(VesError::parse(
                                "Unterminated fragment",
                                frag.span,
                                self.fid,
                            ));
                        }
                    }
                }
            }
            let span_end = self.current.span.end;
            return Ok(ast::Expr {
                span: span_start..span_end,
                kind: ast::ExprKind::FString(ast::FString { fragments }),
            });
        }
        // array literal
        if self.match_(&TokenKind::LeftBracket) {
            let span_start = self.previous.span.start;
            let mut exprs = vec![];
            while !self.at_end() && !self.check(&TokenKind::RightBracket) {
                exprs.push(self.expr()?);
            }
            self.consume(&TokenKind::RightBracket, "Expected ']'")?;
            let span_end = self.current.span.end;
            return Ok(ast::Expr {
                kind: ast::ExprKind::Array(exprs),
                span: span_start..span_end,
            });
        }
        // map literals (JS-style object literals)
        if self.match_(&TokenKind::LeftBrace) {
            let span_start = self.previous.span.start;
            let mut pairs = vec![];
            while !self.at_end() && !self.check(&TokenKind::RightBrace) {
                let mut identifier = None;
                let key = if self.match_(&TokenKind::Identifier) {
                    // simple keys may be identifiers
                    let key_token = self.previous.clone();
                    identifier = Some(key_token.clone());
                    literal!(self, ast::LitValue::Str(key_token.lexeme))
                } else {
                    // keys may also be expressions wrapped in []
                    self.consume(
                        &TokenKind::LeftBracket,
                        "Expected '[' before key expression",
                    )?;
                    let key = self.expr()?;
                    self.consume(
                        &TokenKind::RightBracket,
                        "Expected ']' after key expression",
                    )?;
                    key
                };

                let value = if self.match_(&TokenKind::Colon) {
                    self.expr()?
                } else if let Some(identifier) = identifier {
                    // if ':' is omitted, the value is the value bound to the identifier key
                    // which means the key must be a simple identifier
                    ast::Expr {
                        span: self.previous.span.clone(),
                        kind: ast::ExprKind::Variable(identifier),
                    }
                } else {
                    return Err(VesError::parse(
                        "Map entries without a value must have an identifier key",
                        self.previous.span.clone(),
                        self.fid,
                    ));
                };
                pairs.push((key, value));
            }
            self.consume(&TokenKind::RightBrace, "Expected '}'")?;
            let span_end = self.previous.span.end;
            return Ok(ast::Expr {
                kind: ast::ExprKind::Map(pairs),
                span: span_start..span_end,
            });
        }
        // grouping expr
        if self.match_(&TokenKind::LeftParen) {
            let span_start = self.previous.span.start;
            let expr = self.comma()?;
            self.consume(&TokenKind::RightParen, "Expected ')'")?;
            let span_end = self.previous.span.end;
            return Ok(ast::Expr {
                kind: ast::ExprKind::Grouping(box expr),
                span: span_start..span_end,
            });
        }
        if self.match_(&TokenKind::EOF) {
            return Err(VesError::parse(
                format!("Unexpected EOF at {:?}", self.previous.clone()),
                self.eof.span.clone(),
                self.fid,
            ));
        }
        Err(VesError::parse(
            format!("Unexpected token {:?}", self.previous.clone()),
            self.current.span.clone(),
            self.fid,
        ))
    }

    #[inline]
    fn skip_semi(&mut self) {
        while !self.at_end() && self.check(&TokenKind::Semi) {
            self.advance();
        }
    }

    #[inline]
    fn consume<S: Into<String>>(
        &mut self,
        kind: &TokenKind<'a>,
        err_msg: S,
    ) -> ParseResult<Token<'a>> {
        if self.check(kind) {
            Ok(self.advance())
        } else {
            Err(VesError::parse(
                err_msg,
                self.current.span.clone(),
                self.fid,
            ))
        }
    }

    #[inline]
    fn match_(&mut self, kind: &TokenKind<'a>) -> bool {
        if self.check(kind) {
            self.advance();
            true
        } else {
            false
        }
    }

    #[inline]
    fn match_any(&mut self, kinds: &[TokenKind<'a>]) -> bool {
        for kind in kinds {
            if self.check(kind) {
                self.advance();
                return true;
            }
        }
        false
    }

    #[inline(always)]
    fn check(&mut self, kind: &TokenKind<'a>) -> bool {
        std::mem::discriminant(kind) == std::mem::discriminant(&self.current.kind)
    }

    /// In case of an error, consume tokens until we reach one
    /// which has a high chance of beginning a new valid segment
    /// of the source code
    fn synchronize(&mut self) {
        self.advance();
        while !self.at_end()
            && self.previous.kind != TokenKind::Semi
            && !([
                TokenKind::Fn,
                TokenKind::Let,
                TokenKind::Mut,
                TokenKind::Loop,
                TokenKind::For,
                TokenKind::While,
                TokenKind::If,
                TokenKind::Return,
                TokenKind::Struct,
                TokenKind::LeftBracket,
                TokenKind::Print,
            ]
            .contains(&self.current.kind))
        {
            self.advance();
        }
    }

    /// Move to the next token
    #[inline]
    fn advance(&mut self) -> Token<'a> {
        std::mem::swap(&mut self.previous, &mut self.current);
        self.current = self.lexer.next_token().unwrap_or_else(|| self.eof.clone());
        self.current.clone()
    }

    /// Check if the parser has reached EOF
    #[inline(always)]
    fn at_end(&self) -> bool {
        self.current.kind == TokenKind::EOF
    }
}

fn desugar_assignment<'a>(
    which: Token<'a>,
    receiver: ast::Expr<'a>,
    value: ast::Expr<'a>,
) -> ast::Expr<'a> {
    // transforms e.g. `name += value` into `name = name + value`
    macro_rules! desugar {
        ($receiver:ident, $op:ident, $value:ident) => {
            ast::Expr {
                span: $receiver.span.start..$value.span.end,
                kind: ast::ExprKind::Binary(ast::BinOpKind::$op, box $receiver, box $value),
            }
        };
    }
    match which.kind {
        // no-op for `name = value`
        TokenKind::Equal => value,
        TokenKind::OrEqual => desugar!(receiver, Or, value),
        TokenKind::AndEqual => desugar!(receiver, And, value),
        TokenKind::PlusEqual => desugar!(receiver, Add, value),
        TokenKind::MinusEqual => desugar!(receiver, Sub, value),
        TokenKind::StarEqual => desugar!(receiver, Mul, value),
        TokenKind::SlashEqual => desugar!(receiver, Div, value),
        TokenKind::PowerEqual => desugar!(receiver, Pow, value),
        TokenKind::PercentEqual => desugar!(receiver, Rem, value),
        _ => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    use ast2str::ast2str_lib::symbols;
    use ast2str::AstToStr;
    use lazy_static::lazy_static;
    use regex::Regex;

    #[derive(Clone, PartialEq)]
    struct DisplayAsDebugWrapper<T>(T);

    impl<T> std::fmt::Debug for DisplayAsDebugWrapper<T>
    where
        T: std::fmt::Display,
    {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.0)
        }
    }

    impl<T> std::ops::Deref for DisplayAsDebugWrapper<T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }

    lazy_static! {
        static ref RE: Regex = Regex::new(
            &[
                symbols::HORIZONTAL_BAR,
                symbols::VERTICAL_BAR,
                symbols::BRANCH,
                symbols::LEFT_UPPER_CORNER,
                symbols::LEFT_BOTTOM_CORNER,
                symbols::RIGHT_UPPER_CORNER,
                symbols::RIGHT_BOTTOM_CORNER,
                symbols::CROSS,
                symbols::DOWNWARDS_POINTING_ARROW,
            ]
            .join("|")
        )
        .unwrap();
    }

    // TODO: assert errors, too
    // TODO: spans may be wrong

    macro_rules! assert_ast {
        ($source:expr, $expected:expr) => {
            pretty_assertions::assert_eq!(
                DisplayAsDebugWrapper(clean_tree(
                    Parser::new(Lexer::new($source), FileId::anon())
                        .parse()
                        .unwrap()
                        .body
                        .into_iter()
                        .map(|stmt| stmt.ast_to_str())
                        .collect::<Vec<_>>()
                        .join("\n")
                )),
                DisplayAsDebugWrapper($expected.trim_start().to_owned())
            )
        };
    }

    fn clean_tree(tree: String) -> String {
        RE.replace_all(&tree, " ")
            .lines()
            .map(|l| l.trim_end())
            .collect::<Vec<_>>()
            .join("\n")
    }

    #[test]
    fn parse_block() {
        const SOURCE: &str = "{ }";
        let parser = Parser::new(Lexer::new(SOURCE), FileId::anon());
        assert_eq!(
            parser.parse().unwrap().body,
            vec![ast::Stmt {
                kind: ast::StmtKind::Block(vec![]),
                span: 0..2
            }]
        );
    }

    #[test]
    fn parse_comma() {
        const SOURCE: &str = r#"1.0e-5, none, true, false, "string""#;
        assert_ast!(
            SOURCE,
            r#"
StmtKind::ExprStmt
  expr: ExprKind::Comma
    field0=
      Lit
        token: "1.0e-5"
        value: LitValue::Number
          field0: 0.00001
      Lit
        token: "none"
        value: LitValue::None
      Lit
        token: "true"
        value: LitValue::Bool
          field0: true
      Lit
        token: "false"
        value: LitValue::Bool
          field0: false
      Lit
        token: "\"string\""
        value: LitValue::Str
          field0: "string""#
        )
    }

    #[test]
    fn parse_binary_or() {
        const SOURCE: &str = "0 || 0";
        assert_ast!(
            SOURCE,
            r#"
StmtKind::ExprStmt
  expr: ExprKind::Binary
    op: Or
    left: Lit
      token: "0"
      value: LitValue::Number
        field0: 0
    right: Lit
      token: "0"
      value: LitValue::Number
        field0: 0"#
        );
    }

    /*
    TODO(jprochazk): test these
    [1.0, "a", true]
    { test }
    { test: 1.0 }
    { ["test"]: 1.0 }
    f"test"
    f"test{2+2}"
    ...a
    a(0, 0)
    a += 5
    a += 5
    a[0] += 5
    a.b += 5
    */
}
