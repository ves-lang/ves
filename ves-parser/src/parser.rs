use crate::{
    ast::{self, StmtKind, AST},
    lexer::{Lexer, NextTokenExt, Token, TokenKind},
};
use logos::Lexer as RawLexer;
use std::convert::Into;
use ves_error::{ErrCtx, FileId, VesError, VesErrorKind};

/// Creates an AST literal node from the provided LitValue
macro_rules! literal {
    ($parser:ident, $value:expr) => {
        ast::Expr {
            span: $parser.previous.span.clone(),
            kind: ast::ExprKind::Lit(box ast::Lit {
                token: $parser.previous.clone(),
                value: $value,
            }),
        }
    };
}

/// Creates an AST binary expression
macro_rules! binary {
    ($left:ident, $op:ident, $right:ident) => {
        ast::Expr {
            span: $left.span.start..$right.span.end,
            kind: ast::ExprKind::Binary(ast::BinOpKind::$op, box $left, box $right),
        }
    };
}

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
        if self.match_(&TokenKind::LeftBracket) {
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
        // if the next token is a RightBracket, the block is empty
        if !self.check(&TokenKind::RightBracket) {
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
        self.consume(
            &TokenKind::RightBracket,
            "Expected closing '}' after a block",
        )?;

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
        match &self.current.kind {
            &TokenKind::Struct => unimplemented!(), /* self.struct_decl() */
            &TokenKind::Fn => unimplemented!(),     /* self.fn_decl() */
            &TokenKind::If => unimplemented!(),     /* self.if_expr() */
            &TokenKind::Do => unimplemented!(),     /* self.do_block() */
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
            return Ok(match &expr.kind {
                // x = <expr>
                &ast::ExprKind::Variable(ref token) => ast::Expr {
                    kind: ast::ExprKind::Assignment(box ast::Assignment {
                        name: token.clone(),
                        value: desugar_assignment(operator, expr.clone(), self.assignment()?),
                    }),
                    span: span_start..self.current.span.end,
                },
                // x[<expr>] = <expr>
                &ast::ExprKind::GetItem(ref node, ref key) => ast::Expr {
                    kind: ast::ExprKind::SetItem(box ast::SetItem {
                        node: (*node.clone()),
                        key: (*key.clone()),
                        value: desugar_assignment(operator, expr.clone(), self.assignment()?),
                    }),
                    span: span_start..self.current.span.end,
                },
                // x.key = <expr>
                // except x?.key = <expr>
                &ast::ExprKind::GetProp(ref prop) if !prop.is_optional => ast::Expr {
                    kind: ast::ExprKind::SetProp(box ast::SetProp {
                        node: prop.node.clone(),
                        field: prop.field.clone(),
                        value: desugar_assignment(operator, expr.clone(), self.assignment()?),
                    }),
                    span: span_start..self.current.span.end,
                },
                _ => {
                    return Err(VesError::parse(
                        "Invalid assignment target",
                        span_start..self.current.span.end,
                        self.fid.clone(),
                    ))
                }
            });
        }

        Ok(expr)
    }

    fn or(&mut self) -> ParseResult<ast::Expr<'a>> {
        let expr = self.and()?;
        if self.match_(&TokenKind::Or) {
            let op = self.previous.clone();
            let right = self.and()?;
            return Ok(binary!(expr, Or, right));
        }

        Ok(expr)
    }

    fn and(&mut self) -> ParseResult<ast::Expr<'a>> {
        let expr = self.equality()?;

        Ok(expr)
    }

    fn equality(&mut self) -> ParseResult<ast::Expr<'a>> {
        let expr = self.comparison()?;

        Ok(expr)
    }

    fn comparison(&mut self) -> ParseResult<ast::Expr<'a>> {
        let expr = self.term()?;

        Ok(expr)
    }

    fn term(&mut self) -> ParseResult<ast::Expr<'a>> {
        let expr = self.factor()?;

        Ok(expr)
    }

    fn factor(&mut self) -> ParseResult<ast::Expr<'a>> {
        let expr = self.power()?;

        Ok(expr)
    }

    fn power(&mut self) -> ParseResult<ast::Expr<'a>> {
        let expr = self.unary()?;

        Ok(expr)
    }

    fn unary(&mut self) -> ParseResult<ast::Expr<'a>> {
        self.call()
    }

    fn call(&mut self) -> ParseResult<ast::Expr<'a>> {
        let mut expr = self.primary()?;

        Ok(expr)
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
                        self.fid.clone(),
                    )
                })?)
            ));
        }
        // string literal
        if self.match_(&TokenKind::String) {
            let str_token = self.previous.clone();
            return Ok(literal!(self, ast::LitValue::Str(str_token.lexeme.into())));
        }
        // array literal
        if self.match_(&TokenKind::LeftBrace) {
            let span_start = self.previous.span.start;
            let mut exprs = vec![];
            while !self.at_end() && !self.check(&TokenKind::RightBrace) {
                exprs.push(self.expr()?);
            }
            self.consume(&TokenKind::RightBrace, "Expected closing ']'")?;
            let span_end = self.current.span.end;
            return Ok(ast::Expr {
                kind: ast::ExprKind::Array(exprs),
                span: span_start..span_end,
            });
        }
        // map literals (JS-style object literals)
        if self.match_(&TokenKind::LeftBracket) {
            let span_start = self.previous.span.start;
            let mut pairs = vec![];
            while !self.at_end() && !self.check(&TokenKind::RightBracket) {
                let mut identifier = None;
                let key = if self.match_(&TokenKind::Identifier) {
                    // simple keys may be identifiers
                    let key_token = self.previous.clone();
                    identifier = Some(key_token.clone());
                    literal!(self, ast::LitValue::Str(key_token.lexeme.into()))
                } else {
                    // keys may also be expressions wrapped in []
                    self.consume(&TokenKind::LeftBrace, "Expected '[' before key expression")?;
                    let key = self.expr()?;
                    self.consume(&TokenKind::RightBrace, "Expected ']' after key expression")?;
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
                        self.fid.clone(),
                    ));
                };
                pairs.push((key, value));
            }
            self.consume(&TokenKind::RightBracket, "Expected closing '}'")?;
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
            self.consume(&TokenKind::RightParen, "Expected closing ')'")?;
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
                self.fid.clone(),
            ));
        }
        Err(VesError::parse(
            format!("Unexpected token {:?}", self.previous.clone()),
            self.current.span.clone(),
            self.fid.clone(),
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
                TokenKind::LeftBrace,
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

    // TODO: assert errors, too
    // TODO: spans may be wrong

    macro_rules! assert_ast {
        ($source:expr, $expected:expr) => {
            pretty_assertions::assert_eq!(
                Parser::new(Lexer::new($source), FileId::anon())
                    .parse()
                    .unwrap()
                    .body,
                $expected
            )
        };
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
        const SOURCE: &str = "0, 0, 0";
        assert_ast!(
            SOURCE,
            vec![ast::Stmt {
                span: 6..6,
                kind: ast::StmtKind::ExprStmt(box ast::Expr {
                    span: 6..6,
                    kind: ast::ExprKind::Comma(vec![
                        ast::Expr {
                            kind: ast::ExprKind::Lit(box ast::Lit {
                                token: Token::new("0", 0..1, TokenKind::Number),
                                value: ast::LitValue::Number(0f64)
                            }),
                            span: 0..1
                        },
                        ast::Expr {
                            kind: ast::ExprKind::Lit(box ast::Lit {
                                token: Token::new("0", 3..4, TokenKind::Number),
                                value: ast::LitValue::Number(0f64)
                            }),
                            span: 3..4
                        },
                        ast::Expr {
                            kind: ast::ExprKind::Lit(box ast::Lit {
                                token: Token::new("0", 6..7, TokenKind::Number),
                                value: ast::LitValue::Number(0f64)
                            }),
                            span: 6..7
                        },
                    ])
                })
            }]
        )
    }

    #[test]
    fn parse_binary_or() {
        const SOURCE: &str = "0 || 0";
        assert_ast!(
            SOURCE,
            vec![ast::Stmt {
                kind: ast::StmtKind::ExprStmt(box ast::Expr {
                    kind: ast::ExprKind::Binary(
                        ast::BinOpKind::Or,
                        box ast::Expr {
                            kind: ast::ExprKind::Lit(box ast::Lit {
                                token: Token::new("0", 0..1, TokenKind::Number),
                                value: ast::LitValue::Number(0f64),
                            }),
                            span: 0..1
                        },
                        box ast::Expr {
                            kind: ast::ExprKind::Lit(box ast::Lit {
                                token: Token::new("0", 5..6, TokenKind::Number),
                                value: ast::LitValue::Number(0f64),
                            }),
                            span: 5..6
                        }
                    ),
                    span: 0..6
                }),
                span: 5..5
            }]
        )
    }

    /*
    TODO: test these
    none
    true
    false
    self
    "string"
    1.0e-5
    [1.0, "a", true]
    { test }
    { test: 1.0 }
    { ["test"]: 1.0 }
    a += 5
    a += 5
    a[0] += 5
    a.b += 5
    */
}
