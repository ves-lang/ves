use crate::{
    ast::{self, StmtKind, AST},
    lexer::{Lexer, NextTokenExt, Token, TokenKind},
};
use logos::Lexer as RawLexer;
use std::convert::Into;
use ves_error::{ErrCtx, FileId, VesError, VesErrorKind};

macro_rules! literal {
    ($self:ident, $value:expr) => {
        ast::Expr {
            span: self.previous.span.clone(),
            kind: ast::ExprKind::Lit(Box::new(ast::Lit {
                token: self.previous.token.clone(),
                value: $value,
            })),
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
        let exprs = vec![self.expr()?];
        while self.match_(&TokenKind::Comma) {
            exprs.push(self.expr()?);
        }
        let span_end = self.current.span.end;

        Ok(ast::Expr {
            kind: ast::ExprKind::Comma(expr),
            span: span_start..span_end,
        })
    }

    fn expr(&mut self) -> ParseResult<ast::Expr<'a>> {
        match &self.current {
            &TokenKind::Struct => unimplemented!(), /* self.struct_decl() */
            &TokenKind::Fn => unimplemented!(),     /* self.fn_decl() */
            &TokenKind::If => unimplemented!(),     /* self.if_expr() */
            &TokenKind::Do => unimplemented!(),     /* self.do_block() */
            _ => self.assignment(),
        }
    }

    fn assignment(&mut self) -> ParseResult<ast::Expr<'a>> {
        let expr = self.or()?;

        if self.match_(&TokenKind::Equal) {
            let span_start = self.current.span.start;
            let value = self.assignment();
            return Ok(match expr.kind {
                // x = <expr>
                ast::ExprKind::Variable(token) => ast::Expr {
                    kind: ast::ExprKind::Assignment(ast::Assignment { name: token, value }),
                    span: span_start..self.current.span.end,
                },
                // x[<expr>] = <expr>
                ast::ExprKind::GetItem(node, key) => ast::Expr {
                    kind: ast::ExprKind::SetItem(ast::SetItem { node, key, value }),
                    span: span_start..self.current.span.end,
                },
                // x.key = <expr>
                // except x?.key = <expr>
                ast::ExprKind::GetProp(prop) if !*prop.is_optional => ast::Expr {
                    kind: ast::ExprKind::SetProp(ast::SetProp {
                        node: *prop.node,
                        field: *prop.field,
                        value,
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
                }))
            ));
        }
        // string literal
        if self.match_(&TokenKind::String) {
            return Ok(literal!(
                self,
                ast::LitValue::Str(self.previous.lexeme.into())
            ));
        }
        // array literal
        if self.match_(&TokenKind::LeftBrace) {
            let span_start = self.previous.span.start;
            let exprs = vec![];
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
            let pairs = vec![];
            while !self.at_end() && !self.check(&TokenKind::RightBracket) {
                let mut identifier = None;
                let key = if self.match_(&TokenKind::Identifier) {
                    // simple keys may be identifiers
                    identifier = Some(self.previous.clone());
                    literal!(self, ast::LitValue::Str(self.previous.lexeme.into()))
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
                kind: ast::ExprKind::Grouping(Box::new(expr)),
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

#[cfg(test)]
mod tests {
    use super::*;

    // TODO: utilities for easier testing parsed AST

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
    */
}
