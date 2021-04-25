use crate::{
    ast::{self, Global, AST},
    lexer::{self, Lexer, NextTokenExt, Token, TokenKind},
};
use std::{collections::HashSet, convert::Into};
use ves_error::{ErrCtx, FileId, Span, VesError, VesFileDatabase};

type ParseResult<T> = std::result::Result<T, VesError>;

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    previous: Token<'a>,
    current: Token<'a>,
    eof: Token<'a>,
    ex: ErrCtx,
    fid: FileId,
    scope_depth: usize,
    globals: HashSet<Global<'a>>,
    db: &'a VesFileDatabase<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>, fid: FileId, db: &'a VesFileDatabase) -> Parser<'a> {
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
            scope_depth: 0,
            globals: HashSet::new(),
            ex: ErrCtx::new(),
            fid,
            db,
        }
    }

    pub fn parse(mut self) -> Result<AST<'a>, ErrCtx> {
        self.advance();
        let mut body = vec![];
        while !self.at_end() {
            match self.stmt(true) {
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
            Ok(AST::with_globals(body, self.globals, self.fid))
        }
    }

    fn stmt(&mut self, consume_semi: bool) -> ParseResult<ast::Stmt<'a>> {
        if self.match_any(&[
            TokenKind::LeftBrace,
            TokenKind::Let,
            TokenKind::Mut,
            TokenKind::Print,
            TokenKind::Loop,
            TokenKind::For,
            TokenKind::While,
            TokenKind::Break,
            TokenKind::Continue,
            TokenKind::Defer,
            TokenKind::Return,
        ]) {
            match self.previous.kind {
                TokenKind::LeftBrace => self.block_stmt(),
                TokenKind::Let => unimplemented!(),
                TokenKind::Mut => unimplemented!(),
                TokenKind::Print => unimplemented!(),
                TokenKind::Loop => unimplemented!(),
                TokenKind::For => unimplemented!(),
                TokenKind::While => unimplemented!(),
                TokenKind::Break => unimplemented!(),
                TokenKind::Continue => unimplemented!(),
                TokenKind::Defer => unimplemented!(),
                TokenKind::Return => unimplemented!(),
                _ => unreachable!(),
            }
        } else {
            self.expr_stmt(consume_semi)
        }
    }

    fn block_stmt(&mut self) -> ParseResult<ast::Stmt<'a>> {
        let span_start = self.previous.span.start;
        let body = self.block()?;
        let span_end = self.previous.span.end;
        Ok(ast::Stmt {
            kind: ast::StmtKind::Block(body),
            span: span_start..span_end,
        })
    }

    fn block(&mut self) -> ParseResult<Vec<ast::Stmt<'a>>> {
        self.scope_depth += 1;

        let mut body = vec![];
        // if the next token is a RightBrace, the block is empty
        if !self.check(&TokenKind::RightBrace) {
            while !self.at_end() && !self.check(&TokenKind::RightBrace) {
                match self.stmt(true) {
                    Ok(stmt) => body.push(stmt),
                    Err(e) => {
                        self.ex.record(e);
                        self.synchronize();
                    }
                }
            }
        }
        self.scope_depth -= 1;
        self.consume(&TokenKind::RightBrace, "Expected '}' after a block")?;
        Ok(body)
    }

    fn expr_stmt(&mut self, consume_semi: bool) -> ParseResult<ast::Stmt<'a>> {
        let span_start = self.previous.span.start;
        let expr = self.comma()?;
        let span_end = self.current.span.end;

        if consume_semi {
            self.skip_semi();
        }

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

    fn spread_expr(&mut self) -> ParseResult<ast::Expr<'a>> {
        if self.match_(&TokenKind::Ellipsis) {
            let span_start = self.previous.span.start;
            Ok(ast::Expr {
                kind: ast::ExprKind::Spread(box self.expr()?),
                span: span_start..self.previous.span.start,
            })
        } else {
            self.expr()
        }
    }

    fn expr(&mut self) -> ParseResult<ast::Expr<'a>> {
        // TODO: this
        if self.match_any(&[
            TokenKind::Struct,
            TokenKind::Fn,
            TokenKind::If,
            TokenKind::Do,
        ]) {
            match self.previous.kind {
                TokenKind::Struct => unimplemented!(),
                TokenKind::Fn => self.fn_decl(ast::FnKind::Function),
                TokenKind::If => self.if_expr(),
                TokenKind::Do => self.do_block_expr(),
                _ => unreachable!(),
            }
        } else {
            self.assignment()
        }
    }

    /* fn struct_decl(&mut self) -> ParseResult<ast::Expr<'a>> {
        let span_start = self.previous.span.start;
        let name = if self.match_(&TokenKind::Identifier) {
            self.previous.clone()
        } else {
            let (line, column) = self.db.location(self.fid, &self.previous.span);
            Token::new(
                format!("[struct@{}:{}]", line, column),
                self.previous.span.clone(),
                TokenKind::Identifier,
            )
        };
        // fields
        if self.match_(&TokenKind::LeftParen) {}
        let span_end = self.previous.span.end;
    } */

    fn fn_decl(&mut self, mut kind: ast::FnKind) -> ParseResult<ast::Expr<'a>> {
        let span_start = self.previous.span.start;
        let name = if self.match_(&TokenKind::Identifier) {
            remember_if_global!(self, self.previous, ast::VarKind::Let);
            self.previous.clone()
        } else {
            if matches!(kind, ast::FnKind::Method) {}
            let (line, column) = self.db.location(self.fid, &self.previous.span);
            Token::new(
                format!("[fn@{}:{}]", line, column),
                self.previous.span.clone(),
                TokenKind::Identifier,
            )
        };

        self.consume(&TokenKind::LeftParen, "Expected '('")?;
        let params = self.param_pack(true)?;
        self.consume(&TokenKind::RightParen, "Expected ')'")?;
        let body = if self.match_(&TokenKind::Arrow) {
            let body_span_start = self.previous.span.start;
            let expr = self.expr()?;
            vec![ast::Stmt {
                span: body_span_start..expr.span.end,
                kind: ast::StmtKind::Return(Some(box expr)),
            }]
        } else {
            self.consume(&TokenKind::LeftBrace, "Expected '{'")?;
            self.block()?
        };
        let span_end = self.previous.span.end;
        if kind == ast::FnKind::Method
            && (params.positional.is_empty() || params.positional[0].kind != TokenKind::Self_)
        {
            kind = ast::FnKind::Static;
        }
        Ok(ast::Expr {
            span: span_start..span_end,
            kind: ast::ExprKind::Fn(box ast::FnInfo {
                name,
                params,
                body,
                kind,
            }),
        })
    }

    fn param_pack(&mut self, rest_args: bool) -> ParseResult<ast::Params<'a>> {
        let mut parsing_default = false;
        let mut positional = vec![];
        let mut default = vec![];
        let mut rest = None;
        while !self.check(&TokenKind::LeftParen) {
            if self.match_(&TokenKind::Ellipsis) {
                if !rest_args {
                    return Err(VesError::parse(
                        "Rest arguments are not allowed here",
                        self.previous.span.clone(),
                        self.fid,
                    ));
                }
                // rest argument
                let name = self.consume_any(
                    &[TokenKind::Identifier, TokenKind::Self_],
                    "Expected parameter name",
                )?;
                rest = Some(name);
                break;
            } else {
                // positional or default argument
                let name = self.consume(&TokenKind::Identifier, "Expected parameter name")?;
                let value = if self.match_(&TokenKind::Equal) {
                    Some(self.expr()?)
                } else {
                    None
                };
                match value {
                    Some(value) => {
                        parsing_default = true;
                        default.push((name, value));
                    }
                    None => {
                        if parsing_default {
                            return Err(VesError::parse(
                                    "Positional arguments may not appear after arguments with default values",
                                    self.previous.span.clone(),
                                    self.fid,
                                ));
                        }
                        positional.push(name);
                    }
                }
            }
            if !self.match_(&TokenKind::Comma) {
                break;
            }
        }
        // consume trailing comma
        self.match_(&TokenKind::Comma);
        if !self.check(&TokenKind::RightParen) {
            // if we get here, it means we're not at the end of the param list
            if rest.is_some() {
                return Err(VesError::parse(
                    "Rest parameter must appear last in parameter list",
                    self.previous.span.clone(),
                    self.fid,
                ));
            }
        }
        Ok(ast::Params {
            positional,
            default,
            rest,
        })
    }

    fn if_expr(&mut self) -> ParseResult<ast::Expr<'a>> {
        let span_start = self.previous.span.start;
        let condition = self.condition()?;
        let then = self.do_block()?;
        let mut otherwise = None;
        if self.match_(&TokenKind::Else) {
            if self.match_(&TokenKind::If) {
                // `else if`
                let nested = self.if_expr()?;
                otherwise = Some(ast::DoBlock {
                    statements: vec![],
                    value: Some(nested),
                });
            } else {
                // `else`
                otherwise = Some(self.do_block()?);
            }
        }
        let span_end = self.previous.span.end;
        Ok(ast::Expr {
            span: span_start..span_end,
            kind: ast::ExprKind::If(box ast::If {
                condition,
                then,
                otherwise,
            }),
        })
    }

    fn condition(&mut self) -> ParseResult<ast::Condition<'a>> {
        if self.match_any(&[TokenKind::Ok, TokenKind::Err]) {
            let which = self.previous.clone();
            self.consume(&TokenKind::LeftParen, "Expected '('")?;
            let ident = self.consume(&TokenKind::Identifier, "Expected identifier")?;
            self.consume(&TokenKind::RightParen, "Expected ')'")?;
            self.consume(&TokenKind::Equal, "Expected assignment")?;
            let value = self.expr()?;
            Ok(ast::Condition {
                value,
                pattern: match which.kind {
                    TokenKind::Ok => ast::ConditionPattern::IsOk(ident),
                    TokenKind::Err => ast::ConditionPattern::IsErr(ident),
                    _ => unreachable!(),
                },
            })
            // destructuring
        } else {
            let value = self.expr()?;
            Ok(ast::Condition {
                value,
                pattern: ast::ConditionPattern::Value,
            })
        }
    }

    fn do_block_expr(&mut self) -> ParseResult<ast::Expr<'a>> {
        let span_start = self.previous.span.start;
        let inner = self.do_block()?;
        let span_end = self.previous.span.end;
        Ok(ast::Expr {
            span: span_start..span_end,
            kind: ast::ExprKind::DoBlock(box inner),
        })
    }

    fn do_block(&mut self) -> ParseResult<ast::DoBlock<'a>> {
        // the value of the block is the last expression statement,
        // but only if it is not terminated by a semicolon.
        // in any other case the value is `none`

        self.consume(&TokenKind::LeftBrace, "Expected block")?;
        self.scope_depth += 1;

        let mut body = vec![];
        let mut last_stmt_had_semi = false;
        // if the next token is a RightBrace, the block is empty
        if !self.check(&TokenKind::RightBrace) {
            while !self.at_end() && !self.check(&TokenKind::RightBrace) {
                // `false` means the statements don't consume their semicolons.
                match self.stmt(false) {
                    Ok(stmt) => {
                        body.push(stmt);
                        last_stmt_had_semi = self.match_(&TokenKind::Semi);
                    }
                    Err(e) => {
                        self.ex.record(e);
                        self.synchronize();
                    }
                }
            }
        }

        self.scope_depth -= 1;
        self.consume(&TokenKind::RightBrace, "Expected '}' after a block")?;

        // if the last statement was not terminated by a semicolon,
        // and it's an expression, then that's the value.
        let mut value = None;
        if !last_stmt_had_semi {
            if let Some(last_stmt) = body.pop() {
                if let ast::StmtKind::ExprStmt(expr) = last_stmt.kind {
                    value = Some(*expr);
                } else {
                    // since we pop the last statement, we have to push it back
                    // if it isn't an expression.
                    body.push(last_stmt);
                }
            }
        };

        Ok(ast::DoBlock {
            statements: body,
            value,
        })
    }

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
                        value: desugar_assignment(operator, expr.clone(), self.expr()?),
                    }),
                    span: span_start..self.current.span.end,
                },
                // x[<expr>] = <expr>
                ast::ExprKind::GetItem(ref get) if is_valid_assignment_target(&get.node, false) => {
                    ast::Expr {
                        kind: ast::ExprKind::SetItem(box ast::SetItem {
                            node: get.node.clone(),
                            key: get.key.clone(),
                            value: desugar_assignment(operator, expr.clone(), self.expr()?),
                        }),
                        span: span_start..self.current.span.end,
                    }
                }
                // x.key = <expr>
                // except x?.key = <expr>
                ast::ExprKind::GetProp(ref get)
                    if !get.is_optional && is_valid_assignment_target(&get.node, false) =>
                {
                    ast::Expr {
                        kind: ast::ExprKind::SetProp(box ast::SetProp {
                            node: get.node.clone(),
                            field: get.field.clone(),
                            value: desugar_assignment(operator, expr.clone(), self.expr()?),
                        }),
                        span: span_start..self.current.span.end,
                    }
                }
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
        // expr in expr
        // expr is expr
        while self.match_any(&[
            TokenKind::More,
            TokenKind::Less,
            TokenKind::MoreEqual,
            TokenKind::LessEqual,
            TokenKind::In,
            TokenKind::Is,
        ]) {
            expr = match self.previous.kind {
                TokenKind::More => binary!(expr, Gt, self.comparison()?),
                TokenKind::Less => binary!(expr, Lt, self.comparison()?),
                TokenKind::MoreEqual => binary!(expr, Ge, self.comparison()?),
                TokenKind::LessEqual => binary!(expr, Le, self.comparison()?),
                TokenKind::In => binary!(expr, In, self.comparison()?),
                TokenKind::Is => binary!(expr, Is, self.comparison()?),
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
                    if is_valid_assignment_target(&expr, true) {
                        ast::Expr {
                            span: op.span.start..expr.span.end,
                            kind: ast::ExprKind::PrefixIncDec(box ast::IncDec {
                                expr,
                                kind: ast::IncDecKind::from(kind),
                            }),
                        }
                    } else {
                        return Err(VesError::parse(
                            "Invalid assignment target",
                            op.span.start..expr.span.end,
                            self.fid,
                        ));
                    }
                }
                _ => unreachable!(),
            });
        }

        let mut expr = self.call()?;

        if self.match_any(&[TokenKind::Increment, TokenKind::Decrement]) {
            println!("??????");
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
                    self.consume(&TokenKind::RightParen, "Expected ')'")?;
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
                TokenKind::Increment | TokenKind::Decrement => {
                    if is_valid_assignment_target(&expr, true) {
                        ast::Expr {
                            span: expr.span.start..self.previous.span.end,
                            kind: ast::ExprKind::PostfixIncDec(box ast::IncDec {
                                expr,
                                kind: ast::IncDecKind::from(self.previous.kind.clone()),
                            }),
                        }
                    } else {
                        return Err(VesError::parse(
                            "Invalid assignment target",
                            expr.span.start..self.previous.span.end,
                            self.fid,
                        ));
                    }
                }
                _ => unreachable!(),
            }
        }

        Ok(expr)
    }

    fn arg_list(&mut self) -> ParseResult<ast::Args<'a>> {
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
                args.push(self.spread_expr()?);
                if !self.match_(&TokenKind::Comma) {
                    break;
                }
            }
        }
        // consume trailing comma
        self.match_(&TokenKind::Comma);
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
        // identifier
        if self.match_(&TokenKind::Identifier) {
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
            let mut literal = self
                .previous
                .lexeme
                .trim_start_matches(|v| v == '"' || v == '\'')
                .trim_end_matches(|v| v == '"' || v == '\'')
                .to_string();
            let span = self.previous.span.clone();
            self.try_unescape(&mut literal, span);
            return Ok(literal!(self, ast::LitValue::Str(literal.into())));
        }
        if self.match_(&TokenKind::InterpolatedString(vec![])) {
            let span_start = self.previous.span.start;
            let mut fragments = vec![];
            let previous = std::mem::replace(&mut self.previous, self.eof.clone());
            if let TokenKind::InterpolatedString(unprocessed) = previous.kind {
                for frag in unprocessed.into_iter() {
                    match frag {
                        lexer::Frag::Str(v) => fragments.push(ast::FStringFrag::Str(ast::Lit {
                            token: v.clone(),
                            value: {
                                let mut lexeme = v.lexeme.to_string();
                                self.try_unescape(&mut lexeme, v.span);
                                ast::LitValue::Str(lexeme.into())
                            },
                        })),
                        lexer::Frag::Sublexer(sublexer) => {
                            let mut subparser = Parser::new(sublexer, self.fid, self.db);
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
            let mut exprs = vec![self.spread_expr()?];
            while self.match_(&TokenKind::Comma) {
                exprs.push(self.spread_expr()?);
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
            let mut entries = vec![self.parse_map_entry()?];
            while self.match_(&TokenKind::Comma) {
                entries.push(self.parse_map_entry()?);
            }
            self.consume(&TokenKind::RightBrace, "Expected '}'")?;
            let span_end = self.previous.span.end;
            return Ok(ast::Expr {
                kind: ast::ExprKind::Map(entries),
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
                format!("Unexpected EOF at {}", self.previous.lexeme),
                self.eof.span.clone(),
                self.fid,
            ));
        }
        Err(VesError::parse(
            format!("Unexpected token {}", self.previous.lexeme),
            self.current.span.clone(),
            self.fid,
        ))
    }

    fn parse_map_entry(&mut self) -> ParseResult<ast::MapEntry<'a>> {
        if self.match_(&TokenKind::Ellipsis) {
            Ok(ast::MapEntry::Spread(self.expr()?))
        } else {
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
            Ok(ast::MapEntry::Pair(key, value))
        }
    }

    fn try_unescape(&mut self, string: &mut String, span: Span) {
        if super::lexer::unescape_in_place(string).is_none() {
            self.ex.record(VesError::parse(
                "Invalid unicode escape sequence",
                span,
                self.fid,
            ));
        }
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
    fn consume_any<S: Into<String>>(
        &mut self,
        kinds: &[TokenKind<'a>],
        err_msg: S,
    ) -> ParseResult<Token<'a>> {
        for kind in kinds {
            if self.check(kind) {
                return Ok(self.advance());
            }
        }
        Err(VesError::parse(
            err_msg,
            self.current.span.clone(),
            self.fid,
        ))
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
        self.previous.clone()
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

fn is_valid_assignment_target(expr: &ast::Expr<'_>, check_top: bool) -> bool {
    if !check_top {
        match &expr.kind {
            ast::ExprKind::GetProp(ref get) => {
                if get.is_optional {
                    false
                } else {
                    is_valid_assignment_target(&get.node, false)
                }
            }
            ast::ExprKind::GetItem(ref get) => is_valid_assignment_target(&get.node, false),
            ast::ExprKind::Call(ref call) => is_valid_assignment_target(&call.callee, false),
            _ => true,
        }
    } else {
        match &expr.kind {
            ast::ExprKind::Variable(..) => true,
            ast::ExprKind::GetProp(ref get) => {
                if get.is_optional {
                    false
                } else {
                    is_valid_assignment_target(&get.node, false)
                }
            }
            ast::ExprKind::GetItem(ref get) => is_valid_assignment_target(&get.node, false),
            _ => false,
        }
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

    // TODO: spans may be wrong

    macro_rules! assert_ast {
        ($source:expr, $expected:expr) => {{
            let src = $source;
            let mut db = VesFileDatabase::new();
            let fid = db.add_snippet(src.into());
            pretty_assertions::assert_eq!(
                DisplayAsDebugWrapper(clean_tree(
                    Parser::new(Lexer::new(src), fid, &db)
                        .parse()
                        .unwrap()
                        .body
                        .into_iter()
                        .map(|stmt| stmt.ast_to_str())
                        .collect::<Vec<_>>()
                        .join("\n")
                )),
                DisplayAsDebugWrapper($expected.trim_start().to_owned())
            );
        }};
    }

    macro_rules! assert_ast_err {
        ($source:literal, $error:literal) => {{
            let src = $source;
            let mut db = VesFileDatabase::new();
            let fid = db.add_snippet(src.into());
            let errors = Parser::new(Lexer::new(src), fid, &db)
                .parse()
                .unwrap_err()
                .errors;
            assert!(errors.len() == 1);
            assert_eq!(&errors[0].msg, $error);
        }};
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
        assert_ast!(
            "{ }",
            r#"
StmtKind::Block
  statements="#
        );
    }

    #[test]
    fn parse_comma() {
        assert_ast!(
            r#"1.0e-5, none, true, false, "string""#,
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
        assert_ast!(
            "0 || 0",
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

    #[test]
    fn parse_access() {
        assert_ast!(
            "a.b?.c[0]",
            r#"
StmtKind::ExprStmt
  expr: GetItem
    node: GetProp
      node: GetProp
        node: ExprKind::Variable
          name: "a"
        field: "b"
        is_optional: false
      field: "c"
      is_optional: true
    key: Lit
      token: "0"
      value: LitValue::Number
        field0: 0"#
        )
    }

    #[test]
    fn parse_prefix_increment() {
        assert_ast!(
            "++a",
            r#"
StmtKind::ExprStmt
  expr: IncDec
    expr: ExprKind::Variable
      name: "a"
    kind: Increment"#
        )
    }

    #[test]
    fn parse_postfix_increment() {
        assert_ast!(
            "a++",
            r#"
StmtKind::ExprStmt
  expr: IncDec
    expr: ExprKind::Variable
      name: "a"
    kind: Increment"#
        )
    }

    #[test]
    fn parse_invalid_assignments() {
        assert_ast_err!("a?.b = v", "Invalid assignment target");
        assert_ast_err!("a()?.b = v", "Invalid assignment target");
        assert_ast_err!("[a,b,c].f()?.x = v", "Invalid assignment target");
        assert_ast_err!("a()?.b().c = v", "Invalid assignment target");
    }

    #[test]
    fn parse_array_literal() {
        // simple
        assert_ast!(
            r#"[0, "a", none, a]"#,
            r#"
StmtKind::ExprStmt
  expr: ExprKind::Array
    field0=
      Lit
        token: "0"
        value: LitValue::Number
          field0: 0
      Lit
        token: "\"a\""
        value: LitValue::Str
          field0: "a"
      Lit
        token: "none"
        value: LitValue::None
      ExprKind::Variable
        name: "a""#
        );
        // with spread
        assert_ast!(
            r#"[...v]"#,
            r#"
StmtKind::ExprStmt
  expr: ExprKind::Array
    field0=
      ExprKind::Spread
        field0: ExprKind::Variable
          name: "v""#
        );
    }

    #[test]
    fn parse_map_literals() {
        // identifier key
        assert_ast!(
            r#"a = { test: 1.0 }"#,
            r#"
StmtKind::ExprStmt
  expr: Assignment
    name: "a"
    value: ExprKind::Map
      field0=
        MapEntry::Pair
          key: Lit
            token: "test"
            value: LitValue::Str
              field0: "test"
          value: Lit
            token: "1.0"
            value: LitValue::Number
              field0: 1"#
        );
        // expression key
        assert_ast!(
            r#"a = { ["test"]: 1.0 }"#,
            r#"
StmtKind::ExprStmt
  expr: Assignment
    name: "a"
    value: ExprKind::Map
      field0=
        MapEntry::Pair
          key: Lit
            token: "\"test\""
            value: LitValue::Str
              field0: "test"
          value: Lit
            token: "1.0"
            value: LitValue::Number
              field0: 1"#
        );
        // spread
        assert_ast!(
            r#"a = { v: 0, ...o }"#,
            r#"
StmtKind::ExprStmt
  expr: Assignment
    name: "a"
    value: ExprKind::Map
      field0=
        MapEntry::Pair
          key: Lit
            token: "v"
            value: LitValue::Str
              field0: "v"
          value: Lit
            token: "0"
            value: LitValue::Number
              field0: 0
        MapEntry::Spread
          target: ExprKind::Variable
            name: "o""#
        );
    }

    #[test]
    fn precedence() {
        assert_ast!(
            r#"1 / 1 + 1 * 1 ** 2"#,
            r#"
StmtKind::ExprStmt
  expr: ExprKind::Binary
    op: Add
    left: ExprKind::Binary
      op: Div
      left: Lit
        token: "1"
        value: LitValue::Number
          field0: 1
      right: Lit
        token: "1"
        value: LitValue::Number
          field0: 1
    right: ExprKind::Binary
      op: Mul
      left: Lit
        token: "1"
        value: LitValue::Number
          field0: 1
      right: ExprKind::Binary
        op: Pow
        left: Lit
          token: "1"
          value: LitValue::Number
            field0: 1
        right: Lit
          token: "2"
          value: LitValue::Number
            field0: 2"#
        )
    }

    #[test]
    fn string_interpolation() {
        assert_ast!(
            r#"f"test{2+2}""#,
            r#"
StmtKind::ExprStmt
  expr: FString
    fragments=
      FStringFrag::Str
        field0: Lit
          token: "test"
          value: LitValue::Str
            field0: "test"
      FStringFrag::Expr
        field0: ExprKind::Binary
          op: Add
          left: Lit
            token: "2"
            value: LitValue::Number
              field0: 2
          right: Lit
            token: "2"
            value: LitValue::Number
              field0: 2"#
        )
    }

    #[test]
    fn parse_call() {
        assert_ast!(
            r#"f(a, b, ...c)"#,
            r#"
StmtKind::ExprStmt
  expr: Call
    callee: ExprKind::Variable
      name: "f"
    args=
      ExprKind::Variable
        name: "a"
      ExprKind::Variable
        name: "b"
      ExprKind::Spread
        field0: ExprKind::Variable
          name: "c"
    tco: false
    rest: false"#
        )
    }

    #[test]
    fn parse_compound_assignment() {
        assert_ast!(
            r#"a += b += 5"#,
            r#"
StmtKind::ExprStmt
  expr: Assignment
    name: "a"
    value: ExprKind::Binary
      op: Add
      left: ExprKind::Variable
        name: "a"
      right: Assignment
        name: "b"
        value: ExprKind::Binary
          op: Add
          left: ExprKind::Variable
            name: "b"
          right: Lit
            token: "5"
            value: LitValue::Number
              field0: 5"#
        );
    }

    #[test]
    fn parse_if_expr() {
        // simple
        assert_ast!(
            r#"if v { 0 }"#,
            r#"
StmtKind::ExprStmt
  expr: If
    condition: Condition
      value: ExprKind::Variable
        name: "v"
      pattern: ConditionPattern::Value
    then: DoBlock
      statements=
      value: Lit
        token: "0"
        value: LitValue::Number
          field0: 0
    otherwise: None"#
        );
        // with else
        assert_ast!(
            r#"if v { 0 } else { 1 }"#,
            r#"
StmtKind::ExprStmt
  expr: If
    condition: Condition
      value: ExprKind::Variable
        name: "v"
      pattern: ConditionPattern::Value
    then: DoBlock
      statements=
      value: Lit
        token: "0"
        value: LitValue::Number
          field0: 0
    otherwise: DoBlock
      statements=
      value: Lit
        token: "1"
        value: LitValue::Number
          field0: 1"#
        );
        // more branches
        assert_ast!(
            r#"if v0 { 0 } else if v1 { 1 } else if v2 { 2 } else { 0 }"#,
            r#"
StmtKind::ExprStmt
  expr: If
    condition: Condition
      value: ExprKind::Variable
        name: "v0"
      pattern: ConditionPattern::Value
    then: DoBlock
      statements=
      value: Lit
        token: "0"
        value: LitValue::Number
          field0: 0
    otherwise: DoBlock
      statements=
      value: If
        condition: Condition
          value: ExprKind::Variable
            name: "v1"
          pattern: ConditionPattern::Value
        then: DoBlock
          statements=
          value: Lit
            token: "1"
            value: LitValue::Number
              field0: 1
        otherwise: DoBlock
          statements=
          value: If
            condition: Condition
              value: ExprKind::Variable
                name: "v2"
              pattern: ConditionPattern::Value
            then: DoBlock
              statements=
              value: Lit
                token: "2"
                value: LitValue::Number
                  field0: 2
            otherwise: DoBlock
              statements=
              value: Lit
                token: "0"
                value: LitValue::Number
                  field0: 0"#
        );
        // destructuring
        assert_ast!(
            r#"if ok(v) = f() { v }"#,
            r#"
StmtKind::ExprStmt
  expr: If
    condition: Condition
      value: Call
        callee: ExprKind::Variable
          name: "f"
        args=
        tco: false
        rest: false
      pattern: ConditionPattern::IsOk
        field0: "v"
    then: DoBlock
      statements=
      value: ExprKind::Variable
        name: "v"
    otherwise: None"#
        );
        assert_ast!(
            r#"if err(e) = f() { e }"#,
            r#"
StmtKind::ExprStmt
  expr: If
    condition: Condition
      value: Call
        callee: ExprKind::Variable
          name: "f"
        args=
        tco: false
        rest: false
      pattern: ConditionPattern::IsErr
        field0: "e"
    then: DoBlock
      statements=
      value: ExprKind::Variable
        name: "e"
    otherwise: None"#
        );
    }

    #[test]
    fn parse_do_block() {
        assert_ast!(
            r#"do {}"#,
            r#"
StmtKind::ExprStmt
  expr: DoBlock
    statements=
    value: None"#
        );
        assert_ast!(
            r#"do { true }"#,
            r#"
StmtKind::ExprStmt
  expr: DoBlock
    statements=
    value: Lit
      token: "true"
      value: LitValue::Bool
        field0: true"#
        );

        assert_ast!(
            r#"do { if cond() { "true" } else { "false" } }"#,
            r#"
StmtKind::ExprStmt
  expr: DoBlock
    statements=
    value: If
      condition: Condition
        value: Call
          callee: ExprKind::Variable
            name: "cond"
          args=
          tco: false
          rest: false
        pattern: ConditionPattern::Value
      then: DoBlock
        statements=
        value: Lit
          token: "\"true\""
          value: LitValue::Str
            field0: "true"
      otherwise: DoBlock
        statements=
        value: Lit
          token: "\"false\""
          value: LitValue::Str
            field0: "false""#
        );
        // TODO: test these once all statements are implemented
        /* assert_ast!(
            r#"
            a = do {
                mut sum = 0
                for i in 0..10 { sum += i }
                sum
            }
            "#
        );
        assert_ast!(
            r#"
            a = do {
                mut sum = 0
                for i in 0..10 { sum += i }
                sum; // notice the semicolon
            }
            "#
        ); */
    }

    #[test]
    fn parse_fn_decl() {
        // basic
        assert_ast!(
            r#"fn name(a, b = 0, ...c) {}"#,
            r#"
StmtKind::ExprStmt
  expr: FnInfo
    name: "name"
    params: Params
      positional=
        "a"
      default=
        tuple
          field0: "b"
          field1: Lit
            token: "0"
            value: LitValue::Number
              field0: 0
      rest: "c"
    body=
    kind: Function"#
        );
        // arrow
        assert_ast!(
            r#"fn name(a, b = 0, ...c) => 0"#,
            r#"
StmtKind::ExprStmt
  expr: FnInfo
    name: "name"
    params: Params
      positional=
        "a"
      default=
        tuple
          field0: "b"
          field1: Lit
            token: "0"
            value: LitValue::Number
              field0: 0
      rest: "c"
    body=
      StmtKind::Return
        field0: Lit
          token: "0"
          value: LitValue::Number
            field0: 0
    kind: Function"#
        );
        // anonymous
        assert_ast!(
            r#"fn(a, b = 0, ...c) {}"#,
            r#"
StmtKind::ExprStmt
  expr: FnInfo
    name: "[fn@1:1]"
    params: Params
      positional=
        "a"
      default=
        tuple
          field0: "b"
          field1: Lit
            token: "0"
            value: LitValue::Number
              field0: 0
      rest: "c"
    body=
    kind: Function"#
        );
        // anonymous, arrow
        assert_ast!(
            r#"fn(a, b = 0, ...c) => 0"#,
            r#"
StmtKind::ExprStmt
  expr: FnInfo
    name: "[fn@1:1]"
    params: Params
      positional=
        "a"
      default=
        tuple
          field0: "b"
          field1: Lit
            token: "0"
            value: LitValue::Number
              field0: 0
      rest: "c"
    body=
      StmtKind::Return
        field0: Lit
          token: "0"
          value: LitValue::Number
            field0: 0
    kind: Function"#
        );
        // trailing comma
        assert_ast!(
            r#"fn(a, b = 0, ...c,) => 0"#,
            r#"
StmtKind::ExprStmt
  expr: FnInfo
    name: "[fn@1:1]"
    params: Params
      positional=
        "a"
      default=
        tuple
          field0: "b"
          field1: Lit
            token: "0"
            value: LitValue::Number
              field0: 0
      rest: "c"
    body=
      StmtKind::Return
        field0: Lit
          token: "0"
          value: LitValue::Number
            field0: 0
    kind: Function"#
        );
    }

    #[test]
    fn parse_bad_fn_decl() {
        // positional after default
        assert_ast_err!(
            "fn(a=0,b) {}",
            "Positional arguments may not appear after arguments with default values"
        );
        // rest not last
        assert_ast_err!(
            "fn(...a, b) {}",
            "Rest parameter must appear last in parameter list"
        );
        // unopened param list
        assert_ast_err!("fn a) {}", "Expected '('");
        // unclosed param list
        assert_ast_err!("fn(a {}", "Expected ')'");
    }
}
