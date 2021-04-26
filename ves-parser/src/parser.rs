use crate::{
    ast::{self, Global, VarKind, AST},
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
                TokenKind::Let | TokenKind::Mut => self.var_decl(),
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

    fn var_decl(&mut self) -> ParseResult<ast::Stmt<'a>> {
        let span_start = self.previous.span.start;
        let kind = if self.previous.kind == TokenKind::Let {
            VarKind::Let
        } else {
            VarKind::Mut
        };
        let mut bindings = vec![self.binding_expression(kind)?];

        while self.match_(&TokenKind::Comma) {
            bindings.push(self.binding_expression(kind)?);
        }

        Ok(ast::Stmt {
            kind: ast::StmtKind::Var(bindings),
            span: span_start..self.previous.span.end,
        })
    }

    fn binding_expression(&mut self, kind: VarKind) -> ParseResult<ast::Var<'a>> {
        let ident = self.consume(
            &TokenKind::Identifier,
            "Expected a variable name after the keyword or comma",
        );

        let init = if self.match_(&TokenKind::Equal) {
            let ident = ident.clone();
            Some(self.expr().map_err(|e| {
                let _ = ident.map_err(|e| self.record(e));
                e
            })?)
        } else {
            None
        };

        let ident = ident?;
        if kind == VarKind::Let && init.is_none() {
            self.record(VesError::let_without_value(
                format!(
                    "Immutable variable `{}` must be initialized at declaration",
                    ident.lexeme
                ),
                ident.span.clone(),
                self.fid,
            ));
        }

        Ok(ast::Var {
            kind,
            name: ident,
            initializer: init,
        })
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
        self.consume(&TokenKind::RightBrace, "Expected a '}' after a block")?;
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
                TokenKind::Struct => self.struct_decl(),
                TokenKind::Fn => self.fn_decl_expr(),
                TokenKind::If => self.if_expr(),
                TokenKind::Do => self.do_block_expr(),
                _ => unreachable!(),
            }
        } else {
            self.assignment()
        }
    }

    fn struct_decl(&mut self) -> ParseResult<ast::Expr<'a>> {
        let span_start = self.previous.span.start;
        // parse struct name, or generate it
        let struct_name = if self.match_(&TokenKind::Identifier) {
            self.previous.clone()
        } else {
            let (line, column) = self.db.location(self.fid, &self.previous.span);
            Token::new(
                format!("[struct@{}:{}]", line, column),
                self.previous.span.clone(),
                TokenKind::Identifier,
            )
        };
        // parse fields
        let fields = if self.match_(&TokenKind::LeftParen) {
            let fields = self.param_pack(false)?;
            self.consume(
                &TokenKind::RightParen,
                "Expected a closing `)` in this position",
            )?;
            Some(fields)
        } else {
            None
        };

        // parse struct body
        let mut methods = vec![];
        let mut r#static = ast::StructStaticProps {
            fields: vec![],
            methods: vec![],
        };
        let mut initializer = None;
        // if we come across a semi or don't come across a left brace,
        // then the struct has no body
        if !self.match_(&TokenKind::Semi) && self.match_(&TokenKind::LeftBrace) {
            while !self.match_(&TokenKind::RightBrace) {
                let prop_name = self.consume(
                    &TokenKind::Identifier,
                    "Expected method, static field or static method",
                )?;

                if prop_name.lexeme == "init" {
                    // this must be an initializer
                    if initializer.is_some() {
                        return Err(VesError::parse(
                            "Cannot have more than one initializer",
                            self.previous.span.clone(),
                            self.fid,
                        ));
                    }
                    let body = self.fn_decl_body()?;
                    initializer = Some(ast::Initializer::new(ast::FnInfo {
                        name: prop_name,
                        params: ast::Params::default(),
                        body,
                        kind: ast::FnKind::Method,
                    }));
                } else if self.match_(&TokenKind::LeftParen) {
                    // this is a method
                    let params = self.param_pack(true)?;
                    self.consume(
                        &TokenKind::RightParen,
                        "Expected a closing `)` in this position",
                    )?;
                    let body = self.fn_decl_body()?;
                    if params.is_instance_method_params() {
                        methods.push(ast::FnInfo {
                            name: prop_name,
                            params,
                            body,
                            kind: ast::FnKind::Method,
                        });
                    } else {
                        r#static.methods.push(ast::FnInfo {
                            name: prop_name,
                            params,
                            body,
                            kind: ast::FnKind::Static,
                        });
                    }
                } else {
                    // this is a static field
                    let value = if self.match_(&TokenKind::Equal) {
                        Some(self.expr()?)
                    } else {
                        None
                    };
                    r#static.fields.push((prop_name, value));
                }
            }
        }
        let span_end = self.previous.span.end;
        Ok(ast::Expr {
            kind: ast::ExprKind::Struct(box ast::StructInfo {
                name: struct_name,
                fields,
                methods,
                initializer,
                r#static,
            }),
            span: span_start..span_end,
        })
    }

    fn fn_decl_expr(&mut self) -> ParseResult<ast::Expr<'a>> {
        let span_start = self.previous.span.start;
        let decl = self.fn_decl()?;
        let span_end = self.previous.span.end;
        Ok(ast::Expr {
            kind: ast::ExprKind::Fn(box decl),
            span: span_start..span_end,
        })
    }

    fn fn_decl(&mut self) -> ParseResult<ast::FnInfo<'a>> {
        let name = if self.match_(&TokenKind::Identifier) {
            remember_if_global!(self, self.previous, ast::VarKind::Let);
            self.previous.clone()
        } else {
            let (line, column) = self.db.location(self.fid, &self.previous.span);
            Token::new(
                format!("[fn@{}:{}]", line, column),
                self.previous.span.clone(),
                TokenKind::Identifier,
            )
        };

        self.consume(
            &TokenKind::LeftParen,
            "Expected an opening `(` after the function name or keyword",
        )?;
        let params = self.param_pack(true)?;
        self.consume(
            &TokenKind::RightParen,
            "Expected a closing `)` in this position",
        )?;
        let body = self.fn_decl_body()?;
        Ok(ast::FnInfo {
            name,
            params,
            body,
            kind: ast::FnKind::Function,
        })
    }

    fn fn_decl_body(&mut self) -> ParseResult<Vec<ast::Stmt<'a>>> {
        if self.match_(&TokenKind::Arrow) {
            let body_span_start = self.previous.span.start;
            let expr = self.expr()?;
            Ok(vec![ast::Stmt {
                span: body_span_start..expr.span.end,
                kind: ast::StmtKind::Return(Some(box expr)),
            }])
        } else if self.match_(&TokenKind::LeftBrace) {
            Ok(self.block()?)
        } else {
            Err(VesError::parse(
                "Expected function body",
                self.previous.span.clone(),
                self.fid,
            ))
        }
    }

    fn param_pack(&mut self, rest_args: bool) -> ParseResult<ast::Params<'a>> {
        let mut parsing_default = false;
        let mut positional = vec![];
        let mut default = vec![];
        let mut rest = None;
        while !self.check(&TokenKind::RightParen) {
            if self.match_(&TokenKind::Ellipsis) {
                if !rest_args {
                    return Err(VesError::parse(
                        "Rest arguments are not allowed here",
                        self.previous.span.clone(),
                        self.fid,
                    ));
                }
                // rest argument
                let name = self.consume(&TokenKind::Identifier, "Expected a parameter name")?;
                rest = Some(name);
                break;
            } else {
                // positional or default argument
                // TODO: check if 'self' has a default value, which is an error (?)
                let name = self.consume_any(
                    &[TokenKind::Identifier, TokenKind::Self_],
                    "Expected parameter name",
                )?;
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

        self.consume(
            &TokenKind::LeftBrace,
            "Expected an opening `{` after the `do` keyword",
        )?;
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
            let span_start = self.previous.span.start;
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
                ast::ExprKind::GetItem(ref get)
                    if check_assignment_target(&get.node, false).is_valid() =>
                {
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
                    if !get.is_optional && check_assignment_target(&get.node, false).is_valid() =>
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
                    // TODO: do not run this twice
                    let kind = check_assignment_target(&expr, false);
                    return Err(self.invalid_assignment_error(kind, expr.span));
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

    fn invalid_assignment_error(&mut self, kind: AssignmentKind, span: Span) -> VesError {
        match kind {
            AssignmentKind::Invalid => VesError::parse(
                "Invalid assignment target. Only variables, struct.fields, and item[accesses] may be assigned to.",
                span,
                self.fid,
            ),
            AssignmentKind::OptionalAccess => VesError::new(
                "Cannot assign to an optional field access. Consider performing the assignment in an `if` block.",
                span,
                ves_error::VesErrorKind::OptionalAccessAssignment,
                self.fid,
            ),
            AssignmentKind::Valid => unreachable!(),
        }
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
                    let ass_kind = check_assignment_target(&expr, true);
                    if ass_kind == AssignmentKind::Valid {
                        ast::Expr {
                            span: op.span.start..expr.span.end,
                            kind: ast::ExprKind::PrefixIncDec(box ast::IncDec {
                                expr,
                                kind: ast::IncDecKind::from(kind),
                            }),
                        }
                    } else {
                        return Err(
                            self.invalid_assignment_error(ass_kind, op.span.start..expr.span.end)
                        );
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
                    let kind = check_assignment_target(&expr, true);
                    if kind == AssignmentKind::Valid {
                        ast::Expr {
                            span: expr.span.start..self.previous.span.end,
                            kind: ast::ExprKind::PostfixIncDec(box ast::IncDec {
                                expr,
                                kind: ast::IncDecKind::from(self.previous.kind.clone()),
                            }),
                        }
                    } else {
                        return Err(self.invalid_assignment_error(
                            kind,
                            expr.span.start..self.previous.span.end,
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
    fn record(&mut self, e: VesError) {
        self.ex.record(e);
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

#[derive(Debug, Clone, Copy, PartialEq)]
enum AssignmentKind {
    Valid,
    Invalid,
    OptionalAccess,
}

impl AssignmentKind {
    /// Returns `true` if the assignment_kind is [`Valid`].
    #[inline]
    fn is_valid(&self) -> bool {
        matches!(self, Self::Valid)
    }
}

fn check_assignment_target(expr: &ast::Expr<'_>, check_top: bool) -> AssignmentKind {
    if !check_top {
        match &expr.kind {
            ast::ExprKind::GetProp(ref get) => {
                if get.is_optional {
                    AssignmentKind::OptionalAccess
                } else {
                    check_assignment_target(&get.node, false)
                }
            }
            ast::ExprKind::GetItem(ref get) => check_assignment_target(&get.node, false),
            ast::ExprKind::Call(ref call) => check_assignment_target(&call.callee, false),
            _ => AssignmentKind::Valid,
        }
    } else {
        match &expr.kind {
            ast::ExprKind::Variable(..) => AssignmentKind::Valid,
            ast::ExprKind::GetProp(ref get) => {
                if get.is_optional {
                    AssignmentKind::OptionalAccess
                } else {
                    check_assignment_target(&get.node, false)
                }
            }
            ast::ExprKind::GetItem(ref get) => check_assignment_target(&get.node, false),
            _ => AssignmentKind::Invalid,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use infra::*;

    macro_rules! test_ok {
        ($test_name:ident $( $attr:ident ),*) => {
            $(#[$attr])*
            #[test]
            fn $test_name() {
                let (source, output) = load_test_file(stringify!($test_name));
                test_ok(stringify!(test_name), source, output);
            }
        };
    }

    macro_rules! test_err {
        ($test_name:ident $( $attr:ident ),*) => {
            $(#[$attr])*
            #[test]
            fn $test_name() {
                let (source, output) = load_test_file(stringify!($test_name));
                test_err(stringify!(test_name), source, output);
            }
        };
    }

    test_ok!(t1_parse_block);
    test_ok!(t2_parse_comma);
    test_ok!(t3_parse_or);
    test_ok!(t4_parse_access);
    test_ok!(t5_parse_postfix_increment);
    test_err!(t6_parse_invalid_assignments);
    test_ok!(t7_parse_array_literal);
    test_ok!(t8_parse_map_literals);
    test_ok!(t9_precedence);
    test_ok!(t10_string_interpolation);
    test_ok!(t11_parse_call);
    test_ok!(t12_parse_compound_assignment);
    test_ok!(t13_if_expr);

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
    test_ok!(t14_parse_do_block);
    test_ok!(t15_parse_fn_decl);
    test_err!(t16_parse_bad_fn_decl);

    // TODO: init {} blocks
    // TODO: test parsing bad struct decls
    test_ok!(t17_parse_struct_decl);
    test_ok!(t18_parse_var_decl);
    test_err!(t19_let_variables_must_be_initialized);

    mod infra {
        use super::*;
        pub use ast2str::ast2str_lib::symbols;
        pub use ast2str::AstToStr;
        pub use lazy_static::lazy_static;
        pub use regex::Regex;

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
            pub static ref RE: Regex = Regex::new(
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

        pub fn clean_tree(tree: String) -> String {
            RE.replace_all(&tree, " ")
                .lines()
                .map(|l| l.trim_end())
                .collect::<Vec<_>>()
                .join("\n")
        }

        static CRATE_ROOT: &str = env!("CARGO_MANIFEST_DIR");
        static TESTS_DIR: &str = "src/tests";

        pub fn load_test_file(name: &str) -> (String, String) {
            let path = std::path::PathBuf::from(CRATE_ROOT)
                .join(TESTS_DIR)
                .join(format!("{}.test", name));
            let source = std::fs::read_to_string(&path)
                .map_err(|e| format!("Failed to read the `{}`: {}", path.display(), e))
                .unwrap();
            let (code, expected) = source.split_once("%output\n").expect(
            "Invalid test file format. Make sure that your test contains the %output directive.",
        );
            (code.trim().to_owned(), expected.trim().to_owned())
        }

        pub fn test_err(test_name: &str, src: String, expected: String) {
            let src = std::borrow::Cow::Borrowed(&src[..]);
            let mut db = VesFileDatabase::new();
            let fid = db.add_snippet(src.clone());
            let errors = Parser::new(Lexer::new(&*src), fid, &db)
                .parse()
                .expect_err("Test succeeded unexpectedly");
            let output = db.report_to_string(&errors).unwrap();
            pretty_assertions::assert_eq!(
                DisplayAsDebugWrapper(output.trim()),
                DisplayAsDebugWrapper(&expected[..]),
                "Failed the error test `{}`",
                test_name
            );
        }

        pub fn test_ok(test_name: &str, src: String, expected: String) {
            let src = std::borrow::Cow::Borrowed(&src[..]);
            let mut db = VesFileDatabase::new();
            let fid = db.add_snippet(src.clone());
            pretty_assertions::assert_eq!(
                DisplayAsDebugWrapper(clean_tree(
                    Parser::new(Lexer::new(&src), fid, &db)
                        .parse()
                        .unwrap()
                        .body
                        .into_iter()
                        .map(|stmt| stmt.ast_to_str())
                        .collect::<Vec<_>>()
                        .join("\n")
                )),
                DisplayAsDebugWrapper(expected),
                "Failed the test `{}`",
                test_name
            );
        }
    }
}
