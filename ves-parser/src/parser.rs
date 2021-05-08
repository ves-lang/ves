use crate::{
    ast::{self, Global, VarKind, AST},
    lexer::{self, Lexer, NextTokenExt, Token, TokenKind},
};
use std::{collections::HashSet, convert::Into};
use ves_error::{ErrCtx, FileId, Span, VesError, VesFileDatabase};

pub type ParseResult<T> = std::result::Result<T, VesError>;

// TODO: unify style and conventions in this file
// span_start, span_end
// do bounded constructs close themselves?
// -> e.g. blocks/param packs, do they consume the closing '}', ')'?
//    or is it up to the caller?

pub struct Parser<'a, 'b, N: AsRef<str>, S: AsRef<str>> {
    lexer: Lexer<'a>,
    previous: Token<'a>,
    current: Token<'a>,
    eof: Token<'a>,
    ex: ErrCtx,
    fid: FileId,
    scope_depth: usize,
    current_label: Token<'a>,
    globals: HashSet<Global<'a>>,
    db: &'b VesFileDatabase<N, S>,
    imports: Vec<ast::Import<'a>>,
    exports: Vec<ast::Symbol<'a>>,
}

impl<'a, 'b, N: AsRef<str> + std::fmt::Display + Clone, S: AsRef<str>> Parser<'a, 'b, N, S> {
    pub fn new(lexer: Lexer<'a>, fid: FileId, db: &'b VesFileDatabase<N, S>) -> Self {
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
            eof: eof.clone(),
            scope_depth: 0,
            current_label: eof,
            globals: HashSet::new(),
            ex: ErrCtx::new(),
            fid,
            db,
            imports: vec![],
            exports: vec![],
        }
    }

    pub fn parse(mut self) -> Result<AST<'a>, ErrCtx> {
        let mut parsing_imports = true;
        self.advance();
        let mut body = vec![];
        while !self.at_end() {
            if self.match_(&TokenKind::Import) {
                if parsing_imports {
                    match self.import() {
                        Ok(import) => {
                            self.match_(&TokenKind::Semi);
                            self.imports.push(ast::Import {
                                import,
                                resolved_path: None,
                            })
                        }
                        Err(err) => {
                            self.ex.record(err);
                            self.synchronize();
                        }
                    }
                } else {
                    self.ex.record(VesError::parse(
                        "Imports must appear first in a file",
                        self.previous.span.clone(),
                        self.fid,
                    ));
                    self.synchronize();
                }
            } else {
                parsing_imports = false;
                match self.export_stmt() {
                    Ok(Some(stmt)) => body.push(stmt),
                    Ok(None) => (),
                    Err(e) => {
                        self.ex.record(e);
                        self.synchronize();
                    }
                }
            }
        }

        self.db.mark_parsed(self.fid);

        if self.ex.had_error() {
            Err(self.ex)
        } else {
            Ok(AST::with(
                body,
                self.globals,
                self.imports,
                self.exports,
                self.fid,
            ))
        }
    }

    fn import(&mut self) -> ParseResult<ast::ImportStmt<'a>> {
        if self.match_(&TokenKind::LeftBrace) {
            // destructured
            let mut symbols = vec![];
            loop {
                let symbol = self.consume(&TokenKind::Identifier, "Expected import name")?;
                if self.match_(&TokenKind::As) {
                    let r#as = self.consume(&TokenKind::Identifier, "Expected alias")?;
                    symbols.push(ast::Symbol::Aliased(symbol, r#as));
                } else {
                    symbols.push(ast::Symbol::Bare(symbol));
                };

                if !self.match_(&TokenKind::Comma) {
                    break;
                }
            }
            self.consume(&TokenKind::RightBrace, "Expected '}'")?;
            self.consume(&TokenKind::From, "Expected 'from'")?;
            let path = self.import_path(false)?;
            Ok(ast::ImportStmt::Destructured(path, symbols))
        } else {
            // direct
            let path = self.import_path(true)?;
            Ok(ast::ImportStmt::Direct(path))
        }
    }

    fn import_path(&mut self, can_alias: bool) -> ParseResult<ast::ImportPath<'a>> {
        let (symbol, is_full_path) = if self.match_(&TokenKind::Identifier) {
            (self.previous.clone(), false)
        } else if self.match_(&TokenKind::String) {
            (self.previous.clone(), true)
        } else {
            return Err(VesError::parse(
                "Expected import name or path",
                self.previous.span.clone(),
                self.fid,
            ));
        };
        let symbol = if self.match_(&TokenKind::As) {
            if !can_alias {
                return Err(VesError::parse(
                    "Alias is invalid in this position",
                    self.previous.span.clone(),
                    self.fid,
                ));
            }
            let r#as = self.consume(&TokenKind::Identifier, "Expected alias name")?;
            ast::Symbol::Aliased(symbol, r#as)
        } else {
            if can_alias && is_full_path {
                return Err(VesError::parse(
                    "Direct path imports must be aliased",
                    self.previous.span.clone(),
                    self.fid,
                ));
            }
            ast::Symbol::Bare(symbol)
        };

        if is_full_path {
            Ok(ast::ImportPath::Full(symbol))
        } else {
            Ok(ast::ImportPath::Simple(symbol))
        }
    }

    fn export_stmt(&mut self) -> ParseResult<Option<ast::Stmt<'a>>> {
        if self.match_(&TokenKind::Export) {
            self.export().map(|v| {
                self.skip_semi();
                v
            })
        } else {
            Ok(Some(self.stmt(true)?))
        }
    }

    fn export(&mut self) -> ParseResult<Option<ast::Stmt<'a>>> {
        if self.match_(&TokenKind::LeftBrace) {
            // table export
            loop {
                let symbol = self.consume(&TokenKind::Identifier, "Expected export name")?;
                if self.match_(&TokenKind::As) {
                    let r#as = self.consume(&TokenKind::Identifier, "Expected alias name")?;
                    self.exports.push(ast::Symbol::Aliased(symbol, r#as));
                } else {
                    self.exports.push(ast::Symbol::Bare(symbol));
                };
                if !self.match_(&TokenKind::Comma) {
                    break;
                }
            }
            self.consume(&TokenKind::RightBrace, "Expected '}'")?;
            Ok(None)
        } else if self.match_any(&[
            TokenKind::Let,
            TokenKind::Mut,
            TokenKind::Fn,
            TokenKind::Struct,
        ]) {
            let stmt_start = self.previous.span.start;
            match self.previous.kind {
                TokenKind::Let => {
                    let binding = self.binding_expression(ast::VarKind::Let)?;
                    self.exports.push(ast::Symbol::Bare(binding.name.clone()));
                    let stmt_end = self.previous.span.end;
                    Ok(Some(ast::Stmt {
                        kind: ast::StmtKind::Var(vec![binding]),
                        span: stmt_start..stmt_end,
                    }))
                }
                TokenKind::Mut => {
                    let binding = self.binding_expression(ast::VarKind::Mut)?;
                    self.exports.push(ast::Symbol::Bare(binding.name.clone()));
                    let stmt_end = self.previous.span.end;
                    Ok(Some(ast::Stmt {
                        kind: ast::StmtKind::Var(vec![binding]),
                        span: stmt_start..stmt_end,
                    }))
                }
                TokenKind::Fn => {
                    let decl = self.fn_decl(true, false)?;
                    self.exports.push(ast::Symbol::Bare(decl.name.clone()));
                    let stmt_end = self.previous.span.end;
                    Ok(Some(ast::Stmt {
                        kind: ast::StmtKind::ExprStmt(box ast::Expr {
                            kind: ast::ExprKind::Fn(box decl),
                            span: stmt_start..stmt_end,
                        }),
                        span: stmt_start..stmt_end,
                    }))
                }
                TokenKind::Struct => {
                    let decl = self.struct_decl(true, false)?;
                    self.exports.push(ast::Symbol::Bare(decl.name.clone()));
                    let stmt_end = self.previous.span.end;
                    Ok(Some(ast::Stmt {
                        kind: ast::StmtKind::ExprStmt(box ast::Expr {
                            kind: ast::ExprKind::Struct(box decl),
                            span: stmt_start..stmt_end,
                        }),
                        span: stmt_start..stmt_end,
                    }))
                }
                _ => unreachable!(),
            }
        } else {
            Err(VesError::parse(
                "Only variables, functions, and structs may be exported",
                self.current.span.clone(),
                self.fid,
            ))
        }
    }

    fn stmt(&mut self, consume_semi: bool) -> ParseResult<ast::Stmt<'a>> {
        let label = if self.match_(&TokenKind::AtIdentifier) {
            let previous = self.previous.clone();
            self.consume(&TokenKind::Colon, "Expected a ':' after the label")?;
            Some(previous)
        } else {
            None
        };
        if label.is_some() && !self.check_any(&[TokenKind::Loop, TokenKind::For, TokenKind::While])
        {
            return Err(VesError::parse(
                "Only loops may be assigned a label",
                self.previous.span.clone(),
                self.fid,
            ));
        }

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
            TokenKind::Import,
            TokenKind::Export,
        ]) {
            match self.previous.kind {
                TokenKind::LeftBrace => self.block_stmt(),
                TokenKind::Let | TokenKind::Mut => self.var_decl(),
                TokenKind::Print => self.print_stmt(),
                TokenKind::Loop => self.loop_stmt(
                    label.unwrap_or_else(|| Self::synthesize_label(self.previous.span.clone())),
                ),
                TokenKind::For => self.for_loop_stmt(
                    label.unwrap_or_else(|| Self::synthesize_label(self.previous.span.clone())),
                ),
                TokenKind::While => self.while_loop_stmt(
                    label.unwrap_or_else(|| Self::synthesize_label(self.previous.span.clone())),
                ),
                TokenKind::Break => self.break_or_continue_stmt(ast::StmtKind::Break),
                TokenKind::Continue => self.break_or_continue_stmt(ast::StmtKind::Continue),
                TokenKind::Defer => self.defer_stmt(),
                TokenKind::Return => self.return_stmt(),
                TokenKind::Import => {
                    return Err(VesError::parse(
                        "Imports may only appear at the top level",
                        self.previous.span.clone(),
                        self.fid,
                    ))
                }
                TokenKind::Export => {
                    return Err(VesError::parse(
                        "Exports may only appear at the top level",
                        self.previous.span.clone(),
                        self.fid,
                    ))
                }
                _ => unreachable!(),
            }
            .map(|res| {
                self.skip_semi();
                res
            })
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
        self.consume(&TokenKind::RightBrace, "Expected a '}' after a block")?;
        Ok(body)
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

    fn print_stmt(&mut self) -> ParseResult<ast::Stmt<'a>> {
        let start = self.previous.span.start;
        self.consume(
            &TokenKind::LeftParen,
            "Expected a '(' after the print keyword",
        )?;
        let args = self.comma(true)?;
        self.consume(
            &TokenKind::RightParen,
            "Expected a ')' after the arguments to print",
        )?;
        Ok(ast::Stmt {
            kind: ast::StmtKind::Print(box args),
            span: start..self.previous.span.end,
        })
    }

    fn loop_stmt(&mut self, label: Token<'a>) -> ParseResult<ast::Stmt<'a>> {
        let span_start = self.previous.span.start;

        self.consume(
            &TokenKind::LeftBrace,
            "Expected a loop body after the keyword",
        )?;

        let previous_label = std::mem::replace(&mut self.current_label, label);
        let body = self.block_stmt()?;
        let label = std::mem::replace(&mut self.current_label, previous_label);

        let span_end = self.previous.span.end;
        Ok(ast::Stmt {
            kind: ast::StmtKind::Loop(box ast::Loop { body, label }),
            span: span_start..span_end,
        })
    }

    fn for_loop_stmt(&mut self, label: Token<'a>) -> ParseResult<ast::Stmt<'a>> {
        let span_start = self.previous.span.start;
        let previous_label = std::mem::replace(&mut self.current_label, label);

        let (binding, binding_span) = if self.match_(&TokenKind::Identifier) {
            (Some(self.previous.clone()), self.previous.span.clone())
        } else {
            (None, self.current.span.clone())
        };

        if self.match_(&TokenKind::In) {
            let variable = binding
                .ok_or_else(|| VesError::parse("Expected identifier", binding_span, self.fid))?;
            // for-each
            let start = self.expr(true)?;
            let iterator = if self.match_(&TokenKind::Range) {
                let inclusive = self.previous.lexeme == "..=";
                let end = self.expr(true)?;
                let step = if self.match_(&TokenKind::Comma) {
                    self.expr(true)?
                } else {
                    literal!(
                        self,
                        ast::LitValue::Number(1f64),
                        Token::new("1", self.previous.span.clone(), TokenKind::Number)
                    )
                };
                ast::IteratorKind::Range(ast::Range {
                    start,
                    end,
                    step,
                    inclusive,
                })
            } else {
                ast::IteratorKind::Expr(start)
            };
            self.consume(&TokenKind::LeftBrace, "Expected loop body")?;
            let body = self.block_stmt()?;
            let span_end = self.previous.span.end;
            let label = std::mem::replace(&mut self.current_label, previous_label);
            Ok(ast::Stmt {
                kind: ast::StmtKind::ForEach(box ast::ForEach {
                    variable,
                    iterator,
                    body,
                    label,
                }),
                span: span_start..span_end,
            })
        } else {
            let mut initializers = vec![];
            // since we already (maybe) parsed one binding identifier,
            // only continue if it actually exists
            if let Some(binding) = binding {
                if self.match_(&TokenKind::Equal) {
                    let name = binding;
                    let value = self.expr(true)?;
                    initializers.push(ast::Assignment { name, value });
                }
                while self.match_(&TokenKind::Comma) {
                    let name = self.consume(&TokenKind::Identifier, "Expected an identifier")?;
                    self.consume(
                        &TokenKind::Equal,
                        "Expected a '=' in an initializer binding",
                    )?;
                    let value = self.expr(true)?;
                    initializers.push(ast::Assignment { name, value });
                }
            }
            self.consume(&TokenKind::Semi, "Expected a ';' after the initializers")?;
            let condition = if !self.check(&TokenKind::Semi) {
                Some(self.expr(true)?)
            } else {
                None
            };
            self.consume(&TokenKind::Semi, "Expected a ';' after the condition ")?;
            let increment = if !self.check(&TokenKind::LeftBrace) {
                Some(self.expr(true)?)
            } else {
                None
            };
            self.consume(&TokenKind::LeftBrace, "Expected loop body")?;
            let body = self.block_stmt()?;
            let span_end = self.previous.span.end;
            let label = std::mem::replace(&mut self.current_label, previous_label);
            Ok(ast::Stmt {
                kind: ast::StmtKind::For(box ast::For {
                    initializers,
                    condition,
                    increment,
                    body,
                    label,
                }),
                span: span_start..span_end,
            })
        }
    }

    fn while_loop_stmt(&mut self, label: Token<'a>) -> ParseResult<ast::Stmt<'a>> {
        let span_start = self.previous.span.start;
        let condition = self.condition()?;
        self.consume(&TokenKind::LeftBrace, "Expected loop body")?;
        let previous_label = std::mem::replace(&mut self.current_label, label);
        let body = self.block_stmt()?;
        let label = std::mem::replace(&mut self.current_label, previous_label);
        let span_end = self.previous.span.end;
        Ok(ast::Stmt {
            kind: ast::StmtKind::While(box ast::While {
                condition,
                body,
                label,
            }),
            span: span_start..span_end,
        })
    }

    fn break_or_continue_stmt<F>(&mut self, constructor: F) -> ParseResult<ast::Stmt<'a>>
    where
        F: Fn(Token<'a>) -> ast::StmtKind,
    {
        let start = self.previous.span.start;
        let label = if self.match_(&TokenKind::AtIdentifier) {
            self.previous.clone()
        } else {
            self.current_label.clone()
        };

        Ok(ast::Stmt {
            kind: constructor(label),
            span: start..self.previous.span.end,
        })
    }

    fn defer_stmt(&mut self) -> ParseResult<ast::Stmt<'a>> {
        let span_start = self.previous.span.start;
        let call = if self.match_(&TokenKind::LeftBrace) {
            let body_start = self.previous.span.start;
            let body = self.block()?;
            let body_end = self.previous.span.end;
            let body_span = body_start..body_end;
            let (line, column) = self.db.location(self.fid, &body_span);
            let name = Token::new(
                format!("[defer@{}:{}]", line, column),
                self.previous.span.clone(),
                TokenKind::Identifier,
            );
            ast::Call {
                callee: ast::Expr {
                    kind: ast::ExprKind::Fn(box ast::FnInfo {
                        name,
                        params: ast::Params::default(),
                        body,
                        kind: ast::FnKind::Function,
                    }),
                    span: body_span,
                },
                args: vec![],
                tco: false,
                rest: false,
            }
        } else if let ast::ExprKind::Call(call) = self.call()?.kind {
            *call
        } else {
            return Err(VesError::parse(
                "Only calls and blocks may be deferred",
                span_start..self.previous.span.end,
                self.fid,
            ));
        };
        let span_end = self.previous.span.end;
        Ok(ast::Stmt {
            kind: ast::StmtKind::Defer(box call),
            span: span_start..span_end,
        })
    }

    fn return_stmt(&mut self) -> ParseResult<ast::Stmt<'a>> {
        let span_start = self.previous.span.start;
        let expr = if !self.match_(&TokenKind::Semi) && !self.check(&TokenKind::RightBrace) {
            Some(box self.expr(true)?)
        } else {
            None
        };
        let span_end = self.previous.span.end;
        Ok(ast::Stmt {
            kind: ast::StmtKind::Return(expr),
            span: span_start..span_end,
        })
    }

    fn binding_expression(&mut self, kind: VarKind) -> ParseResult<ast::Var<'a>> {
        let ident = self.consume(
            &TokenKind::Identifier,
            "Expected a variable name after the keyword or comma",
        );

        let init = if self.match_(&TokenKind::Equal) {
            let ident = ident.clone();
            Some(self.expr(true).map_err(|e| {
                let _ = ident.map_err(|e| self.ex.record(e));
                e
            })?)
        } else {
            None
        };

        let ident = ident?;
        if kind == VarKind::Let && init.is_none() {
            self.ex.record(VesError::let_without_value(
                format!(
                    "Immutable variable `{}` must be initialized at declaration",
                    ident.lexeme
                ),
                ident.span.clone(),
                self.fid,
            ));
        }

        remember_if_global!(self, ident, kind);

        Ok(ast::Var {
            kind,
            name: ident,
            initializer: init,
            n_uses: std::rc::Rc::new(std::cell::Cell::new(0)),
        })
    }

    fn expr_stmt(&mut self, consume_semi: bool) -> ParseResult<ast::Stmt<'a>> {
        let span_start = self.previous.span.start;
        let expr = self.comma(false)?;
        let span_end = self.current.span.end;

        if consume_semi {
            self.skip_semi();
        }

        Ok(ast::Stmt {
            kind: ast::StmtKind::ExprStmt(Box::new(expr)),
            span: span_start..span_end,
        })
    }

    fn comma(&mut self, is_sub_expr: bool) -> ParseResult<ast::Expr<'a>> {
        let span_start = self.previous.span.start;
        let mut exprs = vec![self.expr(is_sub_expr)?];
        while self.match_(&TokenKind::Comma) {
            exprs.push(self.expr(true)?);
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
                kind: ast::ExprKind::Spread(box self.expr(true)?),
                span: span_start..self.previous.span.start,
            })
        } else {
            self.expr(true)
        }
    }

    fn expr(&mut self, is_sub_expr: bool) -> ParseResult<ast::Expr<'a>> {
        if self.match_any(&[
            TokenKind::Struct,
            TokenKind::Fn,
            TokenKind::If,
            TokenKind::Do,
        ]) {
            match self.previous.kind {
                TokenKind::Struct => self.struct_decl_expr(is_sub_expr),
                TokenKind::Fn => self.fn_decl_expr(is_sub_expr),
                TokenKind::If => self.if_expr(),
                TokenKind::Do => self.do_block_expr(),
                _ => unreachable!(),
            }
        } else {
            self.assignment()
        }
    }

    fn struct_decl_expr(&mut self, is_sub_expr: bool) -> ParseResult<ast::Expr<'a>> {
        let span_start = self.previous.span.start;
        let decl = self.struct_decl(false, is_sub_expr)?;
        let span_end = self.previous.span.end;
        Ok(ast::Expr {
            kind: ast::ExprKind::Struct(box decl),
            span: span_start..span_end,
        })
    }

    fn struct_decl(
        &mut self,
        require_name: bool,
        is_sub_expr: bool,
    ) -> ParseResult<ast::StructInfo<'a>> {
        // parse struct name, or generate it
        let struct_name = if self.match_(&TokenKind::Identifier) {
            if !is_sub_expr {
                remember_if_global!(self, self.previous, ast::VarKind::Struct);
            }
            self.previous.clone()
        } else {
            if require_name {
                return Err(VesError::parse(
                    "Expected struct name",
                    self.previous.span.clone(),
                    self.fid,
                ));
            }
            let (line, column) = self.db.location(self.fid, &self.previous.span);
            Token::new(
                format!("[struct@{}:{}]", line, column),
                self.previous.span.clone(),
                TokenKind::Identifier,
            )
        };
        // parse fields
        let fields = if self.match_(&TokenKind::LeftParen) {
            let fields = self.param_pack(ParamListKind::StructFields)?;
            self.consume(&TokenKind::RightParen, "Expected a closing `)`")?;
            fields
        } else {
            ast::Params::default()
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
                let prop_name = self
                    .consume_any(
                        &[TokenKind::Identifier, TokenKind::AtIdentifier],
                        "Expected a method, static field or static method declaration",
                    )
                    .map_err(|mut e| {
                        if self.current.kind == TokenKind::Fn {
                            e.kind = ves_error::VesErrorKind::FnBeforeMethod;
                            e.msg =
                                "Instance and static methods do not require `fn` to be declared"
                                    .into();
                        }
                        e
                    })?;
                // QQQ(moscow): do we have static magic methods? if no, it should be an error here
                // TODO: detect duplicate properties here? (`@add` and `add` are duplicate)

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
                        kind: ast::FnKind::Initializer,
                    }));
                } else if self.match_(&TokenKind::LeftParen) {
                    // this is a method
                    let params = self.param_pack(ParamListKind::Method)?;
                    self.consume(&TokenKind::RightParen, "Expected a closing `)`")?;
                    let body = self.fn_decl_body()?;
                    if params.is_instance_method_params() {
                        methods.push(ast::FnInfo {
                            kind: match prop_name.kind {
                                TokenKind::Identifier => ast::FnKind::Method,
                                TokenKind::AtIdentifier => ast::FnKind::MagicMethod,
                                _ => unreachable!(),
                            },
                            name: prop_name,
                            params,
                            body,
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
                        Some(self.expr(true)?)
                    } else {
                        None
                    };
                    r#static.fields.push((prop_name, value));
                }
            }
        }
        let mut field_initializers = fields
            .default
            .iter()
            .map(|(name, value, _)| struct_field_init_stmt(name, value))
            .collect::<Vec<ast::Stmt<'_>>>();
        let initializer = match initializer {
            Some(mut initializer) => {
                std::mem::swap(&mut initializer.body.body, &mut field_initializers);
                initializer.body.body.extend(field_initializers);
                Some(initializer)
            }
            None if !field_initializers.is_empty() => Some(ast::Initializer {
                body: ast::FnInfo {
                    name: Token::new("init", struct_name.span.clone(), TokenKind::Identifier),
                    params: ast::Params::default(),
                    body: field_initializers,
                    kind: ast::FnKind::Initializer,
                },
                may_escape: false,
            }),
            _ => None,
        };
        Ok(ast::StructInfo {
            name: struct_name,
            fields,
            methods,
            initializer,
            r#static,
        })
    }

    fn fn_decl_expr(&mut self, is_sub_expr: bool) -> ParseResult<ast::Expr<'a>> {
        let span_start = self.previous.span.start;
        let decl = self.fn_decl(false, is_sub_expr)?;
        let span_end = self.previous.span.end;
        Ok(ast::Expr {
            kind: ast::ExprKind::Fn(box decl),
            span: span_start..span_end,
        })
    }

    fn fn_decl(&mut self, require_name: bool, is_sub_expr: bool) -> ParseResult<ast::FnInfo<'a>> {
        let name = if self.match_(&TokenKind::Identifier) {
            if !is_sub_expr {
                remember_if_global!(self, self.previous, ast::VarKind::Fn);
            }
            self.previous.clone()
        } else {
            if require_name {
                return Err(VesError::parse(
                    "Expected function name",
                    self.previous.span.clone(),
                    self.fid,
                ));
            }
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
        let params = self.param_pack(ParamListKind::Function)?;
        self.consume(&TokenKind::RightParen, "Expected a closing `)`")?;
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
            let expr = self.expr(true)?;
            Ok(vec![ast::Stmt {
                span: body_span_start..expr.span.end,
                kind: ast::StmtKind::Return(Some(box expr)),
            }])
        } else if self.match_(&TokenKind::LeftBrace) {
            Ok(self.block()?)
        } else {
            Err(VesError::parse(
                "Expected a function body",
                self.previous.span.clone(),
                self.fid,
            ))
        }
    }

    // TODO: test new cases
    fn param_pack(&mut self, kind: ParamListKind) -> ParseResult<ast::Params<'a>> {
        let mut parsing_default = false;
        let mut positional = vec![];
        let mut default = vec![];
        let mut rest = None;
        while !self.check(&TokenKind::RightParen) {
            if self.match_(&TokenKind::Ellipsis) {
                if kind == ParamListKind::StructFields {
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
                let is_mutable = if self.match_(&TokenKind::Mut) {
                    if kind == ParamListKind::StructFields {
                        return Err(VesError::parse(
                            "Struct fields do not have mutability modifiers",
                            self.previous.span.clone(),
                            self.fid,
                        ));
                    }
                    true
                } else {
                    false
                };
                let name = self.consume_any(
                    &[TokenKind::Identifier, TokenKind::Self_],
                    "Expected a parameter name",
                )?;
                if name.lexeme == "self" && kind != ParamListKind::Method {
                    return Err(VesError::parse(
                        "'self' may only be used in methods",
                        self.previous.span.clone(),
                        self.fid,
                    ));
                }
                if !positional.is_empty() && kind == ParamListKind::Method && name.lexeme == "self"
                {
                    return Err(VesError::parse(
                        "'self' must be the first parameter",
                        self.previous.span.clone(),
                        self.fid,
                    ));
                }
                if is_mutable && kind == ParamListKind::Method && name.lexeme == "self" {
                    return Err(VesError::parse(
                        "'self' may not be mutable",
                        self.previous.span.clone(),
                        self.fid,
                    ));
                }
                let value = if self.match_(&TokenKind::Equal) {
                    if kind == ParamListKind::Method && name.lexeme == "self" {
                        return Err(VesError::parse(
                            "'self' may not have a default value",
                            self.previous.span.clone(),
                            self.fid,
                        ));
                    }
                    Some(self.expr(true)?)
                } else {
                    None
                };
                match value {
                    Some(value) => {
                        parsing_default = true;
                        default.push((name, value, is_mutable));
                    }
                    None => {
                        if parsing_default {
                            return Err(VesError::parse(
                                    "Positional arguments may not appear after arguments with default values",
                                    self.previous.span.clone(),
                                    self.fid,
                                ));
                        }
                        positional.push((name, is_mutable));
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
        let if_ = self.if_()?;
        let span_end = self.previous.span.end;
        Ok(ast::Expr {
            span: span_start..span_end,
            kind: ast::ExprKind::If(box if_),
        })
    }

    fn if_(&mut self) -> ParseResult<ast::If<'a>> {
        let condition = self.condition()?;
        let then = self.do_block()?;
        let mut otherwise = None;
        if self.match_(&TokenKind::Else) {
            if self.match_(&TokenKind::If) {
                otherwise = Some(ast::Else::If(box self.if_()?));
            } else {
                otherwise = Some(ast::Else::Block(box self.do_block()?));
            }
        }
        Ok(ast::If {
            condition,
            then,
            otherwise,
        })
    }

    fn condition(&mut self) -> ParseResult<ast::Condition<'a>> {
        if self.match_any(&[TokenKind::Ok, TokenKind::Err]) {
            let which = self.previous.clone();
            self.consume(&TokenKind::LeftParen, "Expected '('")?;
            let ident = self.consume(&TokenKind::Identifier, "Expected identifier")?;
            self.consume(&TokenKind::RightParen, "Expected ')'")?;
            self.consume(&TokenKind::Equal, "Expected assignment")?;
            let value = self.expr(true)?;
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
            let value = self.expr(true)?;
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

        self.consume(&TokenKind::LeftBrace, "Expected an opening `{`")?;
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
                        value: desugar_assignment(operator, expr.clone(), self.expr(true)?),
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
                            value: desugar_assignment(operator, expr.clone(), self.expr(true)?),
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
                            value: desugar_assignment(operator, expr.clone(), self.expr(true)?),
                        }),
                        span: span_start..self.current.span.end,
                    }
                }
                _ => {
                    let kind = check_assignment_target(&expr, true);
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
                TokenKind::EqualEqual => binary!(expr, Equal, self.comparison()?),
                TokenKind::BangEqual => binary!(expr, NotEqual, self.comparison()?),
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
                TokenKind::More => binary!(expr, GreaterThan, self.comparison()?),
                TokenKind::Less => binary!(expr, LessThan, self.comparison()?),
                TokenKind::MoreEqual => binary!(expr, GreaterEqual, self.comparison()?),
                TokenKind::LessEqual => binary!(expr, LessEqual, self.comparison()?),
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
                TokenKind::Minus => binary!(expr, Subtract, self.factor()?),
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
        // expr % expr
        while self.match_any(&[TokenKind::Star, TokenKind::Slash, TokenKind::Percent]) {
            expr = match self.previous.kind {
                TokenKind::Star => binary!(expr, Multiply, self.power()?),
                TokenKind::Slash => binary!(expr, Divide, self.power()?),
                TokenKind::Percent => binary!(expr, Remainder, self.power()?),
                _ => unreachable!(),
            }
        }
        Ok(expr)
    }

    fn power(&mut self) -> ParseResult<ast::Expr<'a>> {
        let mut expr = self.unary()?;
        // expr ** expr
        while self.match_(&TokenKind::Power) {
            expr = binary!(expr, Power, self.power()?);
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
                TokenKind::Minus => unary!(Negate, self.unary()?, op),
                // try <expr>
                TokenKind::Try => unary!(Try, self.unary()?, op),
                // ok <expr>
                TokenKind::Ok => unary!(WrapOk, self.unary()?, op),
                // err <expr>
                TokenKind::Err => unary!(WrapErr, self.unary()?, op),
                // ++<expr> or --<expr>
                TokenKind::Increment | TokenKind::Decrement => {
                    let kind = self.previous.kind.clone();
                    let expr = self.call()?;
                    let assign_kind = check_assignment_target(&expr, true);
                    if assign_kind == AssignmentKind::Valid {
                        ast::Expr {
                            span: op.span.start..expr.span.end,
                            kind: ast::ExprKind::PrefixIncDec(box ast::IncDec {
                                expr,
                                kind: ast::IncDecKind::from(kind),
                            }),
                        }
                    } else {
                        return Err(self
                            .invalid_assignment_error(assign_kind, op.span.start..expr.span.end));
                    }
                }
                _ => unreachable!(),
            });
        }
        self.call()
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
                    let args = self.arg_list()?;
                    self.consume(&TokenKind::RightParen, "Expected ')'")?;
                    ast::Expr {
                        span: expr.span.start..self.previous.span.end,
                        kind: ast::ExprKind::Call(box ast::Call {
                            callee: expr,
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
                    let key = self.expr(true)?;
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
        // 'self', some, identifier
        if self.match_any(&[TokenKind::Self_, TokenKind::Some, TokenKind::Identifier]) {
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
                        "Failed to parse the number",
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
        if self.match_(&TokenKind::InterpolatedString(Default::default())) {
            let span_start = self.previous.span.start;
            let mut fragments = vec![];
            let previous = std::mem::replace(&mut self.previous, self.eof.clone());
            if let TokenKind::InterpolatedString(fstr) = previous.kind {
                if let Some(error) = fstr.error() {
                    return Err(VesError::parse(error, previous.span.clone(), self.fid));
                }
                for frag in fstr.fragments.into_iter() {
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
                            fragments.push(ast::FStringFrag::Expr(subparser.expr(true)?));
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
            let expr = self.comma(true)?;
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
            if self.previous.kind == TokenKind::EOF {
                "File ended unexpected".to_string()
            } else {
                format!(
                    "Unexpected token `{}` ({:?})",
                    self.current.lexeme, self.current.kind
                )
            },
            self.current.span.clone(),
            self.fid,
        ))
    }

    fn parse_map_entry(&mut self) -> ParseResult<ast::MapEntry<'a>> {
        if self.match_(&TokenKind::Ellipsis) {
            Ok(ast::MapEntry::Spread(self.expr(true)?))
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
                let key = self.expr(true)?;
                self.consume(
                    &TokenKind::RightBracket,
                    "Expected ']' after key expression",
                )?;
                key
            };

            let value = if self.match_(&TokenKind::Colon) {
                self.expr(true)?
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

    fn synthesize_label(span: Span) -> Token<'a> {
        Token::new(
            std::borrow::Cow::Owned(format!("<@label: {:?}>", span)),
            span,
            TokenKind::AtIdentifier,
        )
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
    fn consume<Msg: Into<String>>(
        &mut self,
        kind: &TokenKind<'a>,
        err_msg: Msg,
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
    fn consume_any<Msg: Into<String>>(
        &mut self,
        kinds: &[TokenKind<'a>],
        err_msg: Msg,
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

    #[inline(always)]
    fn check_any(&mut self, kinds: &[TokenKind<'a>]) -> bool {
        for kind in kinds {
            if std::mem::discriminant(kind) == std::mem::discriminant(&self.current.kind) {
                return true;
            }
        }
        false
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
                TokenKind::Export,
                TokenKind::Import,
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
        if self.previous.kind == TokenKind::Error {
            self.ex.record(VesError::lex(
                format!("Unexpected character sequence `{}`", self.previous.lexeme),
                self.previous.span.clone(),
                self.fid,
            ));
            self.advance();
        }
        self.previous.clone()
    }

    /// Check if the parser has reached EOF
    #[inline(always)]
    fn at_end(&self) -> bool {
        self.current.kind == TokenKind::EOF
    }
}

fn struct_field_init_stmt<'a>(name: &Token<'a>, value: &ast::Expr<'a>) -> ast::Stmt<'a> {
    let span = name.span.start..value.span.end;
    ast::Stmt {
        span: span.clone(),
        kind: ast::StmtKind::ExprStmt(box ast::Expr {
            span: span.clone(),
            kind: ast::ExprKind::If(box ast::If {
                condition: ast::Condition {
                    value: ast::Expr {
                        span: span.clone(),
                        kind: ast::ExprKind::Binary(
                            ast::BinOpKind::Is,
                            box ast::Expr {
                                span: span.clone(),
                                kind: ast::ExprKind::GetProp(box ast::GetProp {
                                    node: ast::Expr {
                                        span: span.clone(),
                                        kind: ast::ExprKind::Variable(Token::new(
                                            "self",
                                            span.clone(),
                                            TokenKind::Self_,
                                        )),
                                    },
                                    field: name.clone(),
                                    is_optional: false,
                                }),
                            },
                            box ast::Expr {
                                span: span.clone(),
                                kind: ast::ExprKind::Lit(box ast::Lit {
                                    token: Token::new("none", span.clone(), TokenKind::None),
                                    value: ast::LitValue::None,
                                }),
                            },
                        ),
                    },
                    pattern: ast::ConditionPattern::Value,
                },
                then: ast::DoBlock {
                    statements: vec![ast::Stmt {
                        span: span.clone(),
                        kind: ast::StmtKind::ExprStmt(box ast::Expr {
                            span: span.clone(),
                            kind: ast::ExprKind::SetProp(box ast::SetProp {
                                node: ast::Expr {
                                    span: span.clone(),
                                    kind: ast::ExprKind::Variable(Token::new(
                                        "self",
                                        span.clone(),
                                        TokenKind::Self_,
                                    )),
                                },
                                field: name.clone(),
                                value: value.clone(),
                            }),
                        }),
                    }],
                    value: None,
                },
                otherwise: None,
            }),
        }),
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
        TokenKind::MinusEqual => desugar!(receiver, Subtract, value),
        TokenKind::StarEqual => desugar!(receiver, Multiply, value),
        TokenKind::SlashEqual => desugar!(receiver, Divide, value),
        TokenKind::PowerEqual => desugar!(receiver, Power, value),
        TokenKind::PercentEqual => desugar!(receiver, Remainder, value),
        _ => unreachable!(),
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum ParamListKind {
    Function,
    Method,
    StructFields,
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
#[ves_testing::ves_test_suite]
mod suite {
    use super::*;
    use ast2str::AstToStr;

    #[ves_tests = "tests"]
    mod parser {
        #[ok_callback]
        use super::parse as parse_ok;

        #[err_callback]
        use super::parse as parse_err;
    }

    fn parse<'a>(
        src: std::borrow::Cow<'a, str>,
        fid: FileId,
        db: &mut VesFileDatabase<String, std::borrow::Cow<'a, str>>,
    ) -> Result<String, ErrCtx> {
        Parser::new(Lexer::new(&src), fid, &db).parse().map(|ast| {
            let imports = ast
                .imports
                .into_iter()
                .map(|import| import.ast_to_str())
                .collect::<Vec<_>>()
                .join("\n");
            let exports = ast
                .exports
                .into_iter()
                .map(|import| import.ast_to_str())
                .collect::<Vec<_>>()
                .join("\n");
            let body = ast
                .body
                .into_iter()
                .map(|stmt| stmt.ast_to_str())
                .collect::<Vec<_>>()
                .join("\n");
            format!(
                "{}{}{}{}{}",
                imports,
                if !imports.is_empty() { "\n" } else { "" },
                exports,
                if !exports.is_empty() { "\n" } else { "" },
                body
            )
        })
    }
}
