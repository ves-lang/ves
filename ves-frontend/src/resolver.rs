use std::borrow::Cow;

use ves_error::{ErrCtx, FileId, VesError, VesErrorKind};
use ves_parser::{ast::*, lexer::Token, Span};

use crate::env::Env;
use crate::resolver_definitions::{LoopKind, NameKind, ScopeKind, VarUsage};

// TODO: some kind of settings struct?

/// A resolver pass that performs a series of checks on the AST.
///
/// ## Performed Checks
/// TODO: list the checks here
#[derive(Clone, Debug)]
pub struct Resolver<'a> {
    /// The id of the file being resolved.
    file_id: FileId,
    /// The environment containing the names used by the program.
    env: Env<Cow<'a, str>, VarUsage>,
    /// The kind of the scope being compiled.
    scope_kind: ScopeKind,
    /// The kind of the loop being compiled.
    loop_kind: LoopKind,
    /// Whether a struct is currently being resolved.
    is_in_struct: bool,
    /// The stack of loop labels currently in use.
    labels: Vec<Token<'a>>,
    /// The name of the function currently being resolved.
    function_name: Option<Cow<'a, str>>,
    /// The name of the struct currently being resolved.
    struct_name: Option<Cow<'a, str>>,
}

impl<'a> Resolver<'a> {
    /// Creates a new resolver instance.
    pub fn new() -> Self {
        Self {
            function_name: None,
            struct_name: None,
            loop_kind: LoopKind::None,
            scope_kind: ScopeKind::Global,
            is_in_struct: false,
            labels: Vec::new(),
            file_id: FileId::anon(),
            env: Env::default(),
        }
    }

    /// Resolves the given AST. Returns the used [`ErrCtx`] containing warnings, errors, and suggestions.
    pub fn resolve(mut self, ast: &mut AST<'a>) -> Result<ErrCtx, ErrCtx> {
        self.file_id = ast.file_id;
        let mut ex = ErrCtx::default();

        for stmt in &mut ast.body {
            self.resolve_stmt(stmt, &mut ex);
        }

        // self.check_variable_usage(&mut ex);

        if ex.had_error() {
            Err(ex)
        } else {
            Ok(ex)
        }
    }

    fn resolve_stmt(&mut self, stmt: &mut Stmt<'a>, ex: &mut ErrCtx) {
        match &mut stmt.kind {
            StmtKind::Var(vars) => {
                for var in vars {
                    // We have to resolve the variable first to allow shadowing.
                    if let Some(ref mut init) = var.initializer {
                        self.resolve_expr(init, ex);
                    } else if var.kind == VarKind::Let {
                        Self::error(
                            format!(
                                "Immutable variable `{}` must be explicitly initialized",
                                var.name.lexeme
                            ),
                            var.name.span.clone(),
                            ex,
                        );
                    }

                    self.declare(
                        &var.name,
                        match var.kind {
                            VarKind::Let => NameKind::Let,
                            VarKind::Mut => NameKind::Mut,
                        },
                        ex,
                    );
                    // Only `let` variables are marked as assigned at this point.
                    if var.initializer.is_some() && var.kind == VarKind::Let {
                        self.assign(&var.name, ex);
                    }
                }
            }
            StmtKind::For(_) => unimplemented!(),
            StmtKind::ForEach(_) => unimplemented!(),
            StmtKind::While(_) => unimplemented!(),
            StmtKind::Block(_) => unimplemented!(),
            StmtKind::ExprStmt(_) => unimplemented!(),
            StmtKind::Print(_) => unimplemented!(),
            StmtKind::If(_) => unimplemented!(),
            StmtKind::Return(_) => unimplemented!(),
            StmtKind::Break(_) => unimplemented!(),
            StmtKind::Continue(_) => unimplemented!(),
            StmtKind::Defer(_) => unimplemented!(),
            StmtKind::_Empty => unimplemented!(),
        }
    }

    fn resolve_expr(&mut self, _expr: &mut Expr<'a>, _ex: &mut ErrCtx) {
        unimplemented!()
    }

    fn declare(&mut self, name: &Token<'a>, kind: NameKind, ex: &mut ErrCtx) {
        if let Some(vu) = self.env.in_current_scope(&name.lexeme) {
            if !vu.used {
                Self::error_of_kind(
                    VesErrorKind::AttemptedToShadowUnusedLocal(vu.span.clone()),
                    format!(
                        "Attempted to shadow an unused local variable `{}`",
                        name.lexeme
                    ),
                    name.span.clone(),
                    ex,
                )
                .mark_last_error_as_warning();
            }
        }

        self.env.add(
            name.lexeme.clone(),
            VarUsage {
                kind,
                declared: true,
                assigned: false,
                used: false,
                span: name.span.clone(),
            },
        );
    }

    fn assign<'b>(&mut self, name: &'b Token<'a>, ex: &mut ErrCtx) {
        match self.env.get_mut(&name.lexeme) {
            Some(v) => {
                if v.is_let() && v.assigned {
                    Self::error(
                        format!("Cannot assign twice to the immutable variable {}. Consider replacing `let` with `mut`", name.lexeme),
                        name.span.clone(),
                        ex
                    );
                }
                v.assigned = true;
            }
            None => self.undefined_variable_error(name, ex),
        }
    }

    fn undefined_variable_error(&self, token: &Token<'a>, ex: &mut ErrCtx) {
        if !is_reserved_identifier(&token) {
            Self::error(
                format!("Undefined variable `{}`", token.lexeme),
                token.span.clone(),
                ex,
            );
        }
    }

    fn error<S: Into<String>>(msg: S, span: Span, ex: &mut ErrCtx) -> &mut ErrCtx {
        Self::error_of_kind(VesErrorKind::Resolution, msg, span, ex)
    }

    fn error_of_kind<S: Into<String>>(
        kind: VesErrorKind,
        msg: S,
        span: Span,
        ex: &mut ErrCtx,
    ) -> &mut ErrCtx {
        ex.record(VesError::new(msg, span, kind, ex.local_file_id));
        ex
    }
}

impl<'a> Default for Resolver<'a> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
pub mod tests {
    // use super::*;
    // use ves_parser::ast::Ptr;

    #[ignore]
    #[test]
    fn test_cannot_assign_to_let() {
        // TODO: test this after the parser is ready.
    }
}
