use std::borrow::Cow;

use ves_error::{ErrCtx, FileId, VesError, VesErrorKind};
use ves_parser::{
    ast::*,
    lexer::{Token, TokenKind},
    Span,
};

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
            StmtKind::For(r#for) => {
                self.env.push();

                r#for.initializers.iter_mut().for_each(|init| {
                    self.resolve_expr(&mut init.value, ex);
                    self.declare(&init.name, NameKind::Mut, ex);
                    self.assign(&init.name, ex);
                });

                if let Some(ref mut cond) = r#for.condition {
                    self.resolve_expr(cond, ex);
                }
                if let Some(ref mut inc) = r#for.increment {
                    self.resolve_expr(inc, ex);
                }

                self.declare_loop_label(&r#for.label, ex);

                let prev_loop = self.loop_kind;
                self.loop_kind = LoopKind::For;
                self.resolve_stmt(&mut r#for.body, ex);
                self.loop_kind = prev_loop;

                self.env.pop();
            }
            StmtKind::ForEach(r#for) => {
                self.env.push();

                self.resolve_expr(&mut r#for.iterator, ex);

                self.declare(&r#for.variable, NameKind::Let, ex);
                self.assign(&r#for.variable, ex);

                self.declare_loop_label(&r#for.label, ex);

                let prev_loop = self.loop_kind;
                self.loop_kind = LoopKind::ForEach;
                self.resolve_stmt(&mut r#for.body, ex);
                self.loop_kind = prev_loop;

                self.env.pop();
            }
            StmtKind::While(box While {
                ref mut condition,
                ref mut body,
                ref label,
            }) => {
                self.env.push();

                self.resolve_condition(condition, ex);

                self.declare_loop_label(label, ex);

                let prev_loop = self.loop_kind;
                self.loop_kind = LoopKind::While;
                self.resolve_stmt(body, ex);
                self.loop_kind = prev_loop;

                self.env.pop();
            }
            StmtKind::Block(statements) => {
                let prev_kind = self.scope_kind;
                if self.scope_kind == ScopeKind::Global {
                    self.scope_kind = ScopeKind::Local;
                }
                self.env.push();
                self.resolve_block(statements, ex);
                self.env.pop();
                self.scope_kind = prev_kind;
            }
            StmtKind::ExprStmt(expr) => self.resolve_expr(expr, ex),
            StmtKind::Print(expr) => self.resolve_expr(expr, ex),
            StmtKind::Return(value) => {
                if let Some(ref mut expr) = value {
                    self.resolve_expr(expr, ex);
                }

                match self.scope_kind {
                    ScopeKind::Global | ScopeKind::Local => {
                        Self::error("Cannot return outside of a function", stmt.span.clone(), ex);
                    }
                    // init {} blocks cannot return values
                    ScopeKind::Initializer if value.is_some() => {
                        Self::error(
                            "Cannot return a value from an init block",
                            stmt.span.clone(),
                            ex,
                        );
                    }
                    // But empty returns are fine, so we need to patch them to return `self`.
                    ScopeKind::Initializer => {
                        *value = Some(box Expr {
                            kind: ExprKind::Variable(Token::new(
                                "self",
                                stmt.span.clone(),
                                TokenKind::Self_,
                            )),
                            span: stmt.span.clone(),
                        });
                    }
                    ScopeKind::Function | ScopeKind::AssocMethod | ScopeKind::Method => {}
                }
            }
            StmtKind::Break(label) => {
                if let LoopKind::None = self.loop_kind {
                    Self::error("Cannot break outside of a loop", stmt.span.clone(), ex);
                }
                if self.env.get(&label.lexeme).is_none() {
                    self.undefined_variable_error(label, ex);
                }
            }
            StmtKind::Continue(label) => {
                if let LoopKind::None = self.loop_kind {
                    Self::error("Cannot continue outside of a loop", stmt.span.clone(), ex);
                }
                if self.env.get(&label.lexeme).is_none() {
                    self.undefined_variable_error(label, ex);
                }
            }
            StmtKind::Defer(defer) => {
                // This should never happen, but we'll look out for it just in case.
                if !matches!(defer.kind, ExprKind::Call(_)) {
                    Self::error(
                        "A defer statement may only contain call expressions",
                        defer.span.clone(),
                        ex,
                    );
                }
                self.resolve_expr(defer, ex);
            }
            StmtKind::_Empty => {}
        }
    }

    fn resolve_block(&mut self, statements: &mut Vec<Stmt<'a>>, ex: &mut ErrCtx) {
        if let Some(StmtKind::Return(Some(ref mut expr))) =
            statements.last_mut().map(|s| &mut s.kind)
        {
            // TODO: detect more things here
            #[allow(clippy::single_match)]
            match &mut expr.kind {
                ExprKind::Call(box Call { ref mut tco, .. }) => *tco = true,
                ExprKind::If(box If {
                    ref mut then,
                    otherwise: Some(ref mut otherwise),
                    ..
                }) => {
                    // If both do blocks of the if end with a call, we can enable TCO on both them without rewriting the AST since
                    // the TCO call instruction automatically cleans up the stack. Thus, the following code:
                    //
                    //  return if (...) { call() } else { call() }
                    //
                    // Becomes equivalent to:
                    //
                    // if (...) { return tco_call() } else { return tco_call() }
                    match (
                        self.find_call_in_do_block(then),
                        self.find_call_in_do_block(otherwise),
                    ) {
                        (Some(then_call), Some(else_call)) => {
                            then_call.tco = true;
                            else_call.tco = true;
                        }
                        _ => {}
                    }
                }
                _ => (),
            }
        }

        statements
            .iter_mut()
            .for_each(|stmt| self.resolve_stmt(stmt, ex));
    }

    fn find_call_in_do_block<'b>(&self, block: &'b mut DoBlock<'a>) -> Option<&'b mut Call<'a>> {
        match block.value {
            Some(Expr {
                kind: ExprKind::Call(box ref mut call),
                ..
            }) => Some(call),
            _ => None,
        }
    }

    fn resolve_do_block(&mut self, block: &mut DoBlock<'a>, ex: &mut ErrCtx) {
        self.env.push();
        block
            .statements
            .iter_mut()
            .for_each(|stmt| self.resolve_stmt(stmt, ex));
        if let Some(ref mut value) = block.value {
            self.resolve_expr(value, ex);
        }
        self.env.pop();
    }

    fn resolve_expr(&mut self, expr: &mut Expr<'a>, ex: &mut ErrCtx) {
        match &mut expr.kind {
            ExprKind::Struct(_) => unimplemented!(),
            ExprKind::Fn(_) => unimplemented!(),
            ExprKind::If(r#if) => {
                self.env.push();

                self.resolve_condition(&mut r#if.condition, ex);
                self.resolve_do_block(&mut r#if.then, ex);
                if let Some(ref mut r#else) = r#if.otherwise {
                    self.resolve_do_block(r#else, ex)
                }

                self.env.pop();
            }
            ExprKind::DoBlock(block) => self.resolve_do_block(block, ex),
            ExprKind::Binary(_, ref mut left, ref mut right) => {
                self.resolve_expr(left, ex);
                self.resolve_expr(right, ex);
            }
            ExprKind::Unary(_, ref mut operand) => self.resolve_expr(operand, ex),
            ExprKind::Comma(exprs) => exprs
                .iter_mut()
                .for_each(|expr| self.resolve_expr(expr, ex)),
            ExprKind::Call(box Call {
                ref mut callee,
                ref mut args,
                ..
            }) => {
                self.resolve_expr(callee, ex);
                args.iter_mut().for_each(|a| self.resolve_expr(a, ex));
            }
            ExprKind::Spread(spread) => self.resolve_expr(spread, ex),
            ExprKind::GetProp(prop) => self.resolve_expr(&mut prop.node, ex),
            ExprKind::SetProp(prop) => {
                self.resolve_expr(&mut prop.value, ex);
                self.resolve_expr(&mut prop.node, ex);
            }
            ExprKind::GetItem(get) => {
                self.resolve_expr(&mut get.node, ex);
                self.resolve_expr(&mut get.key, ex);
            }
            ExprKind::SetItem(set) => {
                self.resolve_expr(&mut set.node, ex);
                self.resolve_expr(&mut set.key, ex);
                self.resolve_expr(&mut set.value, ex);
            }
            ExprKind::FString(s) => s.fragments.iter_mut().for_each(|f| match f {
                FStringFrag::Str(_) => (),
                FStringFrag::Expr(ref mut expr) => self.resolve_expr(expr, ex),
            }),
            ExprKind::Array(arr) => arr.iter_mut().for_each(|expr| self.resolve_expr(expr, ex)),
            ExprKind::Map(_) => unimplemented!(),
            ExprKind::Variable(v) => {
                if matches!(v.kind, TokenKind::Self_)
                    && !matches!(self.scope_kind, ScopeKind::Method | ScopeKind::Initializer)
                {
                    Self::error(
                        "Cannot use `self` outside of an instance method or `init` block",
                        v.span.clone(),
                        ex,
                    );
                }

                self.r#use(v, ex);
            }
            ExprKind::Range(box Range {
                ref mut start,
                ref mut end,
                ref mut step,
                ..
            }) => {
                self.resolve_expr(start, ex);
                self.resolve_expr(end, ex);
                self.resolve_expr(step, ex);
                // TODO: lint for invalid range bounds?
            }
            ExprKind::PrefixIncDec(inc) => self.resolve_expr(&mut inc.expr, ex),
            ExprKind::PostfixIncDec(inc) => self.resolve_expr(&mut inc.expr, ex),
            ExprKind::Assignment(ass) => {
                self.resolve_expr(&mut ass.value, ex);
                self.assign(&ass.name, ex);
            }
            ExprKind::Grouping(ref mut expr) => self.resolve_expr(expr, ex),
            ExprKind::AtIdent(ref name) => {
                if self.env.get(&name.lexeme).is_none() {
                    self.undefined_variable_error(name, ex);
                }
            }
            ExprKind::Lit(_) => {}
        }
    }

    fn resolve_condition(&mut self, condition: &mut Condition<'a>, ex: &mut ErrCtx) {
        self.resolve_expr(&mut condition.value, ex);
        match &condition.pattern {
            ConditionPattern::IsErr(v) | ConditionPattern::IsOk(v) => {
                self.declare(v, NameKind::Let, ex);
                self.assign(v, ex);
            }
            _ => (),
        }
    }

    fn declare_loop_label(&mut self, label: &Option<Token<'a>>, ex: &mut ErrCtx) {
        if let Some(ref lbl) = label {
            self.declare(lbl, NameKind::Let, ex);
            self.assign(lbl, ex);
        }
    }

    fn declare(&mut self, name: &Token<'a>, kind: NameKind, ex: &mut ErrCtx) {
        if let Some(vu) = self.env.in_current_scope(&name.lexeme) {
            if !vu.used {
                Self::error_of_kind(
                    VesErrorKind::AttemptedToShadowUnusedLocal(vu.span.clone()),
                    format!("Attempted to shadow an unused variable `{}`", name.lexeme),
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

    /// Marks the given variable as used.
    #[inline]
    fn r#use(&mut self, name: &Token<'a>, ex: &mut ErrCtx) {
        match self.env.get_mut(&name.lexeme) {
            Some(v) => v.used = true,
            None => self.undefined_variable_error(name, ex),
        }
    }

    fn undefined_variable_error(&self, token: &Token<'a>, ex: &mut ErrCtx) {
        if !is_reserved_identifier(&token) {
            Self::error(
                match token.kind {
                    TokenKind::AtIdentifier => format!("Undefined loop label `{}`", token.lexeme),
                    _ => format!("Undefined variable `{}`", token.lexeme),
                },
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
        let _source = r#"
        let x = 5
        x = 3
    "#;
    }

    #[ignore]
    #[test]
    fn test_let_requires_an_initializer() {
        let _source = r#"
        mut x; // ok
        let y; // error
        let z = true; // ok
    "#;
    }

    #[ignore]
    #[test]
    fn test_undefined_variables_are_rejected() {
        let _source = r#"
        let global = 7
        
        {
            mut local = 5
            local = 3
            
            print global, local
        }
        
        print global
        print local
        print undefined
"#;
    }

    #[ignore]
    #[test]
    fn test_shadowing_unused_variable_warning() {
        let _source = r#"
        let unused = 42
        let unused = "new value";
    "#;
    }

    #[ignore]
    #[test]
    fn test_undefined_loop_labels_are_detected() {
        let _source = r#"
            loop { 
                break @label;
            }
            @label: loop { 
                break @label;
            }
        "#;
    }

    #[ignore]
    #[test]
    fn test_return_is_allowed_only_in_functions() {
        let _source = r#"
        struct S(x) { 
            init { 
                if (false) { return 5; } // error
                return; // ek
            }

            method1(self) { loop { return;  } } // ok
            method2(self) => none;  // ok
            method3() { return; } // ok
            method4() => none;  // ok
        }

        fn func1() { return; }
        fn func2() => none;

        print fn() { return }; // ok
        print fn() => none; // ok


        return; // error

        do {
            return; // error
        }

        loop { return; } // error
        "#;
    }
}
