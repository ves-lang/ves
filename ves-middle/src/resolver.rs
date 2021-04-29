use std::{borrow::Cow, cell::Cell, rc::Rc};

use ves_error::{ErrCtx, FileId, Files, VesError, VesErrorKind, VesFileDatabase};
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
    pub fn resolve(
        mut self,
        ast: &mut AST<'a>,
        db: &VesFileDatabase<'a>,
    ) -> Result<ErrCtx, ErrCtx> {
        self.file_id = ast.file_id;
        let mut ex = ErrCtx {
            local_file_id: self.file_id,
            ..Default::default()
        };

        self.resolve_imports(&ast.imports, db, &mut ex);

        let mut sorted_globals = ast.globals.clone().into_iter().collect::<Vec<_>>();
        sorted_globals.sort_by_key(|e| e.name.span.start);
        for global in &sorted_globals {
            self.declare_global(&global.name, NameKind::from(global.kind));
        }

        for stmt in &mut ast.body {
            self.resolve_stmt(stmt, &mut ex);
        }

        self.resolve_exports(&ast.exports, &mut ex);

        self.check_variable_usage(&mut ex);

        if ex.had_error() {
            Err(ex)
        } else {
            Ok(ex)
        }
    }

    fn resolve_imports(
        &mut self,
        imports: &[Import<'a>],
        db: &VesFileDatabase<'a>,
        ex: &mut ErrCtx,
    ) {
        // The path to the current file, all imports are resolved relatively to it
        let base_path = db
            .name(self.file_id)
            .expect("Attempted to resolve an anonymous file.");

        for i in imports {
            match i {
                Import::Direct(path) => match path {
                    ImportPath::Simple(symbol) => {}
                    ImportPath::Full(symbol) => {}
                },
                Import::Destructured(path, symbols) => {}
            }
        }
    }

    fn resolve_exports(&mut self, exports: &[Symbol<'a>], ex: &mut ErrCtx) {
        // unimplemented!()
    }

    fn resolve_stmt(&mut self, stmt: &mut Stmt<'a>, ex: &mut ErrCtx) {
        match &mut stmt.kind {
            StmtKind::Var(vars) => {
                for var in vars {
                    // We have to resolve the variable first to allow shadowing.
                    if let Some(ref mut init) = var.initializer {
                        self.resolve_expr(init, ex);
                    } else if var.kind == VarKind::Let {
                        debug_assert!(false, "This should never happen as assignment checks are performed in the parser");
                        Self::error(
                            format!(
                                "Immutable variable `{}` must be explicitly initialized",
                                var.name.lexeme
                            ),
                            var.name.span.clone(),
                            ex,
                        );
                    }

                    self.declare(&var.name, var.n_uses.clone(), NameKind::from(var.kind), ex);

                    // Only `let` variables are marked as assigned at this point.
                    if var.initializer.is_some() && var.kind == VarKind::Let {
                        self.assign(&var.name, ex);
                    }
                }
            }
            StmtKind::Loop(r#loop) => {
                self.push();

                self.declare_loop_label(&r#loop.label, ex);

                let prev_loop = self.loop_kind;
                self.loop_kind = LoopKind::Loop;
                self.resolve_stmt(&mut r#loop.body, ex);
                self.loop_kind = prev_loop;

                self.pop(ex);
            }
            StmtKind::For(r#for) => {
                self.push();

                r#for.initializers.iter_mut().for_each(|init| {
                    self.resolve_expr(&mut init.value, ex);
                    self.declare(&init.name, Rc::new(Cell::new(0)), NameKind::Mut, ex);
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

                self.pop(ex);
            }
            StmtKind::ForEach(r#for) => {
                self.push();

                self.resolve_expr(&mut r#for.iterator, ex);

                self.declare(
                    &r#for.variable,
                    Rc::new(Cell::new(0)),
                    NameKind::ForEachVar,
                    ex,
                );
                self.assign(&r#for.variable, ex);

                self.declare_loop_label(&r#for.label, ex);

                let prev_loop = self.loop_kind;
                self.loop_kind = LoopKind::ForEach;
                self.resolve_stmt(&mut r#for.body, ex);
                self.loop_kind = prev_loop;

                self.pop(ex);
            }
            StmtKind::While(box While {
                ref mut condition,
                ref mut body,
                ref label,
            }) => {
                self.push();

                self.resolve_condition(condition, ex);

                self.declare_loop_label(label, ex);

                let prev_loop = self.loop_kind;
                self.loop_kind = LoopKind::While;
                self.resolve_stmt(body, ex);
                self.loop_kind = prev_loop;

                self.pop(ex);
            }
            StmtKind::Block(statements) => {
                let prev_kind = self.scope_kind;
                if self.scope_kind == ScopeKind::Global {
                    self.scope_kind = ScopeKind::Local;
                }
                self.push();
                self.resolve_block(statements, ex);
                self.pop(ex);
                self.scope_kind = prev_kind;
            }
            StmtKind::ExprStmt(expr) => self.resolve_expr(expr, ex),
            StmtKind::Print(expr) => self.resolve_expr(expr, ex),
            StmtKind::Return(value) => {
                if let Some(ref mut expr) = value {
                    self.resolve_expr(expr, ex);
                }

                match self.scope_kind {
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
                    ScopeKind::Global
                    | ScopeKind::Local
                    | ScopeKind::Function
                    | ScopeKind::AssocMethod
                    | ScopeKind::Method => {}
                }
            }
            StmtKind::Break(label) => {
                if let LoopKind::None = self.loop_kind {
                    Self::error("Cannot break outside of a loop", stmt.span.clone(), ex);
                }
                if let Some(name) = label.as_ref() {
                    if self.env.get(&name.lexeme).is_none() {
                        self.undefined_variable_error(name, ex);
                    } else {
                        self.r#use(name, ex);
                    }
                }
            }
            StmtKind::Continue(label) => {
                if let LoopKind::None = self.loop_kind {
                    Self::error("Cannot continue outside of a loop", stmt.span.clone(), ex);
                }
                if let Some(name) = label.as_ref() {
                    if self.env.get(&name.lexeme).is_none() {
                        self.undefined_variable_error(name, ex);
                    } else {
                        self.r#use(name, ex);
                    }
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
        self.push();
        block
            .statements
            .iter_mut()
            .for_each(|stmt| self.resolve_stmt(stmt, ex));
        if let Some(ref mut value) = block.value {
            self.resolve_expr(value, ex);
        }
        self.pop(ex);
    }

    fn resolve_function(&mut self, f: &mut FnInfo<'a>, ex: &mut ErrCtx) {
        if f.kind != FnKind::Initializer {
            self.declare(&f.name, Rc::new(Cell::new(0)), NameKind::Fn, ex);
            self.assign(&f.name, ex);
        }

        let prev_kind = self.scope_kind;
        self.scope_kind = match f.kind {
            FnKind::Method => ScopeKind::Method,
            FnKind::Static => ScopeKind::AssocMethod,
            FnKind::Function => ScopeKind::Function,
            FnKind::Initializer => ScopeKind::Initializer,
        };
        self.push();

        for (_, p) in &mut f.params.default {
            self.resolve_expr(p, ex);
        }

        for param in f
            .params
            .positional
            .iter()
            .chain(f.params.default.iter().map(|p| &p.0))
            .chain(f.params.rest.iter())
        {
            self.declare(&param, Rc::new(Cell::new(0)), NameKind::Param, ex);
            self.assign(&param, ex);
        }

        self.resolve_block(&mut f.body, ex);

        self.pop(ex);
        self.scope_kind = prev_kind;
    }

    fn resolve_expr(&mut self, expr: &mut Expr<'a>, ex: &mut ErrCtx) {
        match &mut expr.kind {
            ExprKind::Struct(box StructInfo {
                ref name,
                ref mut fields,
                ref mut methods,
                ref mut initializer,
                ref mut r#static,
            }) => {
                self.declare(name, Rc::new(Cell::new(0)), NameKind::Let, ex);
                self.assign(name, ex);

                if let Some(init) = initializer {
                    self.push();
                    let this = Token::new("self", name.span.clone(), TokenKind::Self_);
                    self.declare(&this, Rc::new(Cell::new(0)), NameKind::Let, ex);
                    self.assign(&this, ex);
                    self.r#use(&this, ex);
                    self.resolve_function(&mut init.body, ex);
                    self.pop(ex);
                }

                for (_, field) in fields.iter_mut().flat_map(|f| &mut f.default) {
                    self.resolve_expr(field, ex);
                }

                for field in r#static.fields.iter_mut().filter_map(|(_, f)| f.as_mut()) {
                    self.resolve_expr(field, ex);
                }

                for method in methods.iter_mut().chain(r#static.methods.iter_mut()) {
                    self.resolve_function(method, ex);
                }
            }
            ExprKind::Fn(box ref mut r#fn) => {
                self.resolve_function(r#fn, ex);
            }
            ExprKind::If(r#if) => {
                self.push();

                self.resolve_condition(&mut r#if.condition, ex);
                self.resolve_do_block(&mut r#if.then, ex);
                if let Some(ref mut r#else) = r#if.otherwise {
                    self.resolve_do_block(r#else, ex)
                }

                self.pop(ex);
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
            ExprKind::Map(entries) => entries.iter_mut().for_each(|entry| match entry {
                MapEntry::Pair(key, value) => {
                    self.resolve_expr(key, ex);
                    self.resolve_expr(value, ex);
                }
                MapEntry::Spread(expr) => self.resolve_expr(expr, ex),
            }),
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
                self.declare(v, Rc::new(Cell::new(0)), NameKind::Let, ex);
                self.assign(v, ex);
            }
            _ => (),
        }
    }

    fn declare_loop_label(&mut self, label: &Option<Token<'a>>, ex: &mut ErrCtx) {
        if let Some(ref lbl) = label {
            self.declare(lbl, Rc::new(Cell::new(0)), NameKind::Let, ex);
            self.assign(lbl, ex);
        }
    }

    fn declare(
        &mut self,
        name: &Token<'a>,
        uses: Rc<Cell<usize>>,
        kind: NameKind,
        ex: &mut ErrCtx,
    ) {
        if let Some(vu) = self.env.in_current_scope(&name.lexeme) {
            if vu.declared {
                Self::error_of_kind(
                    VesErrorKind::AttemptedToShadowLocalVariable(vu.span.clone()),
                    format!("Attempted to shadow a local variable `{}`", name.lexeme),
                    name.span.clone(),
                    ex,
                );
                return;
            }
        }

        // NOTE: this code used to allow shadowing. Review #7bb446467b if needed.
        self.env.add(
            name.lexeme.clone(),
            VarUsage {
                kind,
                declared: true,
                assigned: false,
                uses,
                span: name.span.clone(),
            },
        );
    }

    fn declare_global(&mut self, name: &Token<'a>, kind: NameKind) {
        debug_assert!(self.scope_kind == ScopeKind::Global);

        // Avoid re-declaring forward-declared globals
        if self.env.get(&name.lexeme).is_some() {
            return;
        }

        self.env.add(
            name.lexeme.clone(),
            VarUsage {
                kind,
                declared: false,
                assigned: false,
                uses: Rc::new(Cell::new(0)),
                span: name.span.clone(),
            },
        );
    }

    fn assign<'b>(&mut self, name: &'b Token<'a>, ex: &mut ErrCtx) {
        match self.env.get_mut(&name.lexeme) {
            Some(v) => {
                if v.is_let() && v.assigned {
                    if v.kind == NameKind::ForEachVar {
                        Self::error(
                            "For-each loop variables may not be reassigned",
                            name.span.clone(),
                            ex,
                        );
                    } else if v.kind == NameKind::Param {
                        Self::error(
                            "Function parameters may not be reassigned",
                            name.span.clone(),
                            ex,
                        );
                    } else if v.kind == NameKind::Let {
                        Self::error_of_kind(
                            VesErrorKind::LetReassignment,
                            format!(
                                "Cannot assign twice to the immutable variable `{}`",
                                name.lexeme
                            ),
                            name.span.clone(),
                            ex,
                        );
                    } else if matches!(v.kind, NameKind::Fn | NameKind::Struct) {
                        Self::error(
                            format!(
                                "Cannot assign to the {} `{}`",
                                if v.kind == NameKind::Fn {
                                    "function"
                                } else {
                                    "struct"
                                },
                                name.lexeme
                            ),
                            name.span.clone(),
                            ex,
                        );
                    }
                }
                // Avoid assigning undeclared variables
                if v.declared {
                    v.assigned = true;
                }
            }
            None => self.undefined_variable_error(name, ex),
        }
    }

    /// Marks the given variable as used.
    #[inline]
    fn r#use(&mut self, name: &Token<'a>, ex: &mut ErrCtx) {
        match self.env.get_mut(&name.lexeme) {
            Some(v) => {
                if !v.declared && self.scope_kind == ScopeKind::Global {
                    Self::error_of_kind(
                        VesErrorKind::UsedGlobalBeforeDeclaration(v.span.clone()),
                        format!(
                            "Attempted to use the {} `{}` before its declaration",
                            match v.kind {
                                NameKind::Fn => "function",
                                NameKind::Struct => "struct",
                                _ => "variable",
                            },
                            name.lexeme
                        ),
                        name.span.clone(),
                        ex,
                    );
                }
                v.uses.set(v.uses.get() + 1);
            }
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

    fn push(&mut self) {
        self.env.push();
    }

    fn pop(&mut self, ex: &mut ErrCtx) {
        self.check_variable_usage(ex);
        self.env.pop();
    }

    /// Checks the variable usage in the current scope.
    #[allow(clippy::match_bool)]
    fn check_variable_usage(&self, ex: &mut ErrCtx) {
        let is_global = self.env.is_global();
        for (name, vu) in self.env.get_scope().unwrap() {
            // Do not apply any lints to `self`.
            if name == "self" {
                continue;
            }

            let noun = match vu.kind {
                NameKind::Fn => "Function",
                NameKind::Struct => "Struct",
                NameKind::Let if name.starts_with('@') => "Label",
                _ => "Variable",
            };

            let is_prefixed = name.starts_with('_');
            // Issue an error for unused local variables, functions and structs.
            if !vu.used() && !is_global && !is_prefixed && vu.is_var() {
                let msg = format!("{} `{}` is never used", noun, name);
                Self::error_of_kind(VesErrorKind::UnusedLocal, msg, vu.span.clone(), ex)
                    .mark_last_error_as_warning();
            }
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
    use super::*;
    use ves_error::VesFileDatabase;
    use ves_parser::{AstToStr, Lexer, Parser};
    use ves_testing::make_test_macros;

    static CRATE_ROOT: &str = env!("CARGO_MANIFEST_DIR");
    static TESTS_DIR: &str = "tests";

    fn parse_and_resolve<'a>(
        src: Cow<'a, str>,
        fid: FileId,
        db: &mut VesFileDatabase<'a>,
    ) -> Result<String, ErrCtx> {
        let mut ast = Parser::new(Lexer::new(&src), fid, &db).parse().unwrap();
        match Resolver::new().resolve(&mut ast, db) {
            Ok(warnings) => {
                let diagnostics = db.report_to_string(&warnings).unwrap();
                Ok(format!(
                    "{}{}",
                    diagnostics,
                    ast.body
                        .into_iter()
                        .map(|stmt| stmt.ast_to_str())
                        .collect::<Vec<_>>()
                        .join("\n")
                ))
            }
            Err(errors) => Err(errors),
        }
    }

    make_test_macros!(CRATE_ROOT, TESTS_DIR, parse_and_resolve, parse_and_resolve);

    test_err!(t1_test_cannot_assign_to_let);
    test_err!(t2_test_variables_must_be_defined);
    test_err!(t3_test_globals_are_forward_declared);
    test_err!(t4_cannot_break_outside_of_a_loop);
    test_err!(t5_test_undefined_loop_labels_are_detected);
    test_err!(t6_test_return_usage);
    test_err!(t7_self_may_be_used_only_inside_methods);
    test_err!(t8_test_for_loops);
    test_ok!(t9_unused_locals);
    test_err!(t10_shadowing);
}
