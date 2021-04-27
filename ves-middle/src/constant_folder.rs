use std::borrow::Cow;

use crate::env::Env;
use ves_parser::ast::*;

#[derive(Debug)]
pub struct ConstantFolder<'a> {
    propagated_variables: Env<Cow<'a, str>, Option<Lit<'a>>>,
    interning_threshold: usize,
}

impl<'a> ConstantFolder<'a> {
    pub fn new(interning_threshold: usize) -> Self {
        Self {
            interning_threshold,
            propagated_variables: Env::new(),
        }
    }

    pub fn fold(&mut self, ast: &mut AST<'a>) {
        for stmt in ast.body.iter_mut() {
            self.fold_stmt(stmt);
        }
    }

    fn fold_stmt(&mut self, stmt: &mut Stmt<'a>) {
        match &mut stmt.kind {
            StmtKind::Var(vars) => vars.iter_mut().for_each(|v| {
                let kind = v.kind;
                let value = v.initializer.as_mut().and_then(|init| {
                    self.fold_expr(init);
                    if let ExprKind::Lit(lit @ box Lit { value, .. }) = &init.kind {
                        match (kind, value) {
                            (VarKind::Let, LitValue::Str(s))
                                if s.len() > self.interning_threshold =>
                            {
                                None
                            }
                            (VarKind::Let, _) => Some((**lit).clone()),
                            _ => None,
                        }
                    } else {
                        None
                    }
                });
                self.propagated_variables.add(v.name.lexeme.clone(), value);
            }),
            StmtKind::Loop(box Loop { ref mut body, .. }) => self.fold_stmt(body),
            StmtKind::For(box For { .. }) => {
                unimplemented!()
            }
            StmtKind::ForEach(_) => {}
            StmtKind::While(box While {
                ref mut condition,
                ref mut body,
                ..
            }) => {
                self.fold_expr(&mut condition.value);
                self.fold_stmt(body);
                if let Some(false) = self.is_truthy_condition(condition) {
                    stmt.kind = StmtKind::_Empty;
                }
            }
            StmtKind::Block(block) => {
                self.push();
                block.iter_mut().for_each(|stmt| self.fold_stmt(stmt));
                self.pop();
            }
            StmtKind::ExprStmt(expr) => self.fold_expr(expr),
            StmtKind::Print(expr) => self.fold_expr(expr),
            StmtKind::Return(value) => {
                if let Some(expr) = value.as_mut() {
                    self.fold_expr(expr)
                }
            }
            StmtKind::Defer(box ref mut call) => self.fold_expr(call),
            StmtKind::Break(_) => {}
            StmtKind::Continue(_) => {}
            StmtKind::_Empty => {}
        }
    }

    fn fold_expr(&mut self, expr: &mut Expr<'a>) {
        match &mut expr.kind {
            ExprKind::Struct(_) => {}
            ExprKind::Fn(_) => {}
            ExprKind::If(_) => {}
            ExprKind::DoBlock(_) => {}
            ExprKind::Binary(_, _, _) => {}
            ExprKind::Unary(_, _) => {}
            ExprKind::Lit(_) => {}
            ExprKind::Comma(_) => {}
            ExprKind::Call(_) => {}
            ExprKind::Spread(_) => {}
            ExprKind::GetProp(_) => {}
            ExprKind::SetProp(_) => {}
            ExprKind::GetItem(_) => {}
            ExprKind::SetItem(_) => {}
            ExprKind::FString(_) => {}
            ExprKind::Array(_) => {}
            ExprKind::Map(_) => {}
            ExprKind::Variable(_) => {}
            ExprKind::Range(_) => {}
            ExprKind::PrefixIncDec(_) => {}
            ExprKind::PostfixIncDec(_) => {}
            ExprKind::Assignment(_) => {}
            ExprKind::Grouping(_) => {}
            ExprKind::AtIdent(_) => {}
        }
    }

    fn is_truthy_condition(&mut self, cond: &Condition<'a>) -> Option<bool> {
        match &cond.value.kind {
            ExprKind::Lit(lit) => Some(match lit.value {
                LitValue::Number(f) => f != 0.0,
                LitValue::Bool(b) => b,
                LitValue::None => false,
                LitValue::Str(_) => true,
            }),
            _ => None,
        }
    }

    #[inline]
    fn push(&mut self) {
        self.propagated_variables.push();
    }

    #[inline]
    fn pop(&mut self) {
        self.propagated_variables.pop();
    }
}
