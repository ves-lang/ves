use std::{borrow::Cow, cell::Cell, rc::Rc};

use crate::env::Env;
use ves_parser::ast::*;

/// A (possibly) propagated variable with a use counter.
/// If the use counter reaches 0 after the variable is propagated, its declaration is safe to remove.
#[derive(Debug, Clone)]
struct PropVar<'a> {
    /// The const value of the variable.
    value: Lit<'a>,
    /// The number of uses this variable still has.
    uses: Rc<Cell<usize>>,
}

/// A simple constant folder that computes constant expressions such as arithmetics and string addition
/// and propagates the result if they're stored in `let` variables to all uses.
/// Optionally removes the `let` stores that have been completely propagated.
#[derive(Debug)]
pub struct ConstantFolder<'a> {
    /// The environment with both normal and const variables. However, only immutable const variables have values.
    propagated_variables: Env<Cow<'a, str>, Option<PropVar<'a>>>,
    /// The interning threshold used to determine whether it's ok to propagate a string or not.
    interning_threshold: usize,
    /// Whether to eliminate dead stores after the const prop / fold pass.
    eliminate_dead_stores: bool,
    /// Whether the DSE pass has been started.
    second_pass: bool,
}

impl<'a> ConstantFolder<'a> {
    /// Creates a new constant folder with the given interning threshold and DSE toggle.
    pub fn new(interning_threshold: usize, eliminate_dead_stores: bool) -> Self {
        Self {
            interning_threshold,
            eliminate_dead_stores,
            second_pass: false,
            propagated_variables: Env::new(),
        }
    }

    /// Folds the given AST, consuming the struct.
    pub fn fold(mut self, ast: &mut AST<'a>) {
        for stmt in ast.body.iter_mut() {
            self.fold_stmt(stmt);
        }
        if self.eliminate_dead_stores && !self.second_pass {
            self.second_pass = true;
            self.fold(ast);
        }
    }

    fn fold_stmt(&mut self, stmt: &mut Stmt<'a>) {
        if self.second_pass {
            if let StmtKind::Var(vars) = &mut stmt.kind {
                // TODO: rewrite the AST to support declarations with multiple variables
                if vars.len() == 1 && vars[0].n_uses.get() == 0 {
                    // The initializer must always have a value if we get here
                    match vars[0].initializer.as_ref() {
                        // The binding stores a variable or a constant and isn't used,
                        // so we can safely remove it
                        Some(Expr {
                            kind: ExprKind::Lit(_),
                            ..
                        })
                        | Some(Expr {
                            kind: ExprKind::Variable(_),
                            ..
                        }) => stmt.kind = StmtKind::_Empty,
                        // The initializer is either missing or a runtime expression
                        _ => (),
                    }
                }
            }
        }
        match &mut stmt.kind {
            StmtKind::Var(vars) => vars.iter_mut().for_each(|v| {
                let kind = v.kind;
                let uses = v.n_uses.clone();
                let value = v.initializer.as_mut().and_then(|init| {
                    self.fold_expr(init);
                    if let ExprKind::Lit(lit @ box Lit { value, .. }) = &init.kind {
                        match (kind, value) {
                            (VarKind::Let, LitValue::Str(s))
                                if s.len() > self.interning_threshold =>
                            {
                                None
                            }
                            (VarKind::Let, _) => Some(PropVar {
                                value: (**lit).clone(),
                                uses,
                            }),
                            _ => None,
                        }
                    } else {
                        None
                    }
                });
                self.propagated_variables.add(v.name.lexeme.clone(), value);
            }),
            StmtKind::Loop(box Loop { ref mut body, .. }) => self.fold_stmt(body),
            StmtKind::For(box For {
                initializers,
                condition,
                increment,
                body,
                ..
            }) => {
                self.push();
                initializers.iter_mut().for_each(|init| {
                    self.fold_expr(&mut init.value);
                    self.propagated_variables
                        .add(init.name.lexeme.clone(), None);
                });

                if let Some(ref mut cond) = condition {
                    self.fold_expr(cond);
                }

                if let Some(ref mut inc) = increment {
                    self.fold_expr(inc);
                }

                self.fold_stmt(body);
                self.pop();
            }
            StmtKind::ForEach(box ForEach {
                iterator,
                body,
                variable,
                ..
            }) => {
                match iterator {
                    IteratorKind::Range(Range {
                        start, end, step, ..
                    }) => {
                        self.fold_expr(start);
                        self.fold_expr(end);
                        self.fold_expr(step);
                    }
                    IteratorKind::Expr(expr) => {
                        self.fold_expr(expr);
                    }
                }
                self.push();
                self.propagated_variables.add(variable.lexeme.clone(), None);
                self.fold_stmt(body);
                self.pop();
            }
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

    fn fold_function(&mut self, info: &mut FnInfo<'a>) {
        self.push();
        info.params.positional.iter_mut().for_each(|p| {
            self.propagated_variables.add(p.0.lexeme.clone(), None);
        });
        info.params.default.iter_mut().for_each(|(name, v, _)| {
            self.propagated_variables.add(name.lexeme.clone(), None);
            self.fold_expr(v)
        });
        if let Some(p) = info.params.rest.as_ref() {
            self.propagated_variables.add(p.lexeme.clone(), None);
        }
        info.body.iter_mut().for_each(|stmt| self.fold_stmt(stmt));
        self.pop();
    }

    fn fold_do_block(&mut self, b: &mut DoBlock<'a>) {
        self.push();
        b.statements
            .iter_mut()
            .for_each(|stmt| self.fold_stmt(stmt));
        if let Some(ref mut value) = b.value {
            self.fold_expr(value)
        }
        self.pop();
    }

    fn fold_expr(&mut self, expr: &mut Expr<'a>) {
        match &mut expr.kind {
            ExprKind::Binary(op, box left, box right) => {
                self.fold_expr(left);
                self.fold_expr(right);
                if let (ExprKind::Lit(box left), ExprKind::Lit(box right)) =
                    (&mut left.kind, &mut right.kind)
                {
                    match op {
                        BinOpKind::Is => { /* TODO */ }
                        BinOpKind::In => { /* TODO */ }
                        BinOpKind::Add => crate::fold_binary_op!(expr, left, right, +),
                        BinOpKind::Subtract => crate::fold_binary_op!(expr, left, right, -),
                        BinOpKind::Multiply => crate::fold_binary_op!(expr, left, right, *),
                        BinOpKind::Divide => {
                            if !right.value.is_zero() {
                                crate::fold_binary_op!(expr, left, right, /)
                            }
                        }
                        BinOpKind::Remainder => {
                            if !right.value.is_zero() {
                                crate::fold_binary_op!(expr, left, right, %)
                            }
                        }
                        BinOpKind::Power => crate::fold_binary_op!(expr, left, right, **),
                        BinOpKind::And => crate::assign_lit_node_if_some!(
                            expr,
                            left,
                            right,
                            Some(LitValue::from(
                                left.value.is_truthy() && right.value.is_truthy(),
                            ))
                        ),
                        BinOpKind::Or => crate::assign_lit_node_if_some!(
                            expr,
                            left,
                            right,
                            Some(LitValue::from(
                                left.value.is_truthy() && right.value.is_truthy(),
                            ))
                        ),
                        BinOpKind::Equal => crate::fold_binary_op!(ord => expr, left, right, ==),
                        BinOpKind::NotEqual => crate::fold_binary_op!(ord => expr, left, right, !=),
                        BinOpKind::LessThan => crate::fold_binary_op!(ord => expr, left, right,< ),
                        BinOpKind::LessEqual => crate::fold_binary_op!(ord => expr, left, right,<=),
                        BinOpKind::GreaterEqual => {
                            crate::fold_binary_op!(ord => expr, left, right,>=)
                        }
                        BinOpKind::GreaterThan => {
                            crate::fold_binary_op!(ord => expr, left, right,>)
                        }
                    }
                }
            }
            ExprKind::Unary(op, box operand) => {
                self.fold_expr(operand);
                if let ExprKind::Lit(box lit) = &mut operand.kind {
                    match op {
                        UnOpKind::Negate => {
                            let mut new = LitValue::None;
                            std::mem::swap(&mut lit.value, &mut new);
                            crate::assign_lit_node_if_some!(
                                expr,
                                lit,
                                Some(crate::unary_num_map!(new, -))
                            );
                        }
                        UnOpKind::Not => {
                            crate::assign_lit_node_if_some!(
                                expr,
                                lit,
                                Some(LitValue::from(!lit.value.is_truthy()))
                            );
                        }
                        UnOpKind::Try | UnOpKind::WrapOk | UnOpKind::WrapErr => (),
                    }
                }
            }
            ExprKind::Struct(box StructInfo {
                ref name,
                ref mut methods,
                ref mut fields,
                ref mut r#static,
                ref mut initializer,
            }) => {
                self.propagated_variables.add(name.lexeme.clone(), None);
                if let Some(fields) = fields {
                    fields
                        .default
                        .iter_mut()
                        .for_each(|(_, v, _)| self.fold_expr(v))
                }
                if let Some(init) = initializer {
                    self.fold_function(&mut init.body);
                }
                methods.iter_mut().for_each(|m| self.fold_function(m));
                r#static
                    .fields
                    .iter_mut()
                    .flat_map(|(_, v)| v.as_mut())
                    .for_each(|v| self.fold_expr(v));
                r#static
                    .methods
                    .iter_mut()
                    .for_each(|f| self.fold_function(f));
            }
            ExprKind::Fn(box r#fn) => self.fold_function(r#fn),
            ExprKind::If(box r#if) => self.fold_if_expr(r#if),
            ExprKind::DoBlock(box b) => self.fold_do_block(b),
            ExprKind::Comma(list) => list.iter_mut().for_each(|e| self.fold_expr(e)),
            ExprKind::Call(box Call { callee, args, .. }) => {
                self.fold_expr(callee);
                args.iter_mut().for_each(|e| self.fold_expr(e));
            }
            ExprKind::Spread(s) => self.fold_expr(s),
            ExprKind::GetProp(box GetProp { node, .. }) => self.fold_expr(node),
            ExprKind::SetProp(box SetProp { node, value, .. }) => {
                self.fold_expr(node);
                self.fold_expr(value);
            }
            ExprKind::GetItem(box GetItem { key, node }) => {
                self.fold_expr(key);
                self.fold_expr(node);
            }
            ExprKind::SetItem(box SetItem { key, node, value }) => {
                self.fold_expr(key);
                self.fold_expr(node);
                self.fold_expr(value);
            }
            ExprKind::FString(f) => f.fragments.iter_mut().for_each(|f| match f {
                FStringFrag::Expr(expr) => self.fold_expr(expr),
                FStringFrag::Str(_) => {}
            }),
            ExprKind::Array(a) => a.iter_mut().for_each(|e| self.fold_expr(e)),
            ExprKind::Map(map) => map.iter_mut().for_each(|entry| match entry {
                MapEntry::Pair(key, value) => {
                    self.fold_expr(key);
                    self.fold_expr(value);
                }
                MapEntry::Spread(spread) => self.fold_expr(spread),
            }),
            ExprKind::Variable(v) => {
                if let Some(const_expr) = self
                    .propagated_variables
                    .get(&v.lexeme)
                    .and_then(|v| v.as_ref())
                {
                    const_expr
                        .uses
                        .set(const_expr.uses.get().checked_sub(1).expect(
                            "Attempted to propagate a variable more times that it has been used; 
                        the resolver must have missed a use",
                        ));
                    *expr = Expr {
                        kind: ExprKind::Lit(box const_expr.value.clone()),
                        span: expr.span.clone(),
                    };
                }
            }
            ExprKind::PrefixIncDec(box inc) | ExprKind::PostfixIncDec(box inc) => {
                self.fold_expr(&mut inc.expr)
            }
            ExprKind::Assignment(asn) => self.fold_expr(&mut asn.value),
            ExprKind::Grouping(box data) => {
                self.fold_expr(data);
                // The kind doesn't matter. `Comma` is just easier to construct.
                let new = Expr {
                    kind: ExprKind::Comma(vec![]),
                    span: expr.span.clone(),
                };
                *expr = std::mem::replace(data, new);
            }
            ExprKind::Lit(_) => {}
        }
    }

    // FIXME(moscow): I changed AST for if expressions and I'm not sure how to fix this (look below)
    fn fold_if_expr(&mut self, _if: &If<'a>) {
        /* // TODO: propagate the value into the pattern binding
        self.fold_expr(&mut condition.value);
        self.fold_do_block(then);

        if let Some(r#else) = otherwise.as_mut() {
            self.fold_do_block(r#else);
        }

        match self.is_truthy_condition(condition) {
            // Condition is truthy, we can replace the node with the value of `then`
            Some(true) => {
                let then = std::mem::replace(
                    then,
                    DoBlock {
                        statements: vec![],
                        value: None,
                    },
                );
                expr.kind = ExprKind::DoBlock(box then);
            }
            Some(false) => {
                // Condition is false, we can replace the node with the value of `else`
                if let Some(r#else) = otherwise.take() {
                    // FIXME: i'm not sure how this interacts with the new AST for if expressions
                    expr.kind = ExprKind::DoBlock(box r#else);
                } else {
                    // There's no else, so we can replace the node with `none`.
                    expr.kind = ExprKind::Lit(box Lit {
                        value: LitValue::None,
                        token: ves_parser::lexer::Token::new(
                            "none",
                            expr.span.clone(),
                            ves_parser::lexer::TokenKind::None,
                        ),
                    });
                }
            }
            None => (),
        } */
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

#[cfg(test)]
mod tests {
    use crate::resolver::Resolver;

    use super::*;
    use ves_error::{ErrCtx, FileId, VesFileDatabase};
    use ves_parser::{AstToStr, Lexer, Parser};
    use ves_testing::make_test_macros;

    static CRATE_ROOT: &str = env!("CARGO_MANIFEST_DIR");
    static TESTS_DIR: &str = "tests";

    fn parse_and_fold<'a>(
        src: Cow<'a, str>,
        fid: FileId,
        db: &mut VesFileDatabase<String, Cow<'a, str>>,
    ) -> Result<String, ErrCtx> {
        let mut ast = Parser::new(Lexer::new(&src), fid, &db).parse().unwrap();
        Resolver::new().resolve(&mut ast).unwrap();
        ConstantFolder::new(20, true).fold(&mut ast);
        Ok(ast
            .body
            .into_iter()
            .map(|stmt| stmt.ast_to_str())
            .collect::<Vec<_>>()
            .join("\n"))
    }

    make_test_macros!(CRATE_ROOT, TESTS_DIR, parse_and_fold, parse_and_fold);

    test_ok!(fold1_test_constant_folding);
    test_ok!(fold2_test_let_variable_propagation);
    // TODO: re-enable this once if expression folding is fixed
    /* test_ok!(fold3_test_control_flow_is_folded); */
}
