#[macro_export]
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

#[macro_export]
/// Creates an AST binary expression
macro_rules! binary {
    ($left:ident, $op:ident, $right:expr) => {{
        let l = $left;
        let r = $right;
        ast::Expr {
            span: l.span.start..r.span.end,
            kind: ast::ExprKind::Binary(ast::BinOpKind::$op, box l, box r),
        }
    }};
}

#[macro_export]
macro_rules! unary {
    ($op:ident, $operand:expr, $t:ident) => {{
        let operand = $operand;
        ast::Expr {
            span: $t.span.start..operand.span.end,
            kind: ast::ExprKind::Unary(ast::UnOpKind::$op, box operand),
        }
    }};
}

#[macro_export]
macro_rules! stmt {
    ($stmt:expr, $span:expr) => {
        Stmt {
            kind: $stmt,
            span: $span,
        }
    };
}

#[macro_export]
macro_rules! stmt_ok {
    ($stmt:expr, $span:expr) => {
        Ok(stmt!($stmt, $span))
    };
}

#[macro_export]
macro_rules! expr {
    ($expr:expr, $span:expr) => {
        Expr {
            kind: $expr,
            span: $span,
        }
    };
}

#[macro_export]
macro_rules! expr_ok {
    ($expr:expr, $span:expr) => {
        Ok(expr!($expr, $span))
    };
}
