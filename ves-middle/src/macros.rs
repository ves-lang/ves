#[macro_export]
macro_rules! unary_num_map {
    ($lit:expr, $op:tt) => {{
        use ves_parser::ast::LitValue;
        match $lit {
            LitValue::Float(i) => LitValue::from($op i),
            rest => rest,
        }
    }};
    ($lit:expr, $f:expr) => {{
        use ves_parser::ast::LitValue;
        match $lit {
            LitValue::Float(i) => LitValue::from(($f)(i)),
            rest => rest,
        }
    }};
}

#[macro_export]
macro_rules! binary_arithm_map {
    ($left:expr, $right:expr, +) => {{
        use ves_parser::ast::LitValue;
        match (&$left, &$right) {
            (LitValue::Float(l), LitValue::Float(r)) => Some(LitValue::from(l + r)),
            (LitValue::Str(l), LitValue::Str(r)) => Some(
                LitValue::Str(Cow::<'a, str>::from(format!("{}{}", l, r)))
                    .into(),
            ),
            _ => None,
        }
    }};
    ($left:expr, $right:expr, **) => {{
        use ves_parser::ast::LitValue;
        match (&$left, &$right) {
            (LitValue::Float(l), LitValue::Float(r)) => Some(LitValue::from(l.powf(*r))),
            _ => None,
        }
    }};
    ($left:expr, $right:expr, $op:tt) => {{
        use ves_parser::ast::LitValue;
        match (&$left, &$right) {
            (LitValue::Float(l), LitValue::Float(r)) => Some(LitValue::from(*l $op *r)),
            _ => None,
        }
    }};
}

#[macro_export]
macro_rules! binary_ord_map {
    ($left:expr, $right:expr, $op:tt) => {{
        use ves_parser::ast::LitValue;
        #[allow(clippy::float_cmp)]
        match (&$left, &$right) {
            (LitValue::Float(l), LitValue::Float(r)) => Some(LitValue::from(l $op r)),
            _ => None,
        }
    }};
}

#[macro_export]
macro_rules! assign_lit_node_if_some {
    ($expr:expr, $left:expr, $right:expr, $value:expr) => {
        if let Some(value) = $value {
            let kind = ves_parser::ast::ExprKind::Lit(box ves_parser::ast::Lit {
                token: ves_parser::lexer::Token::new(
                    "<folded>",
                    usize::MAX..usize::MAX,
                    ves_parser::lexer::TokenKind::EOF,
                ),
                value,
            });
            $expr.kind = kind;
        }
    };
    ($expr:expr, $operand:expr, $value:expr) => {
        if let Some(value) = $value {
            $expr.kind = ves_parser::ast::ExprKind::Lit(box ves_parser::ast::Lit {
                token: $operand.token.clone(),
                value,
            })
        }
    };
}

#[macro_export]
macro_rules! fold_binary_op {
    ($expr:ident, $left:expr, $right:expr, **) => {
        crate::assign_lit_node_if_some!(
            $expr,
            $left,
            $right,
            crate::binary_arithm_map!($left.value, $right.value, **)
        )
    };
    ($expr:ident, $left:expr, $right:expr, $op:tt) => {
        crate::assign_lit_node_if_some!(
            $expr,
            $left,
            $right,
            crate::binary_arithm_map!($left.value, $right.value, $op)
        )
    };
    (ord => $expr:ident, $left:expr, $right:expr, $op:tt) => {
        crate::assign_lit_node_if_some!(
            $expr,
            $left,
            $right,
            crate::binary_ord_map!($left.value, $right.value, $op)
        )
    };
}
