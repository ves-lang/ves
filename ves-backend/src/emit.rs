use crate::opcode::Opcode;
use crate::Result;
use crate::{
    builder::{BytecodeBuilder, Chunk},
    Span,
};
use ves_error::FileId;
use ves_parser::ast::*;
use ves_parser::lexer::Token;
use ves_runtime::Value;

struct Local<'a> {
    name: Token<'a>,
    depth: usize,
}

struct LoopInfo<'a> {
    label: Option<Token<'a>>,
    start: u32,
    depth: usize,
}
impl<'a> LoopInfo<'a> {
    pub fn new(label: Option<Token<'a>>, start: u32, depth: usize) -> LoopInfo<'a> {
        LoopInfo {
            label,
            start,
            depth,
        }
    }
}

struct State<'a> {
    builder: BytecodeBuilder,
    loops: Vec<LoopInfo<'a>>,
    locals: Vec<Local<'a>>,
    scope_depth: usize,
}
impl<'a> State<'a> {
    fn new(file_id: FileId) -> State<'a> {
        State {
            builder: BytecodeBuilder::new(file_id),
            loops: vec![],
            locals: vec![],
            scope_depth: 0,
        }
    }

    fn begin_scope(&mut self) {
        self.scope_depth += 1;
    }

    fn end_scope(&mut self, scope_span: Span) {
        self.scope_depth -= 1;

        // pop locals from the closed scope
        let mut pop_n = 0;
        while !self.locals.is_empty() && self.locals[self.locals.len() - 1].depth > self.scope_depth
        {
            pop_n += 1;
            self.locals.pop();
        }

        if pop_n > 1 {
            self.builder.op(Opcode::PopN(pop_n), scope_span);
        } else if pop_n == 1 {
            self.builder.op(Opcode::Pop, scope_span);
        }
    }

    fn begin_loop(&mut self, label: Option<&Token<'a>>) {
        self.loops.push(LoopInfo::new(
            label.cloned(),
            self.builder.offset(),
            self.scope_depth,
        ))
    }

    fn end_loop(&mut self) {
        self.loops.pop();
    }

    fn in_loop(&self) -> bool {
        !self.loops.is_empty()
    }

    fn add_local(&mut self, name: &Token<'a>) {
        self.locals.push(Local {
            name: name.clone(),
            depth: self.scope_depth,
        });
    }

    fn resolve_local(&mut self, name: &str) -> Option<u32> {
        // since local variables can shadow outer scopes,
        // we have to resolve starting from the top-most scope
        for (index, local) in self.locals.iter().enumerate().rev() {
            if local.name.lexeme == name {
                return Some(index as u32);
            }
        }
        None
    }

    fn define(&mut self, name: &Token<'a>) -> Result<()> {
        if self.scope_depth > 0 {
            self.add_local(name);
        }
        if self.scope_depth == 0 {
            // global scope
            // FIXME: stub before heap values are available
            // the constant here should be a string
            let offset = self.builder.constant(Value::None, name.span.clone())?;
            self.builder
                .op(Opcode::DefineGlobal(offset), name.span.clone());
        }
        Ok(())
    }
}

pub struct Emitter<'a> {
    states: Vec<State<'a>>,
    ast: AST<'a>,
}

impl<'a> Emitter<'a> {
    pub fn new(ast: AST<'a>) -> Emitter<'a> {
        Emitter {
            states: vec![State::new(ast.file_id)],
            ast,
        }
    }

    #[inline]
    fn state(&mut self) -> &mut State<'a> {
        self.states.last_mut().unwrap()
    }

    pub fn emit(mut self) -> Result<Chunk> {
        let body = std::mem::take(&mut self.ast.body);
        for stmt in body.into_iter() {
            self.emit_stmt(&stmt)?;
        }

        Ok(self.state().builder.finish())
    }

    fn emit_stmt(&mut self, stmt: &Stmt<'a>) -> Result<()> {
        use StmtKind::*;
        match &stmt.kind {
            ExprStmt(ref expr) => {
                self.emit_expr(expr)?;
                self.state().builder.op(Opcode::Pop, stmt.span.clone());
            }
            Var(ref vars) => {
                for var in vars {
                    if let Some(ref initializer) = var.initializer {
                        self.emit_expr(initializer)?;
                    } else {
                        self.state()
                            .builder
                            .op(Opcode::PushNone, var.name.span.clone());
                    }
                    self.state().define(&var.name)?;
                }
            }
            Loop(ref loop_) => self.emit_loop(loop_, stmt.span.clone())?,
            For(_) => unimplemented!(),
            ForEach(_) => unimplemented!(),
            While(_) => unimplemented!(),
            Block(ref body) => self.emit_block(body, stmt.span.clone())?,
            Print(ref expr) => match &expr.kind {
                ExprKind::Comma(ref exprs) => {
                    for expr in exprs {
                        self.emit_expr(expr)?;
                    }
                    self.state()
                        .builder
                        .op(Opcode::PrintN(exprs.len() as u32), expr.span.clone());
                }
                _ => {
                    self.emit_expr(expr)?;
                    self.state().builder.op(Opcode::Print, expr.span.clone());
                }
            },
            Return(_) => unimplemented!(),
            Break(_) => unimplemented!(),
            Continue(_) => unimplemented!(),
            Defer(_) => unimplemented!(),
            _Empty => panic!("Unexpected StmtKind::_Empty"),
        }

        Ok(())
    }

    fn emit_loop(&mut self, loop_: &Loop<'a>, span: Span) -> Result<()> {
        self.state().begin_loop(loop_.label.as_ref());
        self.emit_stmt(&loop_.body)?;
        let address = self.state().loops.last().unwrap().start;
        self.state().builder.op(Opcode::Jump(address), span);
        self.state().end_loop();
        Ok(())
    }

    fn emit_block(&mut self, body: &[Stmt<'a>], span: Span) -> Result<()> {
        self.state().begin_scope();
        for stmt in body {
            self.emit_stmt(stmt)?;
        }
        self.state().end_scope(span);

        Ok(())
    }

    fn emit_expr(&mut self, expr: &Expr) -> Result<()> {
        match expr.kind {
            ExprKind::Lit(ref literal) => self.emit_lit(literal)?,
            ExprKind::Binary(op, ref left, ref right) => {
                self.emit_binary_expr(op, left, right, expr.span.clone())?
            }
            ExprKind::Unary(op, ref operand) => {
                self.emit_expr(operand)?;
                self.state().builder.op(
                    match op {
                        UnOpKind::Not => Opcode::LogicalNot,
                        UnOpKind::Neg => Opcode::Negate,
                        UnOpKind::Try => Opcode::Try,
                        UnOpKind::Ok => Opcode::WrapOk,
                        UnOpKind::Err => Opcode::WrapErr,
                    },
                    expr.span.clone(),
                );
            }

            ExprKind::Struct(_) => unimplemented!(),
            ExprKind::Fn(_) => unimplemented!(),
            ExprKind::If(_) => unimplemented!(),
            ExprKind::DoBlock(_) => unimplemented!(),
            ExprKind::Comma(_) => unimplemented!(),
            ExprKind::Call(_) => unimplemented!(),
            ExprKind::Spread(_) => unimplemented!(),
            ExprKind::GetProp(_) => unimplemented!(),
            ExprKind::SetProp(_) => unimplemented!(),
            ExprKind::GetItem(_) => unimplemented!(),
            ExprKind::SetItem(_) => unimplemented!(),
            ExprKind::FString(_) => unimplemented!(),
            ExprKind::Array(_) => unimplemented!(),
            ExprKind::Map(_) => unimplemented!(),
            ExprKind::Variable(ref name) => self.emit_var_access(name)?,
            ExprKind::Range(_) => unimplemented!(),
            ExprKind::PrefixIncDec(_) => unimplemented!(),
            ExprKind::PostfixIncDec(_) => unimplemented!(),
            ExprKind::Assignment(_) => unimplemented!(),
            ExprKind::Grouping(ref expr) => self.emit_expr(expr)?,
            ExprKind::AtIdent(_) => unimplemented!(),
        }

        Ok(())
    }

    fn emit_binary_expr(
        &mut self,
        op: BinOpKind,
        left: &Expr,
        right: &Expr,
        span: Span,
    ) -> Result<()> {
        self.emit_expr(left)?;
        if op == BinOpKind::Is {
            let isnt = match right.kind {
                ExprKind::Lit(ref lit) if lit.token.lexeme == "none" => Some(Opcode::IsNone),
                ExprKind::Variable(ref var) => match var.lexeme.as_ref() {
                    "num" => Some(Opcode::IsNum),
                    "str" => Some(Opcode::IsStr),
                    "bool" => Some(Opcode::IsBool),
                    "map" => Some(Opcode::IsMap),
                    "array" => Some(Opcode::IsArray),
                    "some" => Some(Opcode::IsSome),
                    _ => None,
                },
                _ => None,
            };
            if let Some(inst) = isnt {
                self.state().builder.op(inst, span);
            } else {
                self.emit_expr(right)?;
                self.state().builder.op(Opcode::CompareType, span);
            }
        } else {
            self.emit_expr(right)?;
            self.state().builder.op(
                match op {
                    BinOpKind::In => Opcode::HasProperty,
                    BinOpKind::Add => Opcode::Add,
                    BinOpKind::Sub => Opcode::Subtract,
                    BinOpKind::Mul => Opcode::Multiply,
                    BinOpKind::Div => Opcode::Divide,
                    BinOpKind::Rem => Opcode::Remainder,
                    BinOpKind::Pow => Opcode::Power,
                    BinOpKind::And => Opcode::LogicalAnd,
                    BinOpKind::Or => Opcode::LogicalOr,
                    BinOpKind::Eq => Opcode::Equal,
                    BinOpKind::Ne => Opcode::NotEqual,
                    BinOpKind::Lt => Opcode::LessThan,
                    BinOpKind::Le => Opcode::LessEqual,
                    BinOpKind::Gt => Opcode::GreaterThan,
                    BinOpKind::Ge => Opcode::GreaterEqual,
                    BinOpKind::Is => unreachable!(),
                },
                span,
            );
        }

        Ok(())
    }

    fn emit_lit(&mut self, lit: &Lit) -> Result<()> {
        let span = lit.token.span.clone();
        match lit.value {
            LitValue::Number(value) => match maybe_f32(value) {
                Some(value) => {
                    self.state()
                        .builder
                        .op(Opcode::PushSmallNumber(value), span);
                }
                None => {
                    let offset = self.state().builder.constant(value.into(), span.clone())?;
                    self.state().builder.op(Opcode::GetConst(offset), span);
                }
            },
            LitValue::Bool(value) => {
                self.state().builder.op(
                    match value {
                        true => Opcode::PushTrue,
                        false => Opcode::PushFalse,
                    },
                    span,
                );
            }
            LitValue::None => {
                self.state().builder.op(Opcode::PushNone, span);
            }
            LitValue::Str(ref _value) => {
                // FIXME: stub before heap values are available
                // the constant here should be a string
                let offset = self.state().builder.constant(Value::None, span.clone())?;
                self.state().builder.op(Opcode::GetConst(offset), span);
            }
        }

        Ok(())
    }

    fn emit_var_access(&mut self, name: &Token<'_>) -> Result<()> {
        let span = name.span.clone();
        if let Some(index) = self.state().resolve_local(&name.lexeme) {
            self.state().builder.op(Opcode::GetLocal(index), span);
        } else {
            // FIXME: stub before heap values are available
            // the constant here should be a string
            let offset = self.state().builder.constant(Value::None, span.clone())?;
            self.state().builder.op(Opcode::GetGlobal(offset), span);
        }

        Ok(())
    }
}

/// Checks if `f64` fits within an `f32`, and converts it if so
fn maybe_f32(value: f64) -> Option<f32> {
    const MIN: f64 = f32::MIN as f64;
    const MAX: f64 = f32::MAX as f64;
    if (MIN..=MAX).contains(&value) {
        Some(value as f32)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;
    use ves_error::{FileId, VesFileDatabase};
    use ves_parser::{Lexer, Parser};

    macro_rules! ast {
        ($src:literal) => {
            Parser::new(
                Lexer::new($src),
                FileId::anon(),
                &VesFileDatabase::default(),
            )
            .parse()
            .unwrap()
        };
    }

    macro_rules! case {
        ($name:ident, $src:literal, $ops:expr) => {
            #[test]
            fn $name() {
                let chunk = Emitter::new(ast!($src)).emit().unwrap();
                assert_eq!(chunk.code, $ops);
            }
        };
    }

    case!(
        simple_arithmetic_expr,
        "1 + ((2 * (10 ** -1)) / 2)",
        vec![
            Opcode::PushSmallNumber(1.0),
            Opcode::PushSmallNumber(2.0),
            Opcode::PushSmallNumber(10.0),
            Opcode::PushSmallNumber(-1.0),
            Opcode::Power,
            Opcode::Multiply,
            Opcode::PushSmallNumber(2.0),
            Opcode::Divide,
            Opcode::Add,
            Opcode::Pop
        ]
    );
    case!(
        type_comparison_num,
        "0 is num",
        vec![Opcode::PushSmallNumber(0.0), Opcode::IsNum, Opcode::Pop]
    );
    case!(
        type_comparison_str,
        "0 is str",
        vec![Opcode::PushSmallNumber(0.0), Opcode::IsStr, Opcode::Pop]
    );
    case!(
        type_comparison_bool,
        "0 is bool",
        vec![Opcode::PushSmallNumber(0.0), Opcode::IsBool, Opcode::Pop]
    );
    case!(
        type_comparison_map,
        "0 is map",
        vec![Opcode::PushSmallNumber(0.0), Opcode::IsMap, Opcode::Pop]
    );
    case!(
        type_comparison_array,
        "0 is array",
        vec![Opcode::PushSmallNumber(0.0), Opcode::IsArray, Opcode::Pop]
    );
    case!(
        type_comparison_none,
        "0 is none",
        vec![Opcode::PushSmallNumber(0.0), Opcode::IsNone, Opcode::Pop]
    );
    case!(
        type_comparison_some,
        "0 is some",
        vec![Opcode::PushSmallNumber(0.0), Opcode::IsSome, Opcode::Pop]
    );
    case!(
        type_comparison_struct,
        "0 is T",
        vec![
            Opcode::PushSmallNumber(0.0),
            Opcode::GetGlobal(0),
            Opcode::CompareType,
            Opcode::Pop
        ]
    );
    case!(
        field_check,
        "0 in 0",
        vec![
            Opcode::PushSmallNumber(0.0),
            Opcode::PushSmallNumber(0.0),
            Opcode::HasProperty,
            Opcode::Pop
        ]
    );
    case!(
        global_variable,
        "let a = 0",
        vec![Opcode::PushSmallNumber(0.0), Opcode::DefineGlobal(0)]
    );
    case!(
        local_variable,
        "{ let a = 0; }",
        vec![Opcode::PushSmallNumber(0.0), Opcode::Pop]
    );
    case!(
        many_local_variables,
        "{ mut a, b, c, d }",
        vec![
            Opcode::PushNone,
            Opcode::PushNone,
            Opcode::PushNone,
            Opcode::PushNone,
            Opcode::PopN(4)
        ]
    );
    case!(
        print_one,
        "print(0)",
        vec![Opcode::PushSmallNumber(0.0), Opcode::Print,]
    );
    case!(
        print_many,
        "print(0, 2, 2)",
        vec![
            Opcode::PushSmallNumber(0.0),
            Opcode::PushSmallNumber(2.0),
            Opcode::PushSmallNumber(2.0),
            Opcode::PrintN(3),
        ]
    );
    case!(
        get_global,
        "mut a; a;",
        vec![
            Opcode::PushNone,
            Opcode::DefineGlobal(0),
            Opcode::GetGlobal(1),
            Opcode::Pop
        ]
    );
    case!(
        get_local,
        "{ mut a; a; }",
        vec![
            Opcode::PushNone,
            Opcode::GetLocal(0),
            Opcode::Pop,
            Opcode::Pop
        ]
    );
    case!(
        multi_scope_local_resolution,
        "{ mut a; { mut a; { mut a; { mut a; a; } a; } a; } a; }",
        vec![
            Opcode::PushNone,
            Opcode::PushNone,
            Opcode::PushNone,
            Opcode::PushNone,
            Opcode::GetLocal(3),
            Opcode::Pop,
            Opcode::Pop,
            Opcode::GetLocal(2),
            Opcode::Pop,
            Opcode::Pop,
            Opcode::GetLocal(1),
            Opcode::Pop,
            Opcode::Pop,
            Opcode::GetLocal(0),
            Opcode::Pop,
            Opcode::Pop,
        ]
    );
    case!(unlabeled_loop, "loop {}", vec![Opcode::Jump(0)]);
}
