use crate::builder::{BytecodeBuilder, Chunk};
use crate::opcode::Opcode;
use crate::Result;
use ves_parser::ast::*;

pub struct Emitter<'a> {
    builder: BytecodeBuilder,
    ast: AST<'a>,
}

impl<'a> Emitter<'a> {
    pub fn new(ast: AST<'a>) -> Emitter<'a> {
        Emitter {
            builder: BytecodeBuilder::new(ast.file_id),
            ast,
        }
    }

    pub fn emit(mut self) -> Result<Chunk> {
        let body = std::mem::take(&mut self.ast.body);
        for stmt in body.into_iter() {
            use StmtKind::*;
            match stmt.kind {
                ExprStmt(box expr) => self.emit_expr(expr)?,
                Var(_) => unimplemented!(),
                Loop(_) => unimplemented!(),
                For(_) => unimplemented!(),
                ForEach(_) => unimplemented!(),
                While(_) => unimplemented!(),
                Block(_) => unimplemented!(),
                Print(_) => unimplemented!(),
                Return(_) => unimplemented!(),
                Break(_) => unimplemented!(),
                Continue(_) => unimplemented!(),
                Defer(_) => unimplemented!(),
                _Empty => panic!("Unexpected StmtKind::_Empty"),
            }
        }

        Ok(self.builder.finish())
    }

    fn emit_expr(&mut self, expr: Expr) -> Result<()> {
        match expr.kind {
            ExprKind::Lit(box literal) => self.emit_lit(literal)?,

            ExprKind::Binary(op, box left, box right) => {
                self.emit_expr(left)?;
                self.emit_expr(right)?;
                self.builder.op(
                    {
                        use BinOpKind::*;
                        match op {
                            Is => unimplemented!(),
                            In => unimplemented!(),
                            Add => Opcode::Add,
                            Sub => Opcode::Subtract,
                            Mul => Opcode::Multiply,
                            Div => Opcode::Divide,
                            Rem => Opcode::Remainder,
                            Pow => Opcode::Power,
                            And => unimplemented!(),
                            Or => unimplemented!(),
                            Eq => unimplemented!(),
                            Ne => unimplemented!(),
                            Lt => unimplemented!(),
                            Le => unimplemented!(),
                            Ge => unimplemented!(),
                            Gt => unimplemented!(),
                        }
                    },
                    expr.span,
                );
            }
            ExprKind::Unary(op, operand) => {
                self.emit_expr(*operand)?;
                self.builder.op(
                    match op {
                        UnOpKind::Not => unimplemented!(),
                        UnOpKind::Neg => Opcode::Negate,
                        UnOpKind::Try => unimplemented!(),
                        UnOpKind::Ok => unimplemented!(),
                        UnOpKind::Err => unimplemented!(),
                    },
                    expr.span,
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
            ExprKind::Variable(_) => unimplemented!(),
            ExprKind::Range(_) => unimplemented!(),
            ExprKind::PrefixIncDec(_) => unimplemented!(),
            ExprKind::PostfixIncDec(_) => unimplemented!(),
            ExprKind::Assignment(_) => unimplemented!(),
            ExprKind::Grouping(_) => unimplemented!(),
            ExprKind::AtIdent(_) => unimplemented!(),
        }

        Ok(())
    }

    fn emit_lit(&mut self, lit: Lit) -> Result<()> {
        match lit.value {
            LitValue::Number(value) => match maybe_f32(value) {
                Some(value) => {
                    self.builder
                        .op(Opcode::PushSmallNumber(value), lit.token.span);
                }
                None => {
                    let offset = self
                        .builder
                        .constant(value.into(), lit.token.span.clone())?;
                    self.builder.op(Opcode::GetConst(offset), lit.token.span);
                }
            },
            LitValue::Bool(value) => {
                match value {
                    true => self.builder.op(Opcode::PushTrue, lit.token.span),
                    false => self.builder.op(Opcode::PushFalse, lit.token.span),
                };
            }
            LitValue::None => {
                self.builder.op(Opcode::PushNone, lit.token.span);
            }
            LitValue::Str(_value) => {
                unimplemented!()
            }
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
                Lexer::new("1 + 2 * 10 ** -1 / 2"),
                FileId::anon(),
                &VesFileDatabase::default(),
            )
            .parse()
            .unwrap()
        };
    }

    #[test]
    fn emit_simple_arithmetic_expr() {
        let chunk = Emitter::new(ast!("1 + (2 * ((10 ** -1) / 2))"))
            .emit()
            .unwrap();
        assert_eq!(
            chunk.code,
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
            ]
        );
    }
}
