use crate::builder::{BytecodeBuilder, Chunk};
use crate::opcode::Opcode;
use crate::Result;
use ves_parser::ast::{self, AST};

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
            match stmt.kind {
                ves_parser::ast::StmtKind::ExprStmt(expr) => self.emit_expr(*expr)?,
                ves_parser::ast::StmtKind::Var(_) => unimplemented!(),
                ves_parser::ast::StmtKind::Loop(_) => unimplemented!(),
                ves_parser::ast::StmtKind::For(_) => unimplemented!(),
                ves_parser::ast::StmtKind::ForEach(_) => unimplemented!(),
                ves_parser::ast::StmtKind::While(_) => unimplemented!(),
                ves_parser::ast::StmtKind::Block(_) => unimplemented!(),
                ves_parser::ast::StmtKind::Print(_) => unimplemented!(),
                ves_parser::ast::StmtKind::Return(_) => unimplemented!(),
                ves_parser::ast::StmtKind::Break(_) => unimplemented!(),
                ves_parser::ast::StmtKind::Continue(_) => unimplemented!(),
                ves_parser::ast::StmtKind::Defer(_) => unimplemented!(),
                ves_parser::ast::StmtKind::_Empty => panic!("Unexpected StmtKind::_Empty"),
            }
        }

        Ok(self.builder.finish())
    }

    fn emit_expr(&mut self, expr: ast::Expr) -> Result<()> {
        match expr.kind {
            ast::ExprKind::Lit(literal) => match literal.value {
                ast::LitValue::Number(value) => {
                    self.builder
                        .emit(Opcode::PushNumber(value), literal.token.span.clone());
                }
                ast::LitValue::Bool(_) => unimplemented!(),
                ast::LitValue::None => unimplemented!(),
                ast::LitValue::Str(_) => unimplemented!(),
            },

            ast::ExprKind::Binary(op, left, right) => {
                self.emit_expr(*left)?;
                self.emit_expr(*right)?;
                self.builder.emit(
                    match op {
                        ast::BinOpKind::Is => unimplemented!(),
                        ast::BinOpKind::In => unimplemented!(),
                        ast::BinOpKind::Add => Opcode::Add,
                        ast::BinOpKind::Sub => Opcode::Subtract,
                        ast::BinOpKind::Mul => Opcode::Multiply,
                        ast::BinOpKind::Div => Opcode::Divide,
                        ast::BinOpKind::Rem => Opcode::Remainder,
                        ast::BinOpKind::Pow => Opcode::Power,
                        ast::BinOpKind::And => unimplemented!(),
                        ast::BinOpKind::Or => unimplemented!(),
                        ast::BinOpKind::Eq => unimplemented!(),
                        ast::BinOpKind::Ne => unimplemented!(),
                        ast::BinOpKind::Lt => unimplemented!(),
                        ast::BinOpKind::Le => unimplemented!(),
                        ast::BinOpKind::Ge => unimplemented!(),
                        ast::BinOpKind::Gt => unimplemented!(),
                    },
                    expr.span,
                );
            }
            ast::ExprKind::Unary(op, operand) => {
                self.emit_expr(*operand)?;
                self.builder.emit(
                    match op {
                        ast::UnOpKind::Not => unimplemented!(),
                        ast::UnOpKind::Neg => Opcode::Negate,
                        ast::UnOpKind::Try => unimplemented!(),
                        ast::UnOpKind::Ok => unimplemented!(),
                        ast::UnOpKind::Err => unimplemented!(),
                    },
                    expr.span,
                );
            }

            ast::ExprKind::Struct(_) => unimplemented!(),
            ast::ExprKind::Fn(_) => unimplemented!(),
            ast::ExprKind::If(_) => unimplemented!(),
            ast::ExprKind::DoBlock(_) => unimplemented!(),
            ast::ExprKind::Comma(_) => unimplemented!(),
            ast::ExprKind::Call(_) => unimplemented!(),
            ast::ExprKind::Spread(_) => unimplemented!(),
            ast::ExprKind::GetProp(_) => unimplemented!(),
            ast::ExprKind::SetProp(_) => unimplemented!(),
            ast::ExprKind::GetItem(_) => unimplemented!(),
            ast::ExprKind::SetItem(_) => unimplemented!(),
            ast::ExprKind::FString(_) => unimplemented!(),
            ast::ExprKind::Array(_) => unimplemented!(),
            ast::ExprKind::Map(_) => unimplemented!(),
            ast::ExprKind::Variable(_) => unimplemented!(),
            ast::ExprKind::Range(_) => unimplemented!(),
            ast::ExprKind::PrefixIncDec(_) => unimplemented!(),
            ast::ExprKind::PostfixIncDec(_) => unimplemented!(),
            ast::ExprKind::Assignment(_) => unimplemented!(),
            ast::ExprKind::Grouping(_) => unimplemented!(),
            ast::ExprKind::AtIdent(_) => unimplemented!(),
        }

        Ok(())
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
                &VesFileDatabase::new(),
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
                Opcode::PushNumber(1f64),
                Opcode::PushNumber(2f64),
                Opcode::PushNumber(10f64),
                Opcode::PushNumber(-1f64),
                Opcode::Power,
                Opcode::Multiply,
                Opcode::PushNumber(2f64),
                Opcode::Divide,
                Opcode::Add,
            ]
        );
    }
}
