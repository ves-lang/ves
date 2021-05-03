use std::{borrow::Cow, collections::HashMap, rc::Rc};

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

#[derive(Debug)]
struct Local<'a> {
    name: Token<'a>,
    depth: usize,
}

/// A named label used by a loop.
struct LoopLabel {
    /// The scope depth of the loop we're jumping / breaking from.
    loop_scope_depth: usize,
    start_label: u32,
    end_label: u32,
}

#[derive(Clone, Copy, PartialEq)]
enum LoopControl {
    Break,
    Continue,
}

struct State<'a> {
    builder: BytecodeBuilder,
    locals: Vec<Local<'a>>,
    globals: Rc<HashMap<String, u32>>,
    scope_depth: usize,

    // The id of the next label
    label_id: u32,
    /// All reserved labels
    labels: Vec<u32>,
    /// The label used for loop jumps
    loop_labels: HashMap<Cow<'a, str>, LoopLabel>,
}

impl<'a> State<'a> {
    fn new(file_id: FileId, globals: Rc<HashMap<String, u32>>) -> Self {
        State {
            builder: BytecodeBuilder::new(file_id),
            locals: vec![],
            loop_labels: HashMap::new(),
            labels: Vec::new(),
            globals,
            scope_depth: 0,
            label_id: 0,
        }
    }

    fn finish(&mut self) -> Chunk {
        self.builder.finish(std::mem::take(&mut self.labels))
    }

    fn begin_scope(&mut self) -> usize {
        self.scope_depth += 1;
        self.scope_depth
    }

    fn end_scope(&mut self, scope_span: Span) {
        self.scope_depth -= 1;
        // pop locals from the closed scope
        let mut n_locals = 0;
        for local in self.locals.iter().rev() {
            if local.depth <= self.scope_depth {
                break;
            }
            n_locals += 1;
        }
        self.locals
            .drain(self.locals.len() - n_locals..self.locals.len());
        self.op_pop(n_locals as u32, scope_span);
    }

    fn op_pop(&mut self, n: u32, span: Span) {
        if n == 1 {
            self.builder.op(Opcode::Pop, span);
        } else if n > 1 {
            self.builder.op(Opcode::PopN(n), span);
        }
    }

    fn begin_loop(&mut self) {
        self.scope_depth += 1;
    }

    fn end_loop(&mut self) {
        self.scope_depth -= 1;
    }

    fn reserve_label(&mut self) -> u32 {
        self.labels.push(self.label_id);
        self.label_id += 1;
        self.label_id - 1
    }

    fn count_locals_in_scope(&mut self, outer_scope_depth: usize) -> u32 {
        self.locals
            .iter()
            .rev()
            .take_while(|l| l.depth >= outer_scope_depth)
            .count() as u32
    }

    fn add_local(&mut self, name: &Token<'a>) -> bool {
        for l in self.locals.iter().rev() {
            // The variable is already in the scope so we do not need to reserve a slot
            if l.depth == self.scope_depth && l.name.lexeme == name.lexeme {
                return true;
            }
        }

        self.locals.push(Local {
            name: name.clone(),
            depth: self.scope_depth,
        });

        false
    }

    fn resolve_local(&mut self, name: &str) -> Option<u32> {
        // since local variables can shadow outer scopes,
        // we have to resolve starting from the innermost scope
        for (index, local) in self.locals.iter().enumerate().rev() {
            if local.name.lexeme == name {
                return Some(index as u32);
            }
        }
        None
    }

    fn define(&mut self, name: &Token<'a>) -> Result<()> {
        if self.scope_depth == 0 {
            let index = self
                .globals
                .get(&name.lexeme[..])
                .ok_or_else(||
                 /* This shouldn't ever happen since we collect and check all globals */
                 format!("Attempted to define the variable `{}` as a global variable", name.lexeme))
                .unwrap();
            self.builder
                .op(Opcode::SetGlobal(*index), name.span.clone());
        } else {
            self.add_local(name);
        }

        Ok(())
    }
}

pub struct Emitter<'a> {
    states: Vec<State<'a>>,
    ast: AST<'a>,
    globals: Rc<HashMap<String, u32>>,
}

impl<'a> Emitter<'a> {
    pub fn new(ast: AST<'a>) -> Emitter<'a> {
        let mut globals = HashMap::new();
        for global in &ast.globals {
            let idx = globals.len();
            globals.insert(global.name.lexeme.clone().into_owned(), idx as u32);
        }
        let globals = Rc::new(globals);
        Emitter {
            states: vec![State::new(ast.file_id, globals.clone())],
            globals,
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

        Ok(self.state().finish())
    }

    fn emit_stmt(&mut self, stmt: &Stmt<'a>) -> Result<()> {
        let span = stmt.span.clone();
        use StmtKind::*;
        match &stmt.kind {
            ExprStmt(ref expr) => self.emit_expr_stmt(expr, span)?,
            Var(ref vars) => self.emit_var_stmt(vars)?,
            Loop(ref loop_) => self.emit_loop(loop_, span)?,
            For(_) => unimplemented!(),
            ForEach(_) => unimplemented!(),
            While(_) => unimplemented!(),
            Block(ref body) => self.emit_block(body, span)?,
            Print(ref expr) => self.emit_print_stmt(expr)?,
            Return(_) => unimplemented!(),
            // TODO: make these pretty
            Break(label) => self.emit_loop_control(label, LoopControl::Break, span)?,
            Continue(label) => self.emit_loop_control(label, LoopControl::Continue, span)?,
            Defer(_) => unimplemented!(),
            _Empty => panic!("Unexpected StmtKind::_Empty"),
        }

        Ok(())
    }

    fn emit_expr_stmt(&mut self, expr: &Expr, span: Span) -> Result<()> {
        self.emit_expr(expr)?;
        self.state().builder.op(Opcode::Pop, span);
        Ok(())
    }

    fn emit_var_stmt(&mut self, vars: &[Var<'a>]) -> Result<()> {
        for var in vars {
            let span = var.name.span.clone();
            if let Some(ref initializer) = var.initializer {
                self.emit_expr(initializer)?;
            } else {
                self.state().builder.op(Opcode::PushNone, span);
            }
            self.state().define(&var.name)?;
        }
        Ok(())
    }

    fn emit_print_stmt(&mut self, expr: &Expr) -> Result<()> {
        let span = expr.span.clone();
        match &expr.kind {
            ExprKind::Comma(ref exprs) => {
                for expr in exprs {
                    self.emit_expr(expr)?;
                }
                self.state()
                    .builder
                    .op(Opcode::PrintN(exprs.len() as u32), span);
            }
            _ => {
                self.emit_expr(expr)?;
                self.state().builder.op(Opcode::Print, span);
            }
        }
        Ok(())
    }

    fn emit_label(&mut self, named_label: Option<(&Token<'a>, usize)>) -> (u32, u32) {
        let label = self.state().reserve_label();
        let other = if let Some((name, depth)) = named_label {
            let end_label = self.state().reserve_label();
            self.state().loop_labels.insert(
                name.lexeme.clone(),
                LoopLabel {
                    loop_scope_depth: depth,
                    start_label: label,
                    end_label,
                },
            );
            end_label
        } else {
            label
        };
        self.state().builder.label(label);
        (label, other)
    }

    fn emit_loop_control(
        &mut self,
        label: &Token<'a>,
        kind: LoopControl,
        span: Span,
    ) -> Result<()> {
        let loop_label = self.state().loop_labels.get(&label.lexeme).unwrap();
        let scope_depth = loop_label.loop_scope_depth;
        // `break` jumps to the end of the loop, `continue` jumps to the start
        let label_id = if kind == LoopControl::Break {
            loop_label.end_label
        } else {
            loop_label.start_label
        };
        // Locals from the loop's inner scopes have to be popped off the stack
        let n_locals = self.state().count_locals_in_scope(scope_depth);
        self.state().op_pop(n_locals, span);
        self.state()
            .builder
            .op(Opcode::Jump(label_id), label.span.clone());
        Ok(())
    }

    fn emit_loop(&mut self, r#loop: &Loop<'a>, span: Span) -> Result<()> {
        // This simply increases the scope depth (required for loop labels to work properly)
        self.state().begin_loop();

        // Emit the loop start label and reserve one label for its end
        let scope_depth = self.state().scope_depth;
        let (loop_start_label, loop_end_label) =
            self.emit_label(Some((&r#loop.label, scope_depth)));

        // Compile the loop body with a jump to the start at the end
        self.emit_stmt(&r#loop.body)?;
        self.state()
            .builder
            .op(Opcode::Jump(loop_start_label), span);

        // Emit the previously reserved end label
        self.state().builder.label(loop_end_label);

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
        let span = expr.span.clone();
        match expr.kind {
            ExprKind::Lit(ref literal) => self.emit_lit(literal)?,
            ExprKind::Binary(op, ref a, ref b) => self.emit_binary_expr(op, a, b, span)?,
            ExprKind::Unary(op, ref operand) => self.emit_unary_expr(op, operand, span)?,
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
                    BinOpKind::Subtract => Opcode::Subtract,
                    BinOpKind::Multiply => Opcode::Multiply,
                    BinOpKind::Divide => Opcode::Divide,
                    BinOpKind::Remainder => Opcode::Remainder,
                    BinOpKind::Power => Opcode::Power,
                    BinOpKind::And => Opcode::And,
                    BinOpKind::Or => Opcode::Or,
                    BinOpKind::Equal => Opcode::Equal,
                    BinOpKind::NotEqual => Opcode::NotEqual,
                    BinOpKind::LessThan => Opcode::LessThan,
                    BinOpKind::LessEqual => Opcode::LessEqual,
                    BinOpKind::GreaterThan => Opcode::GreaterThan,
                    BinOpKind::GreaterEqual => Opcode::GreaterEqual,
                    BinOpKind::Is => unreachable!(),
                },
                span,
            );
        }
        Ok(())
    }

    fn emit_unary_expr(&mut self, op: UnOpKind, operand: &Expr, span: Span) -> Result<()> {
        self.emit_expr(operand)?;
        self.state().builder.op(
            match op {
                UnOpKind::Not => Opcode::Not,
                UnOpKind::Negate => Opcode::Negate,
                UnOpKind::Try => Opcode::Try,
                UnOpKind::WrapOk => Opcode::WrapOk,
                UnOpKind::WrapErr => Opcode::WrapErr,
            },
            span,
        );
        Ok(())
    }

    fn emit_lit(&mut self, lit: &Lit) -> Result<()> {
        let span = lit.token.span.clone();
        match lit.value {
            LitValue::Number(value) => match maybe_f32(value) {
                Some(value) => {
                    self.state().builder.op(Opcode::PushNum32(value), span);
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
        println!("{:?} {:?}", name, &self.state().locals);
        if let Some(index) = self.state().resolve_local(&name.lexeme) {
            self.state().builder.op(Opcode::GetLocal(index), span);
        } else {
            println!("{}", name.lexeme);
            let id = *self.globals.get(&name.lexeme[..]).unwrap();
            self.state().builder.op(Opcode::GetGlobal(id), span);
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
    use ves_middle::Resolver;
    use ves_parser::{Lexer, Parser};

    macro_rules! ast {
        ($src:literal) => {{
            let mut ast = Parser::new(
                Lexer::new($src),
                FileId::anon(),
                &VesFileDatabase::default(),
            )
            .parse()
            .unwrap();
            Resolver::new().resolve(&mut ast).unwrap();
            ast
        }};
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
            Opcode::PushNum32(1.0),
            Opcode::PushNum32(2.0),
            Opcode::PushNum32(10.0),
            Opcode::PushNum32(-1.0),
            Opcode::Power,
            Opcode::Multiply,
            Opcode::PushNum32(2.0),
            Opcode::Divide,
            Opcode::Add,
            Opcode::Pop
        ]
    );
    case!(
        type_comparison_num,
        "0 is num",
        vec![Opcode::PushNum32(0.0), Opcode::IsNum, Opcode::Pop]
    );
    case!(
        type_comparison_str,
        "0 is str",
        vec![Opcode::PushNum32(0.0), Opcode::IsStr, Opcode::Pop]
    );
    case!(
        type_comparison_bool,
        "0 is bool",
        vec![Opcode::PushNum32(0.0), Opcode::IsBool, Opcode::Pop]
    );
    case!(
        type_comparison_map,
        "0 is map",
        vec![Opcode::PushNum32(0.0), Opcode::IsMap, Opcode::Pop]
    );
    case!(
        type_comparison_array,
        "0 is array",
        vec![Opcode::PushNum32(0.0), Opcode::IsArray, Opcode::Pop]
    );
    case!(
        type_comparison_none,
        "0 is none",
        vec![Opcode::PushNum32(0.0), Opcode::IsNone, Opcode::Pop]
    );
    case!(
        type_comparison_some,
        "0 is some",
        vec![Opcode::PushNum32(0.0), Opcode::IsSome, Opcode::Pop]
    );
    case!(
        type_comparison_struct,
        "mut T; 0 is T",
        vec![
            /* 00 */ Opcode::PushNone,
            /* 01 */ Opcode::SetGlobal(0),
            /* 02 */ Opcode::PushNum32(0.0),
            /* 03 */ Opcode::GetGlobal(0),
            /* 04 */ Opcode::CompareType,
            /* 05 */ Opcode::Pop
        ]
    );
    case!(
        field_check,
        "0 in 0",
        vec![
            /* 00 */ Opcode::PushNum32(0.0),
            /* 01 */ Opcode::PushNum32(0.0),
            /* 02 */ Opcode::HasProperty,
            /* 03 */ Opcode::Pop
        ]
    );
    case!(
        global_variable,
        "let a = 0",
        vec![
            /* 00 */ Opcode::PushNum32(0.0), //
            /* 01 */ Opcode::SetGlobal(0) //    let a = 0
        ]
    );
    case!(
        local_variable,
        "{ let a = 0; }",
        vec![
            /* 00 */ Opcode::PushNum32(0.0), // let a = 0
            /* 01 */ Opcode::Pop //             pop a
        ]
    );
    case!(
        many_local_variables,
        "{ mut a, b, c, d }",
        vec![
            /* 00 */ Opcode::PushNone, //   mut a = none
            /* 01 */ Opcode::PushNone, //   mut b = none
            /* 02 */ Opcode::PushNone, //   mut c = none
            /* 03 */ Opcode::PushNone, //   mut d = none
            /* 04 */ Opcode::PopN(4) //     pop a, b, c, d
        ]
    );
    case!(
        print_one,
        "print(0)",
        vec![
            /* 00 */ Opcode::PushNum32(0.0),
            /* 01 */ Opcode::Print,
        ]
    );
    case!(
        print_many,
        "print(0, 2, 2)",
        vec![
            /* 00 */ Opcode::PushNum32(0.0),
            /* 01 */ Opcode::PushNum32(2.0),
            /* 02 */ Opcode::PushNum32(2.0),
            /* 03 */ Opcode::PrintN(3),
        ]
    );
    case!(
        get_global,
        "mut a; a;",
        vec![
            /* 00 */ Opcode::PushNone, //
            /* 01 */ Opcode::SetGlobal(0), //   mut a = none
            /* 02 */ Opcode::GetGlobal(0), //   get a
            /* 03 */ Opcode::Pop //             pop get a
        ]
    );
    case!(
        get_local,
        "{ mut a; a; }",
        vec![
            /* 00 */ Opcode::PushNone, //       mut a = none
            /* 01 */ Opcode::GetLocal(0), //    get a
            /* 02 */ Opcode::Pop, //            pop get a
            /* 03 */ Opcode::Pop //             pop a
        ]
    );
    case!(
        multi_scope_local_resolution,
        "{ mut a; { mut a; { mut a; { mut a; a; } a; } a; } a; }",
        vec![
            /* 00 */ Opcode::PushNone, //       mut a = none <depth: 1>
            /* 01 */ Opcode::PushNone, //       mut a = none <depth: 2>
            /* 02 */ Opcode::PushNone, //       mut a = none <depth: 3>
            /* 03 */ Opcode::PushNone, //       mut a = none <depth: 4>
            /* 04 */ Opcode::GetLocal(3), //    get a        <depth: 4>
            /* 05 */ Opcode::Pop, //            pop get a    <depth: 4>
            /* 06 */ Opcode::Pop, //            pop a        <depth: 4>
            /* 07 */ Opcode::GetLocal(2), //    get a        <depth: 3>
            /* 08 */ Opcode::Pop, //            pop get a    <depth: 3>
            /* 09 */ Opcode::Pop, //            pop a        <depth: 3>
            /* 10 */ Opcode::GetLocal(1), //    get a        <depth: 2>
            /* 11 */ Opcode::Pop, //            pop get a    <depth: 2>
            /* 12 */ Opcode::Pop, //            pop a        <depth: 2>
            /* 13 */ Opcode::GetLocal(0), //    get a        <depth: 1>
            /* 14 */ Opcode::Pop, //            pop get a    <depth: 1>
            /* 15 */ Opcode::Pop, //            pop a        <depth: 1>
        ]
    );
    case!(unlabeled_loop, "loop {}", vec![Opcode::Jump(0)]);
    case!(
        loop_with_body,
        "loop { mut a; 1 + 1; }",
        vec![
            /* 00 */ Opcode::PushNone, //       mut a = none <loop start>
            /* 01 */ Opcode::PushNum32(1.0), //
            /* 02 */ Opcode::PushNum32(1.0), //
            /* 03 */ Opcode::Add, //            1 + 1
            /* 04 */ Opcode::Pop, //            pop result of 1 + 1
            /* 05 */ Opcode::Pop, //            pop a
            /* 06 */ Opcode::Jump(0) //         jump to start of loop <loop end>
        ]
    );
    case!(
        loop_inside_scope,
        "mut a; { mut b; { mut c; loop { mut d = c; a + b; loop {} } } }",
        vec![
            /* 00 */ Opcode::PushNone, //
            /* 01 */ Opcode::SetGlobal(0), //   mut a = none
            /* 02 */ Opcode::PushNone, //       mut b = none <loop #1 start>
            /* 03 */ Opcode::PushNone, //       mut c = none
            /* 04 */ Opcode::GetLocal(1), //    mut d = c
            /* 05 */ Opcode::GetGlobal(0), //   a
            /* 06 */ Opcode::GetLocal(0), //    b
            /* 07 */ Opcode::Add, //            a + b
            /* 08 */ Opcode::Pop, //            pop a + b
            /* 09 */ Opcode::Jump(9), //        jump to loop 2 <loop #2 start + end>
            /* 10 */ Opcode::Pop, //            pop d
            /* 11 */ Opcode::Jump(4), //        jump to loop 1 <loop #1 end>
            /* 12 */ Opcode::Pop, //            pop c
            /* 13 */ Opcode::Pop //             pop b
        ]
    );
    case!(
        continue_in_empty_loop,
        "loop { continue; }",
        vec![
            /* 00 */ Opcode::Jump(0), //    jump to start of loop
            /* 00 */ Opcode::Jump(0) //     (unreachable) continue
        ]
    );
    case!(
        break_in_empty_loop,
        "loop { break; }\n  none",
        vec![
            /* 00 */ Opcode::Jump(2), //    break
            /* 01 */ Opcode::Jump(0), //    (unreachable) jump to start of loop
            /* 02 */ Opcode::PushNone, //   push none <- break jumps to here
            /* 03 */ Opcode::Pop //         pop none
        ]
    );
    case!(
        continue_in_loop_with_values,
        "mut a; loop { mut b = a; print(5 + b); continue; none; }",
        vec![
            /* 00 */ Opcode::PushNone, //
            /* 01 */ Opcode::SetGlobal(0), //   mut a = none
            /* 02 */ Opcode::GetGlobal(0), //   mut b = a
            /* 03 */ Opcode::PushNum32(5.0), // push 5
            /* 04 */ Opcode::GetLocal(0), //    get b
            /* 05 */ Opcode::Add, //            5 + b
            /* 06 */ Opcode::Print, //          print result of 5 + b
            /* 07 */ Opcode::Pop, //            pop b
            /* 08 */ Opcode::Jump(2), //        continue -> jump to start of loop
            /* 09 */ Opcode::PushNone, //       (unreachable) none
            /* 10 */ Opcode::Pop, //            (unreachable) pop none
            /* 11 */ Opcode::Pop, //            (unreachable) pop b
            /* 12 */ Opcode::Jump(2), //        < loop end >
        ]
    );
    case!(
        break_in_loop_with_values,
        "mut a; loop { mut b = a; print(5 + b); break; none; }\n print(a)",
        vec![
            /* 00 */ Opcode::PushNone, //
            /* 01 */ Opcode::SetGlobal(0), //   mut a = none
            /* 02 */ Opcode::GetGlobal(0), //   mut b = a
            /* 03 */ Opcode::PushNum32(5.0), // push 5
            /* 04 */ Opcode::GetLocal(0), //    get b
            /* 05 */ Opcode::Add, //            5 + b
            /* 06 */ Opcode::Print, //          print result of 5 + b
            /* 07 */ Opcode::Pop, //            pop b
            /* 08 */ Opcode::Jump(13), //       break -> jump to end of loop
            /* 09 */ Opcode::PushNone, //       (unreachable) none
            /* 10 */ Opcode::Pop, //            (unreachable) pop none
            /* 11 */ Opcode::Pop, //            (unreachable) pop b
            /* 12 */ Opcode::Jump(2), //        < loop end >
            /* 13 */ Opcode::GetGlobal(0), //   get a <- break jumps to here
            /* 14 */ Opcode::Print, //          print a
        ]
    );
    case!(
        break_and_continue_with_labels,
        r#"
        mut a;
        @first: loop { 
            mut b;
            @second: loop {
                mut c;
                continue @first;
                break @second;
            }
            @third: loop {
                mut d;
                break @first;
                continue @third;
            }
        }"#,
        vec![
            /* 00 */ Opcode::PushNone, //
            /* 01 */ Opcode::SetGlobal(0), //   mut a = none
            /* 02 */ Opcode::PushNone, //       mut b = none
            /* 03 */ Opcode::PushNone, //       mut c = none
            /* 04 */ Opcode::PopN(2), //        pop c and b
            /* 05 */ Opcode::Jump(2), //        continue @first
            /* 06 */ Opcode::Pop, //            pop c
            /* 07 */ Opcode::Jump(10), //       break second
            /* 08 */ Opcode::Pop, //            pop c
            /* 09 */ Opcode::Jump(3), //        continue @second
            /* 10 */ Opcode::PushNone, //       mut d = none
            /* 11 */ Opcode::PopN(2), //        pop d and b
            /* 12 */ Opcode::Jump(19), //       break @first
            /* 13 */ Opcode::Pop, //            pop d
            /* 14 */ Opcode::Jump(10), //       continue @third
            /* 15 */ Opcode::Pop, //            pop d
            /* 16 */ Opcode::Jump(10), //       continue @third
            /* 17 */ Opcode::Pop, //            pop b
            /* 18 */ Opcode::Jump(2), //        @continue first
        ]
    );
}