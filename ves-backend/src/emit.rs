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

/// A label used in loop control flow (break/continue)
struct ControlLabel {
    /// The scope depth of the loop we're jumping / breaking from.
    depth: usize,
    /// The ID of the label to which a `continue` should jump.
    start: u32,
    /// The ID of the label to which a `break` should jump.
    end: u32,
}
#[derive(Clone, Copy, PartialEq)]
enum LoopControl {
    Break,
    Continue,
}

/// QQQ(moscow): the word `label` is overloaded a lot here.
/// can we call it `virtual address` instead of a `label` for the "label ids" that are used for virtual jumps
/// and `labels` for the "physical" LoopLabel, which holds the start/end of a loop?

struct State<'a> {
    builder: BytecodeBuilder,
    locals: Vec<Local<'a>>,
    globals: Rc<HashMap<String, u32>>,
    scope_depth: usize,

    // The id of the next label
    label_id: u32,
    /// Reserved label IDs
    labels: Vec<u32>,
    /// The label used for loop jumps
    control_labels: HashMap<Cow<'a, str>, ControlLabel>,
}

impl<'a> State<'a> {
    fn new(file_id: FileId, globals: Rc<HashMap<String, u32>>) -> Self {
        State {
            builder: BytecodeBuilder::new(file_id),
            locals: vec![],
            control_labels: HashMap::new(),
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

    fn reserve_labels<const N: usize>(&mut self) -> [u32; N] {
        let mut out = [u32::MAX; N];
        for label in out.iter_mut() {
            self.labels.push(self.label_id);
            self.label_id += 1;
            *label = self.label_id - 1;
        }
        out
    }

    fn add_control_label(&mut self, name: &Token<'a>, start_label: u32, end_label: u32) {
        let loop_scope_depth = self.scope_depth;
        self.control_labels.insert(
            name.lexeme.clone(),
            ControlLabel {
                depth: loop_scope_depth,
                start: start_label,
                end: end_label,
            },
        );
    }

    fn resolve_label(&mut self, name: &Token<'a>) -> Option<&ControlLabel> {
        self.control_labels.get(&name.lexeme)
    }

    fn count_locals_in_scope(&mut self, outer_scope_depth: usize) -> u32 {
        self.locals
            .iter()
            .rev()
            .take_while(|l| l.depth >= outer_scope_depth)
            .count() as u32
    }

    fn add_local(&mut self, name: &Token<'a>) {
        self.locals.push(Local {
            name: name.clone(),
            depth: self.scope_depth,
        });
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

    fn resolve_variable_get(&mut self, name: &str) -> Opcode {
        if let Some(index) = self.resolve_local(name) {
            Opcode::GetLocal(index)
        } else if let Some(index) = self.globals.get(name).copied() {
            Opcode::GetGlobal(index)
        } else {
            panic!("Undefined variable: {}", name)
        }
    }

    fn resolve_variable_set(&mut self, name: &str) -> Opcode {
        if let Some(index) = self.resolve_local(name) {
            Opcode::SetLocal(index)
        } else if let Some(index) = self.globals.get(name).copied() {
            Opcode::SetGlobal(index)
        } else {
            panic!("Undefined variable: {}", name)
        }
    }

    fn define(&mut self, name: &Token<'a>) -> Result<()> {
        if self.scope_depth == 0 {
            let index = self
                .globals
                .get(&name.lexeme[..])
                .copied()
                .ok_or_else(|| {
                    format!(
                        /* This shouldn't ever happen since we collect and check all globals */
                        "Attempted to define the variable `{}` as a global variable",
                        name.lexeme
                    )
                })
                .unwrap();
            self.builder.op(Opcode::SetGlobal(index), name.span.clone());
            self.op_pop(1, name.span.clone());
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
            Loop(ref info) => self.emit_loop(info, span)?,
            For(ref info) => self.emit_for_loop(info, span)?,
            ForEach(_) => unimplemented!(),
            While(ref info) => self.emit_while_loop(info, span)?,
            Block(ref body) => self.emit_block(body, span)?,
            Print(ref expr) => self.emit_print_stmt(expr)?,
            Return(_) => unimplemented!(),
            Break(label) => self.emit_loop_control(label, LoopControl::Break, span)?,
            Continue(label) => self.emit_loop_control(label, LoopControl::Continue, span)?,
            Defer(_) => unimplemented!(),
            _Empty => panic!("Unexpected StmtKind::_Empty"),
        }

        Ok(())
    }

    fn emit_expr_stmt(&mut self, expr: &Expr<'a>, span: Span) -> Result<()> {
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

    fn emit_print_stmt(&mut self, expr: &Expr<'a>) -> Result<()> {
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

    fn emit_loop_control(
        &mut self,
        label: &Token<'a>,
        kind: LoopControl,
        span: Span,
    ) -> Result<()> {
        let control_label = self.state().resolve_label(label).unwrap();
        let scope_depth = control_label.depth;
        // `break` jumps to the end of the loop, `continue` jumps to the start
        let label_id = if kind == LoopControl::Break {
            control_label.end
        } else {
            control_label.start
        };
        // Locals from the loop's inner scopes have to be popped off the stack
        let n_locals = self.state().count_locals_in_scope(scope_depth);
        self.state().op_pop(n_locals, span);
        self.state()
            .builder
            .op(Opcode::Jump(label_id), label.span.clone());
        Ok(())
    }

    /// Emits the bytecode for a simple infinite loop without a condition.
    ///
    /// # Layout
    /// The basic layout of this loop looks like this:
    /// ```x86asm
    /// start:
    ///   <body>
    ///   jump @start
    /// end:
    /// ```
    ///
    /// If `continue` or `break` is used, they simply target the start or end label, respectively.
    /// Note that both statements must pop off the locals within the loop scope before jumping (not shown here).
    /// ```x86asm
    /// start:
    ///   <code>
    ///   jump @start    ; user-supplied continue
    ///   jump @end      ; user-supplied break
    ///   jump @start    ; default loop jump
    /// end:
    /// ```
    fn emit_loop(&mut self, info: &Loop<'a>, span: Span) -> Result<()> {
        self.state().begin_loop();

        // Reserve two labels - start and end of the loop.
        let [start, end] = self.state().reserve_labels::<2>();

        // The labels may be used for explicit control flow with break and continue,
        // so we need to declare them.
        self.state().add_control_label(&info.label, start, end);

        // Emit the loop body with a jump to the start label at the end
        self.state().builder.label(start);
        self.emit_stmt(&info.body)?;
        self.state().builder.op(Opcode::Jump(start), span);

        // Emit the end label
        self.state().builder.label(end);

        self.state().end_loop();
        Ok(())
    }

    /// Emits the bytecode for a while loop.
    ///
    /// # Layout
    /// The basic layout of this loop looks like this:
    /// ```x86asm
    /// start:
    ///     <condition>
    ///     jump_if_false @exit
    ///     pop condition result
    ///     <body>
    ///     jump @start
    /// exit:
    ///     pop condition result
    /// end:
    /// ```
    ///
    /// If `break` or `continue` is used, they simply target the start or end label, respectively.
    /// Note that both statements must pop off the locals within the loop scope before jumping (not shown here).
    /// ```x86asm
    /// start:
    ///     <condition>
    ///     jump_if_false @exit
    ///     pop condition result
    ///     <body>
    ///     jump @end    ; user-supplied break
    ///     jump @start  ; user-supplied continue
    ///     jump @start  ; default loop jump
    /// exit:
    ///     pop condition result
    /// end:
    ///
    /// TODO: describe the layout for the loops with a binding
    /// ```
    fn emit_while_loop(&mut self, info: &While<'a>, span: Span) -> Result<()> {
        self.state().begin_loop();

        // Reserve three labels as required by the layout
        let [start, exit, end] = self.state().reserve_labels::<3>();

        // Break statements jump to the @end label (not @exit), so that's what we need to declare
        self.state().add_control_label(&info.label, start, end);

        // Emit the start label and compile the condition
        self.state().builder.label(start);

        match &info.condition.pattern {
            ConditionPattern::Value => {
                // A simple value condition: evaluate it and jump to the exit label if it's false
                self.emit_expr(&info.condition.value)?;
                self.state()
                    .builder
                    .op(Opcode::JumpIfFalse(exit), span.clone());

                // If this instruction is reached, the condition was true, and the jump didn't occur, so
                // we need to clean up the condition value.
                self.state().builder.op(Opcode::Pop, span.clone());
            }
            // TODO
            ConditionPattern::IsOk(ref _binding) => {
                unimplemented!();
            }
            ConditionPattern::IsErr(ref _binding) => {
                unimplemented!();
            }
        }

        // Emit the loop body with a jump to the start at the end
        self.emit_stmt(&info.body)?;
        self.state().builder.op(Opcode::Jump(start), span);

        // Emit the loop exit block
        self.state().builder.label(exit);
        self.state().op_pop(1, info.condition.value.span.clone());

        // Emit the loop end block (targeted `break`s)
        self.state().builder.label(end);

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

    fn emit_for_loop(&mut self, info: &For<'a>, span: Span) -> Result<()> {
        /* layout:
          <initializer>
        condition:
          <condition>
          jump if false @end
          pop condition result
          jump @body
        increment:
          <increment>
          jump @condition
        body:
          <body>
          jump @increment
        end:
        */

        self.state().begin_loop();
        // a for loop needs 4 labels
        let [condition, increment, body, end] = self.state().reserve_labels::<4>();
        // for any loop controls, the start is `increment` and the end is `end`
        self.state().add_control_label(&info.label, increment, end);
        // <initializer>
        for init in info.initializers.iter() {
            self.emit_expr(&init.value)?;
            self.state().add_local(&init.name);
        }
        // condition:
        self.state().builder.label(condition);
        if let Some(ref condition) = info.condition {
            // <condition>
            self.emit_expr(condition)?;
            // jump if false @end
            self.state()
                .builder
                .op(Opcode::JumpIfFalse(end), condition.span.clone());
            // pop condition result
            self.state().builder.op(Opcode::Pop, condition.span.clone());
            // jump @body
            self.state()
                .builder
                .op(Opcode::Jump(body), condition.span.clone());
        } else {
            // if no condition is provided, it is implicity `true`. Because of this,
            // instead of emitting `PushTrue, JumpIfFalse(end), Pop, Jump(body)`, emit only `Jump(body)`
            self.state().builder.op(Opcode::Jump(body), span.clone());
        }
        // increment:
        self.state().builder.label(increment);
        if let Some(ref increment) = info.increment {
            // <increment>
            self.emit_expr(increment)?;
            // jump @condition
            self.state()
                .builder
                .op(Opcode::Jump(condition), increment.span.clone());
        }
        // body:
        self.state().builder.label(body);
        // <body>
        self.emit_stmt(&info.body)?;
        // jump @increment
        self.state().builder.op(Opcode::Jump(increment), span);
        // end:
        self.state().builder.label(end);
        self.state().end_loop();
        Ok(())
    }

    fn emit_expr(&mut self, expr: &Expr<'a>) -> Result<()> {
        let span = expr.span.clone();
        match expr.kind {
            ExprKind::Lit(ref literal) => self.emit_lit(literal)?,
            ExprKind::Binary(op, ref a, ref b) => self.emit_binary_expr(op, a, b, span)?,
            ExprKind::Unary(op, ref operand) => self.emit_unary_expr(op, operand, span)?,
            ExprKind::Struct(_) => unimplemented!(),
            ExprKind::Fn(_) => unimplemented!(),
            ExprKind::If(_) => unimplemented!(),
            ExprKind::DoBlock(_) => unimplemented!(),
            ExprKind::Comma(ref exprs) => self.emit_comma_expr(exprs, span)?,
            ExprKind::Call(_) => unimplemented!(),
            ExprKind::Spread(_) => unimplemented!(),
            ExprKind::GetProp(ref get) => {
                self.emit_get_prop(&get.node, &get.field, get.is_optional, span)?
            }
            ExprKind::SetProp(ref set) => {
                self.emit_set_prop(&set.node, &set.field, &set.value, span)?
            }
            ExprKind::GetItem(ref get) => self.emit_get_item(&get.node, &get.key, span)?,
            ExprKind::SetItem(ref set) => {
                self.emit_set_item(&set.node, &set.key, &set.value, span)?
            }
            ExprKind::FString(_) => unimplemented!(),
            ExprKind::Array(_) => unimplemented!(),
            ExprKind::Map(_) => unimplemented!(),
            ExprKind::Variable(ref name) => self.emit_var_expr(name)?,
            // only emitted as part of a for-each loop, where it's manually matched
            ExprKind::Range(..) => unreachable!(),
            ExprKind::PrefixIncDec(ref incdec) => self.emit_incdec_expr(incdec, false, span)?,
            ExprKind::PostfixIncDec(ref incdec) => self.emit_incdec_expr(incdec, true, span)?,
            ExprKind::Assignment(ref a) => self.emit_assign_expr(&a.name, &a.value, span)?,
            ExprKind::Grouping(ref expr) => self.emit_expr(expr)?,
        }

        Ok(())
    }

    fn emit_binary_expr(
        &mut self,
        op: BinOpKind,
        left: &Expr<'a>,
        right: &Expr<'a>,
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

    fn emit_unary_expr(&mut self, op: UnOpKind, operand: &Expr<'a>, span: Span) -> Result<()> {
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

    fn emit_comma_expr(&mut self, exprs: &[Expr<'a>], span: Span) -> Result<()> {
        // a comma expression is guaranteed to have at least 2 sub expressions,
        // so this will never panic due to underflow
        // we want to pop every expr except the last one (which is the result of the expression)
        for i in 0..exprs.len() - 1 {
            self.emit_expr(&exprs[i])?;
        }
        self.state().op_pop((exprs.len() - 1) as u32, span);
        self.emit_expr(exprs.last().unwrap())?;

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

    fn emit_get_prop(
        &mut self,
        node: &Expr<'a>,
        _name: &Token<'a>,
        is_optional: bool,
        span: Span,
    ) -> Result<()> {
        self.emit_expr(node)?;
        // FIXME: stub before heap values are available
        let offset = self.state().builder.constant(Value::None, span.clone())?;
        // TODO: optional access

        self.state().builder.op(
            if is_optional {
                Opcode::TryGetProp(offset)
            } else {
                Opcode::GetProp(offset)
            },
            span,
        );
        Ok(())
    }

    fn emit_set_prop(
        &mut self,
        node: &Expr<'a>,
        _name: &Token<'a>,
        value: &Expr<'a>,
        span: Span,
    ) -> Result<()> {
        self.emit_expr(node)?;
        self.emit_expr(value)?;
        // FIXME: stub before heap values are available
        let offset = self.state().builder.constant(Value::None, span.clone())?;
        self.state().builder.op(Opcode::SetProp(offset), span);
        Ok(())
    }

    fn emit_get_item(&mut self, node: &Expr<'a>, key: &Expr<'a>, span: Span) -> Result<()> {
        self.emit_expr(node)?;
        self.emit_expr(key)?;
        self.state().builder.op(Opcode::GetItem, span);
        Ok(())
    }

    fn emit_set_item(
        &mut self,
        node: &Expr<'a>,
        key: &Expr<'a>,
        value: &Expr<'a>,
        span: Span,
    ) -> Result<()> {
        self.emit_expr(node)?;
        self.emit_expr(key)?;
        self.emit_expr(value)?;
        self.state().builder.op(Opcode::SetItem, span);
        Ok(())
    }

    fn emit_var_expr(&mut self, name: &Token<'_>) -> Result<()> {
        let span = name.span.clone();
        let name = name.lexeme.as_ref();
        if let Some(index) = self.state().resolve_local(name) {
            self.state().builder.op(Opcode::GetLocal(index), span);
            // FIXME: once functions and upvalues are implemented, try to resolve an upvalue before a global
        } else if let Some(index) = self.globals.get(name).copied() {
            self.state().builder.op(Opcode::GetGlobal(index), span);
        } else {
            panic!("Undefined variable '{}'", name);
        }

        Ok(())
    }

    fn emit_assign_expr(&mut self, name: &Token<'a>, value: &Expr<'a>, span: Span) -> Result<()> {
        self.emit_expr(&value)?;
        let set = self.state().resolve_variable_set(name.lexeme.as_ref());
        self.state().builder.op(set, span);
        // we don't pop the right-side expression result, because
        // it's the result of the assignment expression

        Ok(())
    }

    fn emit_incdec_expr(
        &mut self,
        incdec: &IncDec<'a>,
        is_postfix: bool,
        span: Span,
    ) -> Result<()> {
        let add_or_sub_one = match incdec.kind {
            IncDecKind::Increment => Opcode::AddOne,
            IncDecKind::Decrement => Opcode::SubtractOne,
        };
        match &incdec.expr.kind {
            ExprKind::GetProp(ref get) => {
                self.emit_get_prop(&get.node, &get.field, get.is_optional, span.clone())?;
                self.emit_get_prop(&get.node, &get.field, get.is_optional, span.clone())?;
                // FIXME: stub before heap values are available
                self.state().builder.op(add_or_sub_one, span.clone());
                let offset = self.state().builder.constant(Value::None, span.clone())?;
                self.state()
                    .builder
                    .op(Opcode::SetProp(offset), span.clone());
            }
            ExprKind::GetItem(ref get) => {
                self.emit_get_item(&get.node, &get.key, span.clone())?;
                self.emit_expr(&get.key)?;
                self.emit_get_item(&get.node, &get.key, span.clone())?;
                self.state().builder.op(add_or_sub_one, span.clone());
                self.state().builder.op(Opcode::SetItem, span.clone());
            }
            ExprKind::Variable(ref var) => {
                self.emit_var_expr(var)?;
                self.state().builder.op(add_or_sub_one, span.clone());
                let set = self.state().resolve_variable_set(var.lexeme.as_ref());
                self.state().builder.op(set, span.clone());
            }
            _ => unreachable!(),
        }
        if is_postfix {
            match incdec.kind {
                IncDecKind::Increment => self.state().builder.op(Opcode::SubtractOne, span),
                IncDecKind::Decrement => self.state().builder.op(Opcode::AddOne, span),
            };
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

    static CRATE_ROOT: &str = env!("CARGO_MANIFEST_DIR");
    static TESTS_DIR: &str = "tests";
    ves_testing::make_test_macros!(eq => CRATE_ROOT, TESTS_DIR, _impl::compile, _impl::strip_comments);

    test_eq!(t01_simple_arithmetic_expr);
    test_eq!(t02_builtin_type_comparisons);
    test_eq!(t03_struct_type_comparison);
    test_eq!(t04_field_check);
    test_eq!(t05_global_and_local_variables);
    test_eq!(t06_many_local_variables);
    test_eq!(t07_print);
    test_eq!(t08_global_variable_access);
    test_eq!(t09_local_variable_access);
    test_eq!(t10_nested_scope_local_resolution_with_shadowing);
    test_eq!(t11_empty_loop);
    test_eq!(t12_loop_with_body);
    test_eq!(t13_loop_inside_scope);
    test_eq!(t14_continue_in_empty_loop);
    test_eq!(t15_break_in_empty_loop);
    test_eq!(t16_continue_in_loop_with_body);
    test_eq!(t17_break_in_loop_with_body);
    test_eq!(t18_break_and_continue_in_named_loops);
    test_eq!(t19_global_assignment);
    test_eq!(t20_global_compound_assignment);
    test_eq!(t21_local_assignment);
    test_eq!(t22_local_compound_assignment);
    test_eq!(t23_comma_expression);
    test_eq!(t24_get_property);
    test_eq!(t25_get_property_optional);
    test_eq!(t26_set_property);
    test_eq!(t27_get_item);
    test_eq!(t28_set_item);
    test_eq!(t29_nested_get_access);
    // TODO: more optimal codegen for increment/decrement
    test_eq!(t30_prefix_increment);
    test_eq!(t31_postfix_increment);
    // TODO: comment this
    test_eq!(t32_nested_prefix_increment);
    test_eq!(t33_empty_for_loop);
    test_eq!(t34_unlabeled_for_loop);
    test_eq!(t35_unlabeled_while_loop);
    test_eq!(t36_while_loop_with_break_and_continue);
    test_eq!(t37_named_while_loop);

    mod _impl {
        use super::*;
        use ves_error::{FileId, VesFileDatabase};
        use ves_middle::Resolver;
        use ves_parser::{Lexer, Parser};

        pub fn compile(src: String) -> String {
            let mut ast = Parser::new(
                Lexer::new(&src),
                FileId::anon(),
                &VesFileDatabase::default(),
            )
            .parse()
            .unwrap();
            Resolver::new().resolve(&mut ast).unwrap();
            let chunk = Emitter::new(ast).emit().unwrap();
            chunk
                .code
                .iter()
                .enumerate()
                .map(|(i, op)| format!("|{:<04}| {:?}", i, op))
                .collect::<Vec<_>>()
                .join("\n")
        }

        pub fn strip_comments(output: String) -> String {
            output
                .lines()
                .map(|line| {
                    line.split_once("//")
                        .map(|(op, _)| op)
                        .unwrap_or(line)
                        .trim()
                })
                .filter(|line| !line.is_empty())
                .collect::<Vec<_>>()
                .join("\n")
        }
    }
}
