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
    name: Cow<'a, str>,
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

    /// Partially closing a scope means discarding all its locals,
    /// but *without* popping the last `preserve` locals.
    ///
    /// NOTE: it is up to the user to ensure that at least `preserve` locals exist
    fn end_scope_partial(&mut self, scope_span: Span, preserve: usize) {
        // drain all locals from the scope
        self.scope_depth -= 1;
        let mut n_locals = 0;
        for local in self.locals.iter().rev() {
            if local.depth <= self.scope_depth {
                break;
            }
            n_locals += 1;
        }
        self.locals
            .drain(self.locals.len() - n_locals..self.locals.len());
        // but only pop n_locals - preserve
        self.op_pop((n_locals - preserve) as u32, scope_span);
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

    fn add_local<S: Into<Cow<'a, str>>>(&mut self, name: S) -> u32 {
        self.locals.push(Local {
            name: name.into(),
            depth: self.scope_depth,
        });
        (self.locals.len() - 1) as u32
    }

    fn resolve_local(&mut self, name: &str) -> Option<u32> {
        // since local variables can shadow outer scopes,
        // we have to resolve starting from the innermost scope
        for (index, local) in self.locals.iter().enumerate().rev() {
            if local.name == name {
                return Some(index as u32);
            }
        }
        None
    }

    fn resolve_variable_get(&mut self, name: &str) -> Opcode {
        if let Some(index) = self.resolve_local(name) {
            Opcode::GetLocal(index)
            // TODO: once upvalues are a thing, resolve_upvalue before resolving a global
        } else if let Some(index) = self.globals.get(name).copied() {
            Opcode::GetGlobal(index)
        } else {
            panic!("Undefined variable: {}", name)
        }
    }

    fn resolve_variable_set(&mut self, name: &str) -> Opcode {
        if let Some(index) = self.resolve_local(name) {
            Opcode::SetLocal(index)
            // TODO: once upvalues are a thing, resolve_upvalue before resolving a global
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
            self.add_local(name.lexeme.clone());
        }

        Ok(())
    }
}

fn extract_global_slots(globals: &std::collections::HashSet<Global<'_>>) -> HashMap<String, u32> {
    let mut globals = globals.iter().collect::<Vec<_>>();
    globals.sort();
    globals
        .into_iter()
        .enumerate()
        .map(|(idx, global)| (global.name.lexeme.clone().into_owned(), idx as u32))
        .collect()
}

pub struct Emitter<'a> {
    states: Vec<State<'a>>,
    ast: AST<'a>,
}

impl<'a> Emitter<'a> {
    pub fn new(ast: AST<'a>) -> Emitter<'a> {
        let globals = Rc::new(extract_global_slots(&ast.globals));
        Emitter {
            states: vec![State::new(ast.file_id, globals)],
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
            ForEach(ref info) => self.emit_foreach_loop(info, span)?,
            While(ref info) => self.emit_while_loop(info, span)?,
            Block(ref body) => self.emit_block(body, span)?,
            Print(ref expr) => self.emit_print_stmt(expr)?,
            Return(ref expr) => self.emit_return_stmt(expr.as_deref(), span)?,
            Break(label) => self.emit_loop_control(label, LoopControl::Break, span)?,
            Continue(label) => self.emit_loop_control(label, LoopControl::Continue, span)?,
            Defer(ref expr) => self.emit_defer_stmt(expr, span)?,
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

    fn emit_return_stmt(&mut self, value: Option<&Expr<'a>>, span: Span) -> Result<()> {
        let n_locals = self.state().locals.len() as u32;
        self.state().op_pop(n_locals, span.clone());
        if let Some(value) = value {
            self.emit_expr(value)?;
        } else {
            self.state().builder.op(Opcode::PushNone, span.clone());
        }
        self.state().builder.op(Opcode::Return, span);
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
        let [start, end] = self.state().reserve_labels::<2>();
        self.state().add_control_label(&info.label, start, end);
        self.state().builder.label(start);
        self.emit_stmt(&info.body)?;
        self.state().builder.op(Opcode::Jump(start), span);
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
    /// ```
    /// TODO: describe the layout for the loops with a binding
    fn emit_while_loop(&mut self, info: &While<'a>, span: Span) -> Result<()> {
        self.state().begin_loop();
        let [start, exit, end] = self.state().reserve_labels::<3>();
        self.state().add_control_label(&info.label, start, end);
        self.state().builder.label(start);
        match &info.condition.pattern {
            ConditionPattern::Value => {
                self.emit_expr(&info.condition.value)?;
            }
            ConditionPattern::IsOk(ref binding) => {
                self.state()
                    .builder
                    .op(Opcode::PushNone, binding.span.clone());
                let slot = self.state().add_local(binding.lexeme.clone());
                self.state()
                    .builder
                    .op(Opcode::UnwrapOk(slot), binding.span.clone());
            }
            ConditionPattern::IsErr(ref binding) => {
                self.state()
                    .builder
                    .op(Opcode::PushNone, binding.span.clone());
                let slot = self.state().add_local(binding.lexeme.clone());
                self.state()
                    .builder
                    .op(Opcode::UnwrapErr(slot), binding.span.clone());
            }
        }
        self.state()
            .builder
            .op(Opcode::JumpIfFalse(exit), span.clone());
        self.state().builder.op(Opcode::Pop, span.clone());
        self.emit_stmt(&info.body)?;
        self.state().builder.op(Opcode::Jump(start), span);
        self.state().builder.label(exit);
        self.state().op_pop(1, info.condition.value.span.clone());
        self.state().builder.label(end);
        self.state().end_loop();
        Ok(())
    }

    /// Emits the bytecode for a For-Each loop.
    ///
    /// For-Each loops are desugared into regular For loops, so the layout is the same.
    ///
    /// The format is: `for ITEM in ITERATOR`, where ITEM is an identifier and ITERATOR
    /// is either a range (`START..END`/`START..=END`) or an expression whose value
    /// is conformant with the iterator protocol.
    ///
    /// The iterator protocol has 3 parts: `@iter`, `@next`, `@done`.
    /// - `@iter` is should return a value which has the `@next` and `@done` methods
    /// - `@next` is should return the next value, or none if there are no more values
    /// - `@done` is should return `true` if there are no more values, and `false` otherwise
    fn emit_foreach_loop(&mut self, info: &ForEach<'a>, span: Span) -> Result<()> {
        self.state().begin_scope();
        let mut comparison_op = Opcode::LessThan;
        match info.iterator {
            IteratorKind::Range(Range {
                ref start,
                ref end,
                ref step,
                inclusive,
            }) => {
                if inclusive {
                    comparison_op = Opcode::LessEqual
                };
                // emit item initializer (e.g. the `i` from `for i in 0..10, 2 { ... }`)
                // this is equivalent to `for i = 0, ...`
                self.state().add_local(info.variable.lexeme.clone());
                self.emit_expr(start)?;

                // the [[END]] and [[STEP]] initializers are given names which
                // are not valid identifiers, so there is no way to access them
                // from within the loop body

                // emit [[END]] initializer (the `10` from `for i in 0..10, 2 { ... }`)
                self.state().add_local("[[END]]");
                self.emit_expr(end)?;
                // emit [[STEP]] initializer (the `2` from `for i in 0..10, 2 { ... }`)
                self.state().add_local("[[STEP]]");
                self.emit_expr(step)?;
            }
            IteratorKind::Expr(ref iterable) => {
                let iter_local = self.state().add_local("[[ITER]]");
                self.emit_expr(iterable)?;
                // FIXME: stub for heap-value
                // this should be a string constant for accessing "iter"
                let iter = self.state().builder.constant(Value::None, span.clone())?;
                // QQQ(moscow): should this be `GetProp` or a special opcode for fetching builtins?
                self.state().builder.op(Opcode::GetProp(iter), span.clone());
                self.state().builder.op(Opcode::Call(0), span.clone());

                // now emit `<item>`
                self.state().add_local(info.variable.lexeme.clone());
                // and initialize it with `[[ITER]].next()`
                self.state()
                    .builder
                    .op(Opcode::GetLocal(iter_local), span.clone());
                // FIXME: stub for heap-value
                // this should be a string constant for accessing "next"
                let next = self.state().builder.constant(Value::None, span.clone())?;
                self.state().builder.op(Opcode::GetProp(next), span.clone());
                self.state().builder.op(Opcode::Call(0), span.clone());
            }
        }
        self.state().begin_loop();
        let [start, latch, body, exit, end] = self.state().reserve_labels::<5>();
        self.state().add_control_label(&info.label, latch, end);
        self.state().builder.label(start);
        match info.iterator {
            IteratorKind::Range(..) => {
                // emit `info.variable < [[END]]` or `info.variable <= [[END]]`
                // these locals are guaranteed to exist, because we create them above
                let start_local = self
                    .state()
                    .resolve_local(info.variable.lexeme.as_ref())
                    .unwrap();
                let end_local = self.state().resolve_local("[[END]]").unwrap();
                self.state()
                    .builder
                    .op(Opcode::GetLocal(start_local), span.clone());
                self.state()
                    .builder
                    .op(Opcode::GetLocal(end_local), span.clone());
                self.state().builder.op(comparison_op, span.clone());
                self.state()
                    .builder
                    .op(Opcode::JumpIfFalse(exit), span.clone());
                self.state().builder.op(Opcode::Pop, span.clone());
                self.state().builder.op(Opcode::Jump(body), span.clone());
            }
            IteratorKind::Expr(..) => {
                // emit `![[ITER]].done()`
                let iter_local = self.state().resolve_local("[[ITER]]").unwrap();
                self.state()
                    .builder
                    .op(Opcode::GetLocal(iter_local), span.clone());
                // FIXME: stub for heap-value
                // this should be a string constant for accessing "done"
                let done = self.state().builder.constant(Value::None, span.clone())?;
                self.state().builder.op(Opcode::GetProp(done), span.clone());
                self.state().builder.op(Opcode::Call(0), span.clone());
                self.state().builder.op(Opcode::Not, span.clone());
                self.state()
                    .builder
                    .op(Opcode::JumpIfFalse(exit), span.clone());
                self.state().builder.op(Opcode::Pop, span.clone());
                self.state().builder.op(Opcode::Jump(body), span.clone());
            }
        }
        self.state().builder.label(latch);
        match info.iterator {
            IteratorKind::Range(..) => {
                // emit `info.variable += [[STEP]]`
                let start_local = self
                    .state()
                    .resolve_local(info.variable.lexeme.as_ref())
                    .unwrap();
                let step_local = self.state().resolve_local("[[STEP]]").unwrap();
                self.state()
                    .builder
                    .op(Opcode::GetLocal(start_local), span.clone());
                self.state()
                    .builder
                    .op(Opcode::GetLocal(step_local), span.clone());
                self.state().builder.op(Opcode::Add, span.clone());
                self.state()
                    .builder
                    .op(Opcode::SetLocal(start_local), span.clone());
                self.state().op_pop(1, span.clone());
                self.state().builder.op(Opcode::Jump(start), span.clone());
            }
            IteratorKind::Expr(..) => {
                // emit `<item> = [[ITER]].next()`
                let iter_local = self.state().resolve_local("[[ITER]]").unwrap();
                self.state()
                    .builder
                    .op(Opcode::GetLocal(iter_local), span.clone());
                // FIXME: stub for heap-value
                // this should be a string constant for accessing "next"
                let next = self.state().builder.constant(Value::None, span.clone())?;
                self.state().builder.op(Opcode::GetProp(next), span.clone());
                self.state().builder.op(Opcode::Call(0), span.clone());
                let item_local = self
                    .state()
                    .resolve_local(info.variable.lexeme.as_ref())
                    .unwrap();
                self.state()
                    .builder
                    .op(Opcode::SetLocal(item_local), span.clone());
                self.state().op_pop(1, span.clone());
                self.state().builder.op(Opcode::Jump(start), span.clone());
            }
        }
        self.state().builder.label(body);
        self.emit_stmt(&info.body)?;
        self.state().builder.op(Opcode::Jump(latch), span.clone());
        self.state().builder.label(exit);
        self.state().op_pop(1, span.clone());
        self.state().builder.label(end);
        self.state().end_loop();
        self.state().end_scope(span);

        Ok(())
    }

    /// Emits the bytecode for a for loop.
    ///
    /// # Layout
    /// The basic layout of this loop looks like this:
    /// ```x86asm
    /// pre_start:
    ///     <initializer>
    /// start:
    ///     <condition>
    ///     jump_if_false @exit
    ///     pop condition result
    ///     jump @body
    /// latch:
    ///     <increment>
    ///     jump @start
    /// body:
    ///     <body>
    ///     jump @latch
    /// exit:
    ///     pop condition result
    /// end:
    /// ```
    ///
    /// If `break` or `continue` is used, they target the latch or exit label, respectively.
    /// Note that both statements must pop off the locals within the loop scope before jumping (not shown here).
    /// ```x86asm
    /// pre_start:
    ///     <initializer>
    /// start:
    ///     <condition>
    ///     jump_if_false @exit
    ///     pop condition result
    ///     jump @body
    /// latch:
    ///     <increment>
    ///     jump @start
    /// body:
    ///     <body>
    ///     jump @end     ; user-supplied break
    ///     jump @latch   ; user-supplied continue
    ///     jump @latch   ; default loop jump
    /// exit:
    ///     pop condition result
    /// end:
    /// ```
    /// TODO: describe the layout for the loops with a binding
    fn emit_for_loop(&mut self, info: &For<'a>, span: Span) -> Result<()> {
        self.state().begin_scope();
        for init in info.initializers.iter() {
            self.emit_expr(&init.value)?;
            self.state().add_local(init.name.lexeme.clone());
        }
        self.state().begin_loop();
        let [start, latch, body, exit, end] = self.state().reserve_labels::<5>();
        // Break and continue target the `latch` and `exit` labels
        self.state().add_control_label(&info.label, latch, end);
        self.state().builder.label(start);
        if let Some(ref condition) = info.condition {
            self.emit_expr(condition)?;
            self.state()
                .builder
                .op(Opcode::JumpIfFalse(exit), condition.span.clone());
            self.state().builder.op(Opcode::Pop, condition.span.clone());
            self.state()
                .builder
                .op(Opcode::Jump(body), condition.span.clone());
        } else {
            // if no condition is provided, it is implicitly `true`.
            // Instead of emitting an analog of a `while true` loop, we jump directly into the loop body.
            self.state().builder.op(Opcode::Jump(body), span.clone());
        }
        self.state().builder.label(latch);
        if let Some(ref increment) = info.increment {
            self.emit_expr(increment)?;
            self.state().op_pop(1, increment.span.clone());
            self.state()
                .builder
                .op(Opcode::Jump(start), increment.span.clone());
        }
        self.state().builder.label(body);
        self.emit_stmt(&info.body)?;
        self.state().builder.op(Opcode::Jump(latch), span.clone());
        self.state().builder.label(exit);
        if info.condition.is_some() {
            self.state().op_pop(1, span.clone());
        }
        self.state().builder.label(end);
        self.state().end_loop();
        self.state().end_scope(span);

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

    fn emit_defer_stmt(&mut self, call: &Call<'a>, span: Span) -> Result<()> {
        self.emit_expr(&call.callee)?;
        for arg in call.args.iter() {
            self.emit_expr(arg)?;
        }
        self.state().builder.op(Opcode::Defer, span);
        Ok(())
    }

    fn emit_expr(&mut self, expr: &Expr<'a>) -> Result<()> {
        let span = expr.span.clone();
        match expr.kind {
            ExprKind::Lit(ref literal) => self.emit_lit(literal)?,
            ExprKind::Binary(op, ref a, ref b) => self.emit_binary_expr(op, a, b, span)?,
            ExprKind::Unary(op, ref operand) => self.emit_unary_expr(op, operand, span)?,
            // TODO
            ExprKind::Struct(_) => unimplemented!(),
            ExprKind::Fn(_) => unimplemented!(),
            ExprKind::If(ref info) => self.emit_if_expr(info, span, None)?,
            ExprKind::DoBlock(ref block) => self.emit_do_block_expr(block, span)?,
            ExprKind::Comma(ref exprs) => self.emit_comma_expr(exprs, span)?,
            ExprKind::Call(ref call) => self.emit_call_expr(call, span)?,
            ExprKind::Spread(ref expr) => {
                self.emit_expr(expr)?;
                self.state().builder.op(Opcode::Spread, span);
            }
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
            ExprKind::FString(ref fstr) => self.emit_fstring(fstr, span)?,
            ExprKind::Array(ref exprs) => self.emit_array_lit(exprs, span)?,
            ExprKind::Map(ref entries) => self.emit_map_lit(entries, span)?,
            ExprKind::Variable(ref name) => self.emit_var_expr(name)?,
            ExprKind::PrefixIncDec(ref incdec) => self.emit_incdec_expr(incdec, false, span)?,
            ExprKind::PostfixIncDec(ref incdec) => self.emit_incdec_expr(incdec, true, span)?,
            ExprKind::Assignment(ref a) => {
                self.emit_assign_expr(a.name.lexeme.as_ref(), &a.value, span)?
            }
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

    ///
    ///
    /// # Layout
    /// ```x86asm
    ///   <condition>
    ///   jump_if_false @other
    ///   pop result of condition
    ///   <then branch>
    ///   jump @end
    /// other:
    ///   pop result of condition
    ///   <else branch>
    /// end:
    /// ```
    /// With else if branch:
    /// ```x86asm
    ///   <condition>
    ///   jump_if_false @other0
    ///   pop result of condition
    ///   <then0 branch>
    ///   jump @end
    /// other0:
    ///   pop result of condition
    ///   <condition>
    ///   jump_if_false @other1
    ///   pop result of condition
    ///   <then1 branch>
    ///   jump @end
    /// other1:
    ///   pop result of condition
    /// end:
    /// ```
    fn emit_if_expr(&mut self, info: &If<'a>, span: Span, end_label: Option<u32>) -> Result<()> {
        // reserve only a single `end` label, which is used as the exit point for all branches
        let [other, end] = if let Some(end_label) = end_label {
            [self.state().reserve_label(), end_label]
        } else {
            self.state().reserve_labels::<2>()
        };
        match info.condition.pattern {
            ConditionPattern::Value => {
                self.emit_expr(&info.condition.value)?;
            }
            ConditionPattern::IsOk(ref binding) => {
                self.state()
                    .builder
                    .op(Opcode::PushNone, binding.span.clone());
                let slot = self.state().add_local(binding.lexeme.clone());
                self.state()
                    .builder
                    .op(Opcode::UnwrapOk(slot), binding.span.clone());
            }
            ConditionPattern::IsErr(ref binding) => {
                self.state()
                    .builder
                    .op(Opcode::PushNone, binding.span.clone());
                let slot = self.state().add_local(binding.lexeme.clone());
                self.state()
                    .builder
                    .op(Opcode::UnwrapErr(slot), binding.span.clone());
            }
        }
        self.state()
            .builder
            .op(Opcode::JumpIfFalse(other), span.clone());
        self.state().builder.op(Opcode::Pop, span.clone());
        for stmt in info.then.statements.iter() {
            self.emit_stmt(stmt)?;
        }
        if let Some(ref value) = info.then.value {
            self.emit_expr(value)?;
        } else {
            self.state().builder.op(Opcode::PushNone, span.clone());
        }
        self.state().builder.op(Opcode::Jump(end), span.clone());
        self.state().builder.label(other);
        self.state().builder.op(Opcode::Pop, span.clone());
        if let Some(ref otherwise) = info.otherwise {
            match otherwise {
                Else::If(ref nested) => self.emit_if_expr(nested, span, Some(end))?,
                Else::Bare(ref block) => self.emit_do_block_expr(block, span)?,
            }
        }
        // only emit the end label once, from the initial call to emit_if_expr
        if end_label.is_none() {
            self.state().builder.label(end);
        }
        Ok(())
    }

    /// Emit a `do { }` expression
    ///
    /// Do block expressions evaluate to the last statement in the block, but only if it is
    /// an expression statement, and that statement is not terminated by a semicolon.
    ///
    /// At the start of the block, we push a hidden local variable `[[VALUE]]`, whose value will be set
    /// to the value of the entire do block. It is normally drained from the locals array, but it's value
    /// is *not* popped from the stack.
    fn emit_do_block_expr(&mut self, do_block: &DoBlock<'a>, span: Span) -> Result<()> {
        self.state().begin_scope();
        let value_slot = self.state().add_local("[[VALUE]]");
        self.state().builder.op(Opcode::PushNone, span.clone());

        for stmt in do_block.statements.iter() {
            self.emit_stmt(stmt)?;
        }
        if let Some(ref value) = do_block.value {
            self.emit_expr(value)?;
            self.state()
                .builder
                .op(Opcode::SetLocal(value_slot), span.clone());
        }
        // preserve one local value on the stack
        self.state().end_scope_partial(span, 1);
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

    fn emit_call_expr(&mut self, call: &Call<'a>, span: Span) -> Result<()> {
        self.emit_expr(&call.callee)?;
        for expr in call.args.iter() {
            self.emit_expr(expr)?;
        }
        self.state()
            .builder
            .op(Opcode::Call(call.args.len() as u32), span);
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

    fn emit_fstring(&mut self, fstr: &FString<'a>, span: Span) -> Result<()> {
        for frag in fstr.fragments.iter() {
            match frag {
                FStringFrag::Str(ref lit) => self.emit_lit(lit)?,
                FStringFrag::Expr(ref expr) => self.emit_expr(expr)?,
            }
        }
        self.state()
            .builder
            .op(Opcode::Interpolate(fstr.fragments.len() as u32), span);
        Ok(())
    }

    fn emit_array_lit(&mut self, exprs: &[Expr<'a>], span: Span) -> Result<()> {
        for expr in exprs {
            self.emit_expr(expr)?;
        }
        self.state()
            .builder
            .op(Opcode::CreateArray(exprs.len() as u32), span);
        Ok(())
    }

    fn emit_map_lit(&mut self, entries: &[MapEntry<'a>], span: Span) -> Result<()> {
        self.state()
            .builder
            .op(Opcode::CreateEmptyMap, span.clone());
        for entry in entries {
            match entry {
                MapEntry::Pair(ref key, ref value) => {
                    self.emit_expr(key)?;
                    self.emit_expr(value)?;
                    self.state().builder.op(Opcode::MapInsert, span.clone());
                }
                MapEntry::Spread(ref expr) => {
                    self.emit_expr(expr)?;
                    self.state().builder.op(Opcode::MapExtend, span.clone());
                }
            }
        }
        Ok(())
    }

    fn emit_var_expr(&mut self, name: &Token<'_>) -> Result<()> {
        let get = self.state().resolve_variable_get(name.lexeme.as_ref());
        self.state().builder.op(get, name.span.clone());

        Ok(())
    }

    fn emit_assign_expr(&mut self, name: &str, value: &Expr<'a>, span: Span) -> Result<()> {
        self.emit_expr(&value)?;
        let set = self.state().resolve_variable_set(name);
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
    test_eq!(t38_loop_for_with_break_and_continue);
    test_eq!(t39_unlabeled_foreach_loop);
    test_eq!(t40_labeled_foreach_with_control);
    test_eq!(t41_multiple_global_vars);
    test_eq!(t42_empty_do_block_expr);
    test_eq!(t43_do_block_expr_with_value);
    test_eq!(t44_simple_if_expr);
    test_eq!(t45_nested_if_expr);
    test_eq!(t46_call_expr);
    test_eq!(t47_string_interpolation);
    test_eq!(t48_array_literal);
    test_eq!(t49_map_literal);
    test_eq!(t50_defer_stmt);
    test_eq!(t51_return_stmt);
    test_eq!(t52_foreach_iterable);
    test_eq!(t53_condition_patterns);

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
