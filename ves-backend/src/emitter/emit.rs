use std::{borrow::Cow, collections::HashMap, rc::Rc};

use crate::{
    gc::{GcObj, VesGc},
    objects::{
        ves_fn::{ClosureDescriptor, VesFn},
        ves_int::VesInt,
        ves_str::view::VesStrView,
    },
    Span, Value, VesObject,
};

use super::opcode::Opcode;
use super::Result;
use super::{
    builder::{BytecodeBuilder, Chunk},
    CompilationContext,
};
use ves_error::FileId;
use ves_parser::ast::*;
use ves_parser::lexer::{Token, TokenKind};

struct Local<'a> {
    name: Cow<'a, str>,
    depth: usize,
}

/// An upvalue stores the index of a value which should be captured
/// into a closure.
///
/// The index may refer to two different places:
/// 1. An enclosing function's stack slot
/// 2. An enclosing function's upvalue index
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum UpvalueInfo {
    /// Upvalue brought in from the enclosing function's locals
    Local(u32),
    /// Upvalue brought in from the enclosing function's upvalues
    Upvalue(u32),
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
    enclosing: Option<Box<State<'a>>>,
    fn_kind: Option<FnKind>,
    builder: BytecodeBuilder,
    locals: Vec<Local<'a>>,
    upvalues: Vec<UpvalueInfo>,
    globals: Rc<HashMap<String, u32>>,
    scope_depth: usize,
    struct_name: Option<Cow<'a, str>>,

    // The id of the next label
    label_id: u32,
    /// Reserved label IDs
    labels: Vec<u32>,
    /// The label used for loop jumps
    control_labels: HashMap<Cow<'a, str>, ControlLabel>,
}

impl<'a> State<'a> {
    fn new(
        enclosing: Option<Box<State<'a>>>,
        file_id: FileId,
        globals: Rc<HashMap<String, u32>>,
    ) -> Self {
        State {
            enclosing,
            builder: BytecodeBuilder::new(file_id),
            fn_kind: None,
            locals: vec![],
            upvalues: vec![],
            control_labels: HashMap::new(),
            labels: Vec::new(),
            globals,
            scope_depth: 0,
            label_id: 0,
            struct_name: None,
        }
    }

    fn finish(&mut self) -> Chunk {
        self.builder.finish(std::mem::take(&mut self.labels))
    }

    fn begin_scope(&mut self) -> usize {
        self.scope_depth += 1;
        self.scope_depth
    }

    fn end_scope(&mut self, scope_span: Span) -> u32 {
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
        n_locals as u32
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

    fn begin_struct<S: Into<Cow<'a, str>>>(&mut self, name: S) {
        self.struct_name = Some(name.into());
    }

    fn end_struct(&mut self) {
        self.struct_name = None;
    }

    fn resolve_struct_name(&self) -> Option<Cow<'a, str>> {
        let mut current = Some(self);
        while let Some(state) = current {
            if let Some(ref name) = state.struct_name {
                return Some(name.clone());
            } else {
                current = self.enclosing.as_deref()
            }
        }
        None
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

    fn resolve_label(&self, name: &Token<'a>) -> Option<&ControlLabel> {
        self.control_labels.get(&name.lexeme)
    }

    fn count_locals_in_scope(&self, outer_scope_depth: usize) -> u32 {
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

    fn resolve_local(&self, name: &str) -> Option<u32> {
        // since local variables can shadow outer scopes,
        // we have to resolve starting from the innermost scope
        for (index, local) in self.locals.iter().enumerate().rev() {
            if local.name == name {
                return Some(index as u32);
            }
        }
        None
    }

    fn add_upvalue(&mut self, upvalue: UpvalueInfo) -> u32 {
        println!("{:?}", upvalue);
        // don't duplicate upvalues
        for (index, existing) in self.upvalues.iter().enumerate() {
            if existing == &upvalue {
                return index as u32;
            }
        }
        self.upvalues.push(upvalue);
        (self.upvalues.len() - 1) as u32
    }

    /// Try to resolve an upvalue from the locals in the enclosing scope,
    /// or the upvalues of an enclosing function.
    fn resolve_upvalue(&mut self, name: &str) -> Option<u32> {
        if let Some(enclosing) = &mut self.enclosing {
            // try to resolve the upvalue as a local from the enclosing scope
            // and if that fails, recurse
            if let Some(index) = enclosing.resolve_local(name) {
                // When the closure is created, this upvalue will be created from a local variable
                // in the enclosing scope

                Some(self.add_upvalue(UpvalueInfo::Local(index)))
            } else {
                enclosing
                    .resolve_upvalue(name)
                    // this upvalue will be created from an upvalue in the enclosing closure
                    // FIXME: panics if there are more than u16::MAX upvalues
                    .map(|index| self.add_upvalue(UpvalueInfo::Upvalue(index)))
            }
        } else {
            None
        }
    }

    fn resolve_variable_get(&mut self, name: &str) -> Opcode {
        if let Some(index) = self.resolve_local(name) {
            Opcode::GetLocal(index)
        } else if let Some(index) = self.resolve_upvalue(name) {
            Opcode::GetUpvalue(index)
        } else if let Some(index) = self.globals.get(name).copied() {
            Opcode::GetGlobal(index)
        } else {
            panic!("Undefined variable: {}", name)
        }
    }

    fn resolve_variable_set(&mut self, name: &str) -> Opcode {
        if let Some(index) = self.resolve_local(name) {
            Opcode::SetLocal(index)
        } else if let Some(index) = self.resolve_upvalue(name) {
            Opcode::SetUpvalue(index)
        } else if let Some(index) = self.globals.get(name).copied() {
            Opcode::SetGlobal(index)
        } else {
            panic!("Undefined variable: {}", name)
        }
    }

    fn define<S: Into<Cow<'a, str>>>(&mut self, name: S, span: Span) -> Result<()> {
        let name = name.into();
        if self.scope_depth == 0 {
            let index = self
                .globals
                .get(&name[..])
                .copied()
                .ok_or_else(|| {
                    format!(
                        /* This shouldn't ever happen since we collect and check all globals */
                        "Attempted to define the variable `{}` as a global variable",
                        name
                    )
                })
                .unwrap();
            self.builder.op(Opcode::SetGlobal(index), span.clone());
            self.op_pop(1, span);
        } else {
            self.add_local(name);
        }

        Ok(())
    }

    fn define_no_pop<S: Into<Cow<'a, str>>>(&mut self, name: S, span: Span) -> Result<()> {
        let name = name.into();
        if self.scope_depth == 0 {
            let index = self
                .globals
                .get(&name[..])
                .copied()
                .ok_or_else(|| {
                    format!(
                        /* This shouldn't ever happen since we collect and check all globals */
                        "Attempted to define the variable `{}` as a global variable",
                        name
                    )
                })
                .unwrap();
            self.builder.op(Opcode::SetGlobal(index), span);
        } else {
            self.add_local(name);
        }

        Ok(())
    }
}

fn extract_global_slots(globals: &std::collections::HashSet<Global<'_>>) -> HashMap<String, u32> {
    globals
        .iter()
        .map(|global| {
            (
                global.name.lexeme.clone().into_owned(),
                global.index.unwrap() as u32,
            )
        })
        .collect()
}

pub struct Emitter<'a, 'b, T: VesGc> {
    state: State<'a>,
    ast: &'b AST<'a>,
    ctx: CompilationContext<'a, 'b, T>,
}

impl<'a, 'b, T: VesGc> Emitter<'a, 'b, T> {
    pub fn new(ast: &'b AST<'a>, ctx: CompilationContext<'a, 'b, T>) -> Self {
        let globals = Rc::new(extract_global_slots(&ast.globals));
        Emitter {
            state: State::new(None, ast.file_id, globals),
            ast,
            ctx,
        }
    }

    fn begin_state(&mut self) {
        let new = State::new(
            None,
            self.state.builder.file_id(),
            self.state.globals.clone(),
        );
        let enclosing = std::mem::replace(&mut self.state, new);
        self.state.enclosing = Some(Box::new(enclosing));
    }

    fn end_state(&mut self) -> Chunk {
        if let Some(enclosing) = self.state.enclosing.take() {
            std::mem::replace(&mut self.state, *enclosing).finish()
        } else {
            panic!("called end_state without a preceding begin_state")
        }
    }

    pub fn emit(mut self) -> Result<GcObj> {
        for stmt in self.ast.body.iter() {
            self.emit_stmt(stmt)?;
        }
        self.state.builder.op(Opcode::Return, 0..0);

        let f = VesFn {
            name: VesStrView::new(self.ctx.alloc_or_intern("<main>")), // TODO: use module name
            positionals: 0,
            defaults: 0,
            rest: false,
            chunk: self.state.finish(),
            file_id: self.ast.file_id,
            is_magic_method: false,
        };
        let ptr = self.ctx.gc.alloc_permanent(VesObject::Fn(f));
        Ok(ptr)
    }

    fn emit_stmt(&mut self, stmt: &'b Stmt<'a>) -> Result<()> {
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
            _Empty => (),
        }

        Ok(())
    }

    fn emit_expr_stmt(&mut self, expr: &'b Expr<'a>, span: Span) -> Result<()> {
        self.emit_expr(expr, false)?;
        self.state.builder.op(Opcode::Pop, span);
        Ok(())
    }

    fn emit_var_stmt(&mut self, vars: &'b [Var<'a>]) -> Result<()> {
        for var in vars {
            let span = var.name.span.clone();
            if let Some(ref initializer) = var.initializer {
                self.emit_expr(initializer, true)?;
            } else {
                self.state.builder.op(Opcode::PushNone, span);
            }
            self.state
                .define(var.name.lexeme.clone(), var.name.span.clone())?;
        }
        Ok(())
    }

    fn emit_print_stmt(&mut self, expr: &'b Expr<'a>) -> Result<()> {
        let span = expr.span.clone();
        match &expr.kind {
            ExprKind::Comma(ref exprs) => {
                for expr in exprs {
                    self.emit_expr(expr, true)?;
                }
                self.state
                    .builder
                    .op(Opcode::PrintN(exprs.len() as u32), span);
            }
            _ => {
                self.emit_expr(expr, true)?;
                self.state.builder.op(Opcode::Print, span);
            }
        }
        Ok(())
    }

    fn emit_return_stmt(&mut self, value: Option<&'b Expr<'a>>, span: Span) -> Result<()> {
        let n_locals = self.state.locals.len() as u32;
        self.state.op_pop(n_locals, span.clone());
        if let Some(value) = value {
            self.emit_expr(value, true)?;
        } else if self.state.fn_kind == Some(FnKind::Initializer) {
            // in case we're in an initializer, an early return should yield `self`
            let self_index = self.state.resolve_local("self").unwrap();
            self.state
                .builder
                .op(Opcode::GetLocal(self_index), span.clone());
        } else {
            self.state.builder.op(Opcode::PushNone, span.clone());
        }
        self.state.builder.op(Opcode::Return, span);
        Ok(())
    }

    fn emit_loop_control(
        &mut self,
        label: &Token<'a>,
        kind: LoopControl,
        span: Span,
    ) -> Result<()> {
        let control_label = self.state.resolve_label(label).unwrap();
        let scope_depth = control_label.depth;
        // `break` jumps to the end of the loop, `continue` jumps to the start
        let label_id = if kind == LoopControl::Break {
            control_label.end
        } else {
            control_label.start
        };
        // Locals from the loop's inner scopes have to be popped off the stack
        let n_locals = self.state.count_locals_in_scope(scope_depth);
        self.state.op_pop(n_locals, span);
        self.state
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
    fn emit_loop(&mut self, info: &'b Loop<'a>, span: Span) -> Result<()> {
        self.state.begin_loop();
        let [start, end] = self.state.reserve_labels();
        self.state.add_control_label(&info.label, start, end);
        self.state.builder.label(start);
        self.emit_stmt(&info.body)?;
        self.state.builder.op(Opcode::Jump(start), span);
        self.state.builder.label(end);
        self.state.end_loop();
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
    fn emit_while_loop(&mut self, info: &'b While<'a>, span: Span) -> Result<()> {
        self.state.begin_loop();
        let [start, exit, end] = self.state.reserve_labels();
        self.state.add_control_label(&info.label, start, end);
        self.state.builder.label(start);
        // TODO: while loops are also wrong (in the same way as if expr)
        self.state.begin_scope();
        let mut used_pattern = false;
        match &info.condition.pattern {
            ConditionPattern::Value => {
                self.emit_expr(&info.condition.value, true)?;
            }
            ConditionPattern::IsOk(ref binding) => {
                used_pattern = true;
                let slot = self.state.add_local(binding.lexeme.clone());
                self.state
                    .builder
                    .op(Opcode::PushNone, binding.span.clone());
                self.emit_expr(&info.condition.value, true)?;
                self.state
                    .builder
                    .op(Opcode::UnwrapOk(slot), binding.span.clone());
            }
            ConditionPattern::IsErr(ref binding) => {
                used_pattern = true;
                let slot = self.state.add_local(binding.lexeme.clone());
                self.state
                    .builder
                    .op(Opcode::PushNone, binding.span.clone());
                self.emit_expr(&info.condition.value, true)?;
                self.state
                    .builder
                    .op(Opcode::UnwrapErr(slot), binding.span.clone());
            }
        }
        self.state
            .builder
            .op(Opcode::JumpIfFalse(exit), span.clone());
        self.state.builder.op(Opcode::Pop, span.clone());
        self.emit_stmt(&info.body)?;
        self.state.end_scope(span.clone());
        self.state.builder.op(Opcode::Jump(start), span);
        self.state.builder.label(exit);
        self.state.op_pop(1, info.condition.value.span.clone());
        if used_pattern {
            self.state.op_pop(1, info.condition.value.span.clone());
        }
        self.state.builder.label(end);
        self.state.end_loop();
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
    fn emit_foreach_loop(&mut self, info: &'b ForEach<'a>, span: Span) -> Result<()> {
        self.state.begin_scope();
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
                self.state.add_local(info.variable.lexeme.clone());
                self.emit_expr(start, true)?;

                // the [[END]] and [[STEP]] initializers are given names which
                // are not valid identifiers, so there is no way to access them
                // from within the loop body

                // emit [[END]] initializer (the `10` from `for i in 0..10, 2 { ... }`)
                self.state.add_local("[[END]]");
                self.emit_expr(end, true)?;
                // emit [[STEP]] initializer (the `2` from `for i in 0..10, 2 { ... }`)
                self.state.add_local("[[STEP]]");
                self.emit_expr(step, true)?;
            }
            IteratorKind::Expr(ref iterable) => {
                let iter_local = self.state.add_local("[[ITER]]");
                self.emit_expr(iterable, true)?;
                let iter = self
                    .state
                    .builder
                    .constant(self.ctx.alloc_or_intern("iter").into(), span.clone())?;
                self.state.builder.get_magic(iter, span.clone());
                self.state.builder.op(Opcode::Call(0), span.clone());

                // now emit `<item>`
                self.state.add_local(info.variable.lexeme.clone());
                // and initialize it with `[[ITER]].next()`
                self.state
                    .builder
                    .op(Opcode::GetLocal(iter_local), span.clone());
                let next = self
                    .state
                    .builder
                    .constant(self.ctx.alloc_or_intern("next").into(), span.clone())?;
                self.state.builder.get_magic(next, span.clone());
                self.state.builder.op(Opcode::Call(0), span.clone());
            }
        }
        self.state.begin_loop();
        let [start, latch, body, exit, end] = self.state.reserve_labels();
        self.state.add_control_label(&info.label, latch, end);
        self.state.builder.label(start);
        match info.iterator {
            IteratorKind::Range(..) => {
                // emit `info.variable < [[END]]` or `info.variable <= [[END]]`
                // these locals are guaranteed to exist, because we create them above
                let start_local = self
                    .state
                    .resolve_local(info.variable.lexeme.as_ref())
                    .unwrap();
                let end_local = self.state.resolve_local("[[END]]").unwrap();
                self.state
                    .builder
                    .op(Opcode::GetLocal(start_local), span.clone());
                self.state
                    .builder
                    .op(Opcode::GetLocal(end_local), span.clone());
                self.state.builder.op(comparison_op, span.clone());
                self.state
                    .builder
                    .op(Opcode::JumpIfFalse(exit), span.clone());
                self.state.builder.op(Opcode::Pop, span.clone());
                self.state.builder.op(Opcode::Jump(body), span.clone());
            }
            IteratorKind::Expr(..) => {
                // emit `![[ITER]].done()`
                let iter_local = self.state.resolve_local("[[ITER]]").unwrap();
                self.state
                    .builder
                    .op(Opcode::GetLocal(iter_local), span.clone());
                let done = self
                    .state
                    .builder
                    .constant(self.ctx.alloc_or_intern("done").into(), span.clone())?;
                self.state.builder.get_magic(done, span.clone());
                self.state.builder.op(Opcode::Call(0), span.clone());
                self.state.builder.op(Opcode::Not, span.clone());
                self.state
                    .builder
                    .op(Opcode::JumpIfFalse(exit), span.clone());
                self.state.builder.op(Opcode::Pop, span.clone());
                self.state.builder.op(Opcode::Jump(body), span.clone());
            }
        }
        self.state.builder.label(latch);
        match info.iterator {
            IteratorKind::Range(..) => {
                // emit `info.variable += [[STEP]]`
                let start_local = self
                    .state
                    .resolve_local(info.variable.lexeme.as_ref())
                    .unwrap();
                let step_local = self.state.resolve_local("[[STEP]]").unwrap();
                self.state
                    .builder
                    .op(Opcode::GetLocal(start_local), span.clone());
                self.state
                    .builder
                    .op(Opcode::GetLocal(step_local), span.clone());
                self.state.builder.op(Opcode::Add, span.clone());
                self.state
                    .builder
                    .op(Opcode::SetLocal(start_local), span.clone());
                self.state.op_pop(1, span.clone());
                self.state.builder.op(Opcode::Jump(start), span.clone());
            }
            IteratorKind::Expr(..) => {
                // emit `<item> = [[ITER]].next()`
                let iter_local = self.state.resolve_local("[[ITER]]").unwrap();
                self.state
                    .builder
                    .op(Opcode::GetLocal(iter_local), span.clone());
                let next = self
                    .state
                    .builder
                    .constant(self.ctx.alloc_or_intern("next").into(), span.clone())?;
                self.state.builder.get_magic(next, span.clone());
                self.state.builder.op(Opcode::Call(0), span.clone());
                let item_local = self
                    .state
                    .resolve_local(info.variable.lexeme.as_ref())
                    .unwrap();
                self.state
                    .builder
                    .op(Opcode::SetLocal(item_local), span.clone());
                self.state.op_pop(1, span.clone());
                self.state.builder.op(Opcode::Jump(start), span.clone());
            }
        }
        self.state.builder.label(body);
        self.emit_stmt(&info.body)?;
        self.state.builder.op(Opcode::Jump(latch), span.clone());
        self.state.builder.label(exit);
        self.state.op_pop(1, span.clone());
        self.state.builder.label(end);
        self.state.end_loop();
        self.state.end_scope(span);

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
    fn emit_for_loop(&mut self, info: &'b For<'a>, span: Span) -> Result<()> {
        self.state.begin_scope();
        for init in info.initializers.iter() {
            self.emit_expr(&init.value, true)?;
            self.state.add_local(init.name.lexeme.clone());
        }
        self.state.begin_loop();
        let [start, latch, body, exit, end] = self.state.reserve_labels();
        // Break and continue target the `latch` and `exit` labels
        self.state.add_control_label(&info.label, latch, end);
        self.state.builder.label(start);
        if let Some(ref condition) = info.condition {
            self.emit_expr(condition, true)?;
            self.state
                .builder
                .op(Opcode::JumpIfFalse(exit), condition.span.clone());
            self.state.builder.op(Opcode::Pop, condition.span.clone());
            self.state
                .builder
                .op(Opcode::Jump(body), condition.span.clone());
        } else {
            // if no condition is provided, it is implicitly `true`.
            // Instead of emitting an analog of a `while true` loop, we jump directly into the loop body.
            self.state.builder.op(Opcode::Jump(body), span.clone());
        }
        self.state.builder.label(latch);
        if let Some(ref increment) = info.increment {
            self.emit_expr(increment, true)?;
            self.state.op_pop(1, increment.span.clone());
            self.state
                .builder
                .op(Opcode::Jump(start), increment.span.clone());
        }
        self.state.builder.label(body);
        self.emit_stmt(&info.body)?;
        self.state.builder.op(Opcode::Jump(latch), span.clone());
        self.state.builder.label(exit);
        if info.condition.is_some() {
            self.state.op_pop(1, span.clone());
        }
        self.state.builder.label(end);
        self.state.end_loop();
        self.state.end_scope(span);

        Ok(())
    }

    fn emit_block(&mut self, body: &'b [Stmt<'a>], span: Span) -> Result<()> {
        self.state.begin_scope();
        for stmt in body {
            self.emit_stmt(stmt)?;
        }
        self.state.end_scope(span);

        Ok(())
    }

    fn emit_defer_stmt(&mut self, call: &'b Call<'a>, span: Span) -> Result<()> {
        self.emit_expr(&call.callee, true)?;
        for arg in call.args.iter() {
            self.emit_expr(arg, true)?;
        }
        self.state.builder.op(Opcode::Defer, span);
        Ok(())
    }

    fn emit_expr(&mut self, expr: &'b Expr<'a>, is_sub_expr: bool) -> Result<()> {
        let span = expr.span.clone();
        match expr.kind {
            ExprKind::Lit(ref literal) => self.emit_lit(literal)?,
            ExprKind::Binary(op, ref a, ref b) => self.emit_binary_expr(op, a, b, span)?,
            ExprKind::Unary(op, ref operand) => self.emit_unary_expr(op, operand, span)?,
            ExprKind::Struct(ref info) => self.emit_struct_expr(info, span, is_sub_expr)?,
            ExprKind::Fn(ref info) => self.emit_fn_expr(info, span, is_sub_expr)?,
            ExprKind::If(ref info) => self.emit_if_expr(info, span)?,
            ExprKind::DoBlock(ref block) => self.emit_do_block_expr(block, span)?,
            ExprKind::Comma(ref exprs) => self.emit_comma_expr(exprs, span)?,
            ExprKind::Call(ref call) => self.emit_call_expr(call, span)?,
            ExprKind::Spread(ref expr) => {
                self.emit_expr(expr, true)?;
                self.state.builder.op(Opcode::Spread, span);
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
            ExprKind::Grouping(ref expr) => self.emit_expr(expr, true)?,
        }

        Ok(())
    }

    fn emit_binary_expr(
        &mut self,
        op: BinOpKind,
        left: &'b Expr<'a>,
        right: &'b Expr<'a>,
        span: Span,
    ) -> Result<()> {
        self.emit_expr(left, true)?;
        if op == BinOpKind::Is {
            let inst = match right.kind {
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
            if let Some(inst) = inst {
                self.state.builder.op(inst, span);
            } else {
                self.emit_expr(right, true)?;
                self.state.builder.op(Opcode::CompareType, span);
            }
        } else if matches!(op, BinOpKind::And | BinOpKind::Or) {
            self.emit_logical_expr(op, right, span)?;
        } else {
            self.emit_expr(right, true)?;
            self.state.builder.op(
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

    fn emit_logical_expr(&mut self, op: BinOpKind, right: &'b Expr<'a>, span: Span) -> Result<()> {
        match op {
            BinOpKind::And => {
                let end = self.state.reserve_label();
                self.state
                    .builder
                    .op(Opcode::JumpIfFalse(end), span.clone());
                self.state.op_pop(1, span);
                self.emit_expr(right, true)?;
                self.state.builder.label(end);
            }
            BinOpKind::Or => {
                let [other, end] = self.state.reserve_labels();
                self.state
                    .builder
                    .op(Opcode::JumpIfFalse(other), span.clone());
                self.state.builder.op(Opcode::Jump(end), span.clone());
                self.state.builder.label(other);
                self.state.op_pop(1, span);
                self.emit_expr(right, true)?;
                self.state.builder.label(end)
            }
            _ => unreachable!(),
        }
        Ok(())
    }

    fn emit_unary_expr(&mut self, op: UnOpKind, operand: &'b Expr<'a>, span: Span) -> Result<()> {
        self.emit_expr(operand, true)?;
        self.state.builder.op(
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

    // TODO
    fn emit_struct_expr(
        &mut self,
        info: &'b StructInfo<'a>,
        span: Span,
        is_sub_expr: bool,
    ) -> Result<()> {
        self.state.begin_struct(info.name.lexeme.clone());
        if is_sub_expr {
            // if the struct is in a sub expression, then it should only be accessible from its own body
            self.state.begin_scope();
            self.state.define(info.name.lexeme.clone(), span.clone())?;
        }
        self.state.builder.op(Opcode::CreateStruct, span.clone());
        // (magic) methods
        for method in info.methods.iter() {
            self.emit_fn_expr(method, span.clone(), true)?;
            match method.name.lexeme.strip_prefix('@') {
                Some(name) => {
                    // TODO: how to *not* to_string here?
                    let name_index = self.state.builder.constant(
                        self.ctx.alloc_or_intern(name.to_string()).into(),
                        span.clone(),
                    )?;
                    self.state
                        .builder
                        .op(Opcode::AddMagicMethod(name_index), span.clone());
                }
                None => {
                    // TODO: how to *not* to_string here?
                    let name_index = self.state.builder.constant(
                        self.ctx
                            .alloc_or_intern(method.name.lexeme.to_string())
                            .into(),
                        span.clone(),
                    )?;
                    self.state
                        .builder
                        .op(Opcode::AddMethod(name_index), span.clone());
                }
            }
        }
        // static methods
        for method in info.r#static.methods.iter() {
            self.emit_fn_expr(method, span.clone(), true)?;
            let name_index = self.state.builder.constant(
                self.ctx.alloc_or_intern(method.name.lexeme.clone()).into(),
                span.clone(),
            )?;
            self.state
                .builder
                .op(Opcode::AddStaticMethod(name_index), span.clone());
        }
        // static fields
        for field in info.r#static.fields.iter() {
            if let Some(ref init) = field.1 {
                self.emit_expr(init, true)?;
            } else {
                self.state.builder.op(Opcode::PushNone, span.clone());
            }
            let name_index = self.state.builder.constant(
                self.ctx.alloc_or_intern(field.0.lexeme.clone()).into(),
                span.clone(),
            )?;
            self.state
                .builder
                .op(Opcode::AddStaticField(name_index), span.clone());
        }
        // initializer
        if let Some(ref initializer) = info.initializer {
            let name_index = self
                .state
                .builder
                .constant(self.ctx.alloc_or_intern("init").into(), span.clone())?;
            self.emit_fn_expr(&initializer.body, span.clone(), true)?;
            self.state
                .builder
                .op(Opcode::AddMethod(name_index), span.clone());
        }
        if is_sub_expr {
            // close the temporary function local scope, but don't pop the value
            self.state.end_scope_partial(span.clone(), 1);
        }
        if !is_sub_expr {
            // if the struct isn't in a sub expression, it should define a variable
            // in the scope where it's declared
            self.state.define_no_pop(info.name.lexeme.clone(), span)?;
        }
        self.state.end_struct();
        Ok(())
    }

    fn emit_fn_expr(&mut self, info: &'b FnInfo<'a>, span: Span, is_sub_expr: bool) -> Result<()> {
        // just like structs, if the fn is in a sub expression,
        // then it should only be accessible from its own body
        if info.kind == FnKind::Function && is_sub_expr {
            // open an extra scope just for the function local
            self.state.begin_scope();
            self.state.define(info.name.lexeme.clone(), span.clone())?;
        }
        self.begin_state();
        self.state.begin_scope();
        self.state.fn_kind = Some(info.kind);
        if matches!(
            info.kind,
            FnKind::Method | FnKind::Initializer | FnKind::MagicMethod
        ) {
            self.state.add_local("self");
        } else {
            self.state.add_local("");
        }
        for param in info.params.positional.iter() {
            if param.0.lexeme == "self" {
                // `self` is implicit
                continue;
            }
            self.state.add_local(param.0.lexeme.clone());
        }
        for param in info.params.default.iter() {
            self.state.add_local(param.0.lexeme.clone());
            self.emit_default_param(&param.0, &param.1, param.0.span.start..param.1.span.end)?;
        }
        if let Some(rest) = &info.params.rest {
            self.state.add_local(rest.lexeme.clone());
        }
        for stmt in info.body.iter() {
            self.emit_stmt(stmt)?;
        }
        self.state.end_scope_partial(
            // in case we're in an initializer, don't pop `self`
            span.clone(),
            if info.kind == FnKind::Initializer {
                1
            } else {
                0
            },
        );
        if info.kind != FnKind::Initializer {
            self.state.builder.op(Opcode::PushNone, span.clone());
        }
        self.state.builder.op(Opcode::Return, span.clone());
        let upvalues = std::mem::take(&mut self.state.upvalues);
        let chunk = self.end_state();
        if info.kind == FnKind::Function && is_sub_expr {
            // close the temporary function local scope, but don't pop the value
            self.state.end_scope_partial(span.clone(), 1);
        }
        let name = self.ctx.alloc_or_intern(if info.kind == FnKind::Function {
            info.name.lexeme.clone()
        } else {
            format!(
                "{}.{}",
                self.state.resolve_struct_name().unwrap(),
                info.name.lexeme
            )
            .into()
        });
        let fn_constant_index = self.state.builder.constant(
            self.ctx.alloc_value(VesFn {
                name: VesStrView::new(name),
                positionals: info.params.positional.len() as u32,
                defaults: info.params.default.len() as u32,
                rest: info.params.rest.is_some(),
                chunk,
                file_id: self.ast.file_id,
                is_magic_method: info.kind == FnKind::MagicMethod,
            }),
            span.clone(),
        )?;
        // if there are no upvalues, the function does not need to be a closure
        if upvalues.is_empty() {
            self.state
                .builder
                .op(Opcode::GetConst(fn_constant_index), span.clone());
        } else {
            let closure_desc_index = self.state.builder.constant(
                self.ctx.alloc_value(ClosureDescriptor {
                    fn_constant_index,
                    upvalues,
                }),
                span.clone(),
            )?;
            self.state
                .builder
                .op(Opcode::CreateClosure(closure_desc_index), span.clone());
        }
        // if the fn isn't in a sub expression, it should define a variable
        // in the scope where it's declared
        if info.kind == FnKind::Function && !is_sub_expr {
            self.state.define_no_pop(info.name.lexeme.clone(), span)?;
        }
        Ok(())
    }

    /// Emits the conditional assignment to a default parameter
    fn emit_default_param(&mut self, name: &Token<'a>, value: &Expr<'a>, span: Span) -> Result<()> {
        // format:
        // if <param> is none { <param> = <value>; }
        let r#if = If {
            condition: Condition {
                value: Expr {
                    // <param> is none
                    kind: ExprKind::Binary(
                        BinOpKind::Is,
                        box Expr {
                            kind: ExprKind::Variable(name.clone()),
                            span: span.clone(),
                        },
                        box Expr {
                            kind: ExprKind::Lit(box Lit {
                                value: LitValue::None,
                                token: Token::new("none", span.clone(), TokenKind::None),
                            }),
                            span: span.clone(),
                        },
                    ),
                    span: span.clone(),
                },
                pattern: ConditionPattern::Value,
            },
            then: DoBlock {
                statements: vec![Stmt {
                    // <param> = <value>
                    kind: StmtKind::ExprStmt(box Expr {
                        kind: ExprKind::Assignment(box Assignment {
                            name: name.clone(),
                            value: value.clone(),
                        }),
                        span: span.clone(),
                    }),
                    span: span.clone(),
                }],
                value: None,
            },
            otherwise: None,
        };
        self.emit_if_expr(
            // Dumb lifetime problem
            unsafe { std::mem::transmute(&r#if) },
            span,
        )
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
    fn emit_if_expr(&mut self, info: &'b If<'a>, span: Span) -> Result<()> {
        // reserve only a single `end` label, which is used as the exit point for all branches
        let end = self.state.reserve_label();
        // similarly to a do block, an if expression has a value
        // this value must outlive every inner scope of the entire expression
        self.state.begin_scope();
        let value_slot = self.state.add_local("[[VALUE]]");
        self.state.builder.op(Opcode::PushNone, span.clone());
        let mut current_branch = Some(info);
        // instead of recursively, the if expression is emitted iteratively,
        // because it greatly simplifies handling of scope
        while let Some(branch) = current_branch {
            let other = self.state.reserve_label();
            self.state.begin_scope();
            let mut used_pattern = false;
            match branch.condition.pattern {
                ConditionPattern::Value => {
                    self.emit_expr(&branch.condition.value, true)?;
                }
                ConditionPattern::IsOk(ref binding) => {
                    used_pattern = true;
                    let slot = self.state.add_local(binding.lexeme.clone());
                    self.state
                        .builder
                        .op(Opcode::PushNone, binding.span.clone());
                    self.emit_expr(&branch.condition.value, true)?;
                    self.state
                        .builder
                        .op(Opcode::UnwrapOk(slot), binding.span.clone());
                }
                ConditionPattern::IsErr(ref binding) => {
                    used_pattern = true;
                    let slot = self.state.add_local(binding.lexeme.clone());
                    self.state
                        .builder
                        .op(Opcode::PushNone, binding.span.clone());
                    self.emit_expr(&branch.condition.value, true)?;
                    self.state
                        .builder
                        .op(Opcode::UnwrapErr(slot), binding.span.clone());
                }
            }
            self.state
                .builder
                .op(Opcode::JumpIfFalse(other), span.clone());
            self.state.builder.op(Opcode::Pop, span.clone());
            for stmt in branch.then.statements.iter() {
                self.emit_stmt(stmt)?;
            }
            if let Some(ref value) = branch.then.value {
                self.emit_expr(value, true)?;
                self.state
                    .builder
                    .op(Opcode::SetLocal(value_slot), span.clone());
                self.state.op_pop(1, span.clone());
            }
            self.state.end_scope(span.clone());
            self.state.builder.op(Opcode::Jump(end), span.clone());
            self.state.builder.label(other);
            self.state.op_pop(1, span.clone());
            if used_pattern {
                self.state.op_pop(1, span.clone());
            }
            current_branch = match branch.otherwise {
                Some(Else::Block(ref block)) => {
                    self.state.begin_scope();
                    for stmt in block.statements.iter() {
                        self.emit_stmt(stmt)?;
                    }
                    if let Some(ref value) = block.value {
                        self.emit_expr(value, true)?;
                        self.state
                            .builder
                            .op(Opcode::SetLocal(value_slot), span.clone());
                        self.state.op_pop(1, span.clone());
                    }
                    self.state.end_scope(span.clone());
                    None
                }
                Some(Else::If(ref branch)) => Some(branch),
                _ => None,
            }
        }
        self.state.builder.label(end);
        self.state.end_scope_partial(span, 1);
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
    fn emit_do_block_expr(&mut self, do_block: &'b DoBlock<'a>, span: Span) -> Result<()> {
        self.state.begin_scope();
        let value_slot = self.state.add_local("[[VALUE]]");
        self.state.builder.op(Opcode::PushNone, span.clone());

        for stmt in do_block.statements.iter() {
            self.emit_stmt(stmt)?;
        }
        if let Some(ref value) = do_block.value {
            self.emit_expr(value, true)?;
            self.state
                .builder
                .op(Opcode::SetLocal(value_slot), span.clone());
            self.state.op_pop(1, span.clone());
        }
        // preserve one local value on the stack
        self.state.end_scope_partial(span, 1);
        Ok(())
    }

    fn emit_comma_expr(&mut self, exprs: &'b [Expr<'a>], span: Span) -> Result<()> {
        // a comma expression is guaranteed to have at least 2 sub expressions,
        // so this will never panic due to underflow
        // we want to pop every expr except the last one (which is the result of the expression)
        for i in 0..exprs.len() - 1 {
            self.emit_expr(&exprs[i], true)?;
        }
        self.state.op_pop((exprs.len() - 1) as u32, span);
        self.emit_expr(exprs.last().unwrap(), true)?;

        Ok(())
    }

    fn emit_call_expr(&mut self, call: &'b Call<'a>, span: Span) -> Result<()> {
        self.emit_expr(&call.callee, true)?;
        for expr in call.args.iter() {
            self.emit_expr(expr, true)?;
        }
        self.state
            .builder
            .op(Opcode::Call(call.args.len() as u32), span);
        Ok(())
    }

    fn emit_lit(&mut self, lit: &'b Lit<'a>) -> Result<()> {
        let span = lit.token.span.clone();
        match &lit.value {
            LitValue::Float(value) => {
                let offset = self.state.builder.constant((*value).into(), span.clone())?;
                self.state.builder.op(Opcode::GetConst(offset), span);
            }
            LitValue::Integer(value) => {
                self.state.builder.op(Opcode::PushInt32(*value), span);
            }
            LitValue::Bool(value) => {
                self.state.builder.op(
                    match value {
                        true => Opcode::PushTrue,
                        false => Opcode::PushFalse,
                    },
                    span,
                );
            }
            LitValue::BigInteger(i) => {
                let int = VesInt::new(i.clone(), self.ctx.vtables.int.clone(), self.ctx.gc.proxy());
                let int = self.ctx.alloc_value(int);
                let offset = self.state.builder.constant(int, span.clone())?;
                self.state.builder.op(Opcode::GetConst(offset), span);
            }
            LitValue::None => {
                self.state.builder.op(Opcode::PushNone, span);
            }
            LitValue::Str(ref value) => {
                let ptr = self.ctx.alloc_or_intern(value.clone());
                let offset = self.state.builder.constant(Value::Ref(ptr), span.clone())?;
                self.state.builder.op(Opcode::GetConst(offset), span);
            }
        }

        Ok(())
    }

    fn emit_get_prop(
        &mut self,
        node: &'b Expr<'a>,
        name: &Token<'a>,
        is_optional: bool,
        span: Span,
    ) -> Result<()> {
        self.emit_expr(node, true)?;
        let offset = self.state.builder.constant(
            self.ctx.alloc_or_intern(name.lexeme.clone()).into(),
            span.clone(),
        )?;
        // TODO: try to speculatively populate the cache
        self.state.builder.with_ic(
            if is_optional {
                Opcode::TryGetProp
            } else {
                Opcode::GetProp
            },
            offset,
            span,
        );
        Ok(())
    }

    fn emit_set_prop(
        &mut self,
        node: &'b Expr<'a>,
        name: &Token<'a>,
        value: &'b Expr<'a>,
        span: Span,
    ) -> Result<()> {
        self.emit_expr(node, true)?;
        self.emit_expr(value, true)?;
        let offset = self.state.builder.constant(
            self.ctx.alloc_or_intern(name.lexeme.clone()).into(),
            span.clone(),
        )?;
        // TODO: try to speculatively populate the cache
        self.state.builder.set_prop(offset, span);
        Ok(())
    }

    fn emit_get_item(&mut self, node: &'b Expr<'a>, key: &'b Expr<'a>, span: Span) -> Result<()> {
        self.emit_expr(node, true)?;
        self.emit_expr(key, true)?;
        self.state.builder.op(Opcode::GetItem, span);
        Ok(())
    }

    fn emit_set_item(
        &mut self,
        node: &'b Expr<'a>,
        key: &'b Expr<'a>,
        value: &'b Expr<'a>,
        span: Span,
    ) -> Result<()> {
        self.emit_expr(node, true)?;
        self.emit_expr(key, true)?;
        self.emit_expr(value, true)?;
        self.state.builder.op(Opcode::SetItem, span);
        Ok(())
    }

    fn emit_fstring(&mut self, fstr: &'b FString<'a>, span: Span) -> Result<()> {
        for frag in fstr.fragments.iter() {
            match frag {
                FStringFrag::Str(ref lit) => self.emit_lit(lit)?,
                FStringFrag::Expr(ref expr) => self.emit_expr(expr, true)?,
            }
        }
        self.state
            .builder
            .op(Opcode::Interpolate(fstr.fragments.len() as u32), span);
        Ok(())
    }

    fn emit_array_lit(&mut self, exprs: &'b [Expr<'a>], span: Span) -> Result<()> {
        for expr in exprs {
            self.emit_expr(expr, true)?;
        }
        self.state
            .builder
            .op(Opcode::CreateArray(exprs.len() as u32), span);
        Ok(())
    }

    fn emit_map_lit(&mut self, entries: &'b [MapEntry<'a>], span: Span) -> Result<()> {
        self.state.builder.op(Opcode::CreateEmptyMap, span.clone());
        for entry in entries {
            match entry {
                MapEntry::Pair(ref key, ref value) => {
                    self.emit_expr(key, true)?;
                    self.emit_expr(value, true)?;
                    self.state.builder.op(Opcode::MapInsert, span.clone());
                }
                MapEntry::Spread(ref expr) => {
                    self.emit_expr(expr, true)?;
                    self.state.builder.op(Opcode::MapExtend, span.clone());
                }
            }
        }
        Ok(())
    }

    fn emit_var_expr(&mut self, name: &Token<'_>) -> Result<()> {
        let get = self.state.resolve_variable_get(name.lexeme.as_ref());
        self.state.builder.op(get, name.span.clone());

        Ok(())
    }

    fn emit_assign_expr(&mut self, name: &str, value: &'b Expr<'a>, span: Span) -> Result<()> {
        self.emit_expr(&value, true)?;
        let set = self.state.resolve_variable_set(name);
        self.state.builder.op(set, span);
        // we don't pop the right-side expression result, because
        // it's the result of the assignment expression

        Ok(())
    }

    fn emit_incdec_expr(
        &mut self,
        incdec: &'b IncDec<'a>,
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
                self.state.builder.op(add_or_sub_one, span.clone());
                let offset = self.state.builder.constant(
                    self.ctx.alloc_or_intern(get.field.lexeme.clone()).into(),
                    span.clone(),
                )?;
                self.state.builder.set_prop(offset, span.clone());
            }
            ExprKind::GetItem(ref get) => {
                self.emit_get_item(&get.node, &get.key, span.clone())?;
                self.emit_expr(&get.key, true)?;
                self.emit_get_item(&get.node, &get.key, span.clone())?;
                self.state.builder.op(add_or_sub_one, span.clone());
                self.state.builder.op(Opcode::SetItem, span.clone());
            }
            ExprKind::Variable(ref var) => {
                self.emit_var_expr(var)?;
                self.state.builder.op(add_or_sub_one, span.clone());
                let set = self.state.resolve_variable_set(var.lexeme.as_ref());
                self.state.builder.op(set, span.clone());
            }
            _ => unreachable!(),
        }
        if is_postfix {
            match incdec.kind {
                IncDecKind::Increment => self.state.builder.op(Opcode::SubtractOne, span),
                IncDecKind::Decrement => self.state.builder.op(Opcode::AddOne, span),
            };
        }
        Ok(())
    }
}

/// Checks if an `i64` fits within an `i32`, and converts it if so.
fn maybe_i32(value: i64) -> Option<i32> {
    const MIN: i64 = i32::MIN as i64;
    const MAX: i64 = i32::MAX as i64;
    if (MIN..=MAX).contains(&value) {
        Some(value as i32)
    } else {
        None
    }
}

#[cfg(test)]
#[ves_testing::ves_test_suite]
mod suite {
    use super::*;

    #[ves_tests = "tests/codegen"]
    mod codegen_tests {
        #[ok_callback]
        use super::_impl::compile;

        #[input_callback]
        use super::_impl::strip_comments;
    }

    mod _impl {
        use crate::{
            emitter::VTables,
            gc::{DefaultGc, GcHandle},
        };

        use super::*;
        use ves_error::VesFileDatabase;
        use ves_middle::Resolver;
        use ves_parser::{Lexer, Parser};

        fn format_closure_descriptor(d: &ClosureDescriptor, c: &[Value]) -> String {
            format!("{}, {}", c[d.fn_constant_index as usize], d.upvalues.len())
        }

        fn format_op(op: &Opcode, c: &[Value]) -> String {
            match op {
                Opcode::GetConst(i) => format!("GetConst({})", c[*i as usize]),
                Opcode::CreateClosure(i) => format!("CreateClosure({})", {
                    match c[*i as usize] {
                        Value::Ref(v) => match &*v {
                            VesObject::ClosureDescriptor(v) => format_closure_descriptor(v, c),
                            _ => unreachable!(),
                        },
                        _ => unreachable!(),
                    }
                }),
                _ => format!("{:?}", op),
            }
        }

        fn chunk_concat(out: &mut String, r#fn: &VesFn) {
            if r#fn.name.str() != "<main>" {
                *out += &format!("\n>>>>>> {}\n", r#fn.name.str());
            }
            *out += &r#fn
                .chunk
                .code
                .iter()
                .enumerate()
                .map(|(i, op)| format!("|{:<04}| {}", i, format_op(&op, &r#fn.chunk.constants)))
                .collect::<Vec<_>>()
                .join("\n");
            for constant in r#fn.chunk.constants.iter() {
                if let Some(ptr) = constant.as_ptr() {
                    if let Some(r#fn) = ptr.as_fn() {
                        chunk_concat(out, &r#fn);
                    }
                }
            }
        }

        pub fn compile(src: String) -> String {
            let mut fdb = VesFileDatabase::default();
            let fid = fdb.add_snippet(&src);
            let mut ast = Parser::new(Lexer::new(&src), fid, &fdb).parse().unwrap();
            Resolver::new().resolve(&mut ast).unwrap();
            let gc = GcHandle::new(DefaultGc::default());
            let mut out = String::new();
            let mut vtables = VTables::init(gc.clone());
            chunk_concat(
                &mut out,
                &Emitter::new(
                    &ast,
                    CompilationContext {
                        // we mustn't move the Gc into here since it may get dropped
                        gc: gc.clone(),
                        strings: &mut HashMap::new(),
                        vtables: &mut vtables,
                    },
                )
                .emit()
                .unwrap()
                .as_fn()
                .unwrap(),
            );
            std::mem::drop(gc);
            out
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
