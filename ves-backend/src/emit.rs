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

#[derive(Debug)]
struct LoopInfo {
    jump_index: usize,
    loop_id: usize,
    origin: Span,
}
impl<'a> LoopInfo {
    pub fn new(loop_id: usize, jump_index: usize, origin: Span) -> LoopInfo {
        LoopInfo {
            loop_id,
            jump_index,
            origin,
        }
    }
}

struct State<'a> {
    builder: BytecodeBuilder,
    loops: Vec<LoopInfo>,
    locals: Vec<Local<'a>>,
    globals: Rc<HashMap<String, u32>>,
    scope_depth: usize,

    // Jumps
    loop_id: usize,
    label_id: u32,
    labels: HashMap<Cow<'a, str>, u32>,
}

impl<'a> State<'a> {
    fn new(file_id: FileId, globals: Rc<HashMap<String, u32>>) -> Self {
        State {
            builder: BytecodeBuilder::new(file_id),
            loops: vec![],
            locals: vec![],
            labels: HashMap::new(),
            globals,
            scope_depth: 0,
            loop_id: 0,
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

        if n_locals == 1 {
            self.builder.op(Opcode::Pop, scope_span);
        } else if n_locals > 1 {
            self.builder.op(Opcode::PopN(n_locals as u32), scope_span);
        }
    }

    fn begin_loop(&mut self) {
        self.loop_id += 1;
    }

    fn end_loop(&mut self) {
        self.loop_id -= 1;
    }

    fn reserve_label(&mut self) -> u32 {
        self.label_id += 1;
        self.label_id - 1
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
            globals.insert(global.name.lexeme.clone().into_owned(), idx as _);
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

    fn emit_label(&mut self, named_label: Option<&Token<'a>>) -> u32 {
        let label = self.state().reserve_label();
        let name = if let Some(named) = named_label {
            named.lexeme.clone()
        } else {
            Cow::Owned(format!("#label-{}", label))
        };
        self.state().labels.insert(name, label);
        self.state().builder.label(label);
        label
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
                        self.state().builder.op(Opcode::None, var.name.span.clone());
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

    fn emit_loop(&mut self, r#loop: &Loop<'a>, span: Span) -> Result<()> {
        self.state().begin_loop();
        let loop_start_label = self.emit_label(r#loop.label.as_ref());
        self.emit_stmt(&r#loop.body)?;
        self.emit_jump(loop_start_label, span);
        self.state().end_loop();
        Ok(())
    }

    fn emit_jump(&mut self, label: u32, span: Span) {
        self.state().builder.op(Opcode::Jump(label), span);
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
                        UnOpKind::Not => Opcode::Not,
                        UnOpKind::Neg => Opcode::Neg,
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
                    BinOpKind::Sub => Opcode::Sub,
                    BinOpKind::Mul => Opcode::Mul,
                    BinOpKind::Div => Opcode::Div,
                    BinOpKind::Rem => Opcode::Rem,
                    BinOpKind::Pow => Opcode::Pow,
                    BinOpKind::And => Opcode::And,
                    BinOpKind::Or => Opcode::Or,
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
                    self.state().builder.op(Opcode::Num32(value), span);
                }
                None => {
                    let offset = self.state().builder.constant(value.into(), span.clone())?;
                    self.state().builder.op(Opcode::GetConst(offset), span);
                }
            },
            LitValue::Bool(value) => {
                self.state().builder.op(
                    match value {
                        true => Opcode::True,
                        false => Opcode::False,
                    },
                    span,
                );
            }
            LitValue::None => {
                self.state().builder.op(Opcode::None, span);
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
            Opcode::Num32(1.0),
            Opcode::Num32(2.0),
            Opcode::Num32(10.0),
            Opcode::Num32(-1.0),
            Opcode::Pow,
            Opcode::Mul,
            Opcode::Num32(2.0),
            Opcode::Div,
            Opcode::Add,
            Opcode::Pop
        ]
    );
    case!(
        type_comparison_num,
        "0 is num",
        vec![Opcode::Num32(0.0), Opcode::IsNum, Opcode::Pop]
    );
    case!(
        type_comparison_str,
        "0 is str",
        vec![Opcode::Num32(0.0), Opcode::IsStr, Opcode::Pop]
    );
    case!(
        type_comparison_bool,
        "0 is bool",
        vec![Opcode::Num32(0.0), Opcode::IsBool, Opcode::Pop]
    );
    case!(
        type_comparison_map,
        "0 is map",
        vec![Opcode::Num32(0.0), Opcode::IsMap, Opcode::Pop]
    );
    case!(
        type_comparison_array,
        "0 is array",
        vec![Opcode::Num32(0.0), Opcode::IsArray, Opcode::Pop]
    );
    case!(
        type_comparison_none,
        "0 is none",
        vec![Opcode::Num32(0.0), Opcode::IsNone, Opcode::Pop]
    );
    case!(
        type_comparison_some,
        "0 is some",
        vec![Opcode::Num32(0.0), Opcode::IsSome, Opcode::Pop]
    );
    case!(
        type_comparison_struct,
        "mut T; 0 is T",
        vec![
            Opcode::None,
            Opcode::SetGlobal(0),
            Opcode::Num32(0.0),
            Opcode::GetGlobal(0),
            Opcode::CompareType,
            Opcode::Pop
        ]
    );
    case!(
        field_check,
        "0 in 0",
        vec![
            Opcode::Num32(0.0),
            Opcode::Num32(0.0),
            Opcode::HasProperty,
            Opcode::Pop
        ]
    );
    case!(
        global_variable,
        "let a = 0",
        vec![Opcode::Num32(0.0), Opcode::SetGlobal(0)]
    );
    case!(
        local_variable,
        "{ let a = 0; }",
        vec![Opcode::Num32(0.0), Opcode::Pop]
    );
    case!(
        many_local_variables,
        "{ mut a, b, c, d }",
        vec![
            Opcode::None,
            Opcode::None,
            Opcode::None,
            Opcode::None,
            Opcode::PopN(4)
        ]
    );
    case!(
        print_one,
        "print(0)",
        vec![Opcode::Num32(0.0), Opcode::Print,]
    );
    case!(
        print_many,
        "print(0, 2, 2)",
        vec![
            Opcode::Num32(0.0),
            Opcode::Num32(2.0),
            Opcode::Num32(2.0),
            Opcode::PrintN(3),
        ]
    );
    case!(
        get_global,
        "mut a; a;",
        vec![
            Opcode::None,
            Opcode::SetGlobal(0),
            Opcode::GetGlobal(0),
            Opcode::Pop
        ]
    );
    case!(
        get_local,
        "{ mut a; a; }",
        vec![Opcode::None, Opcode::GetLocal(0), Opcode::Pop, Opcode::Pop]
    );
    case!(
        multi_scope_local_resolution,
        "{ mut a; { mut a; { mut a; { mut a; a; } a; } a; } a; }",
        vec![
            Opcode::None,
            Opcode::None,
            Opcode::None,
            Opcode::None,
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
    case!(
        loop_with_body,
        "loop { mut a; 1 + 1; }",
        vec![
            Opcode::None,
            Opcode::Num32(1.0),
            Opcode::Num32(1.0),
            Opcode::Add,
            Opcode::Pop,
            Opcode::Pop,
            Opcode::Jump(0)
        ]
    );
    case!(
        loop_inside_scope,
        "mut a; { mut b; { mut c; loop { mut d = c; a + b; loop {} } } }",
        vec![
            Opcode::None,         //
            Opcode::SetGlobal(0), // mut a = none
            Opcode::None,         // mut b = none
            Opcode::None,         // mut c = none
            /* loop 1 start - at 4 */
            Opcode::GetLocal(1),  // mut d = c
            Opcode::GetGlobal(0), // a
            Opcode::GetLocal(0),  // b
            Opcode::Add,          // a + b
            Opcode::Pop,          // pop a + b
            /* loop 2 start - at 9 */
            Opcode::Jump(9), // jump to loop 2
            /* loop 2 end */
            Opcode::Pop,     // pop d
            Opcode::Jump(4), // jump to loop 1
            /* loop 1 end */
            Opcode::Pop, // pop c
            Opcode::Pop  // pop b
        ]
    );
}
