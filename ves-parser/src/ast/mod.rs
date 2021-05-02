use std::{borrow::Cow, cell::Cell, collections::HashSet};

use ast2str::AstToStr;
use ves_error::{FileId, Files, VesFileDatabase};

use crate::lexer::{Span, Token, TokenKind};

pub type Ptr<T> = Box<T>;
pub type ExprPtr<'a> = Ptr<Expr<'a>>;
pub type StmtPtr<'a> = Ptr<Stmt<'a>>;
pub type BinOp = BinOpKind;
pub type UnOp = UnOpKind;
pub type Args<'a> = Vec<Expr<'a>>;

/// Returns `true` if the given token is a reserved identifier.
pub fn is_reserved_identifier(token: &Token<'_>) -> bool {
    if token.kind == TokenKind::Identifier {
        matches!(&token.lexeme[..], "num" | "str" | "bool" | "map" | "arr")
    } else {
        token.kind == TokenKind::Self_ || token.kind == TokenKind::Some
    }
}

/// A global variable. This struct doesn't appear anywhere in the AST directly and is created
/// by the parser every time it visits a global declaration.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Global<'a> {
    /// The name of the global.
    pub name: Token<'a>,
    /// The kind of the global.
    pub kind: VarKind,
}

/// An imported or exported symbol.
#[derive(Clone, Debug, PartialEq, AstToStr)]
pub enum Symbol<'a> {
    /// An imported/exported name without an alias
    Bare(#[rename = "symbol"] Token<'a>),
    /// An imported/exported name with an alias
    Aliased(
        /// The symbol that is being aliased
        #[rename = "name"]
        Token<'a>,
        /// The alias
        #[rename = "as"]
        Token<'a>,
    ),
}

impl<'a> Symbol<'a> {
    /// Returns the "bare" part of the symbol.
    pub fn bare(&self) -> &str {
        match self {
            Symbol::Bare(bare) => bare.lexeme.as_ref(),
            Symbol::Aliased(bare, _) => bare.lexeme.as_ref(),
        }
    }
}

/// A relative import of a file.
#[derive(Clone, Debug, PartialEq, AstToStr)]
pub enum ImportPath<'a> {
    /// A simple path (e.g. `import thing`)
    ///
    /// This has to be resolved into a full path
    /// according to resolution config before usage
    Simple(#[rename = "symbol"] Symbol<'a>),
    /// A full path (e.g. `import "../src/thing.ves"`)
    Full(#[rename = "symbol"] Symbol<'a>),
}

/// An import statement.
#[derive(Clone, Debug, PartialEq, AstToStr)]
pub enum ImportStmt<'a> {
    /// A direct import (e.g. `import thing`)
    Direct(#[rename = "path"] ImportPath<'a>),
    /// A destructured import (e.g. `import { a, b as c } from thing`)
    Destructured(
        #[rename = "path"] ImportPath<'a>,
        #[rename = "symbols"] Vec<Symbol<'a>>,
    ),
}

/// An import statement with a resolved path to the file being imported.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct Import<'a> {
    /// The import statement.
    pub import: ImportStmt<'a>,
    /// The actual file being imported.
    pub resolved_path: Option<String>,
}

/// An Abstract Syntax Tree for a Ves source file.
#[derive(Debug, PartialEq, AstToStr)]
pub struct AST<'a> {
    #[forward]
    /// The statements in the global scope.
    pub body: Vec<Stmt<'a>>,
    /// The id of the file the AST belongs to.
    pub file_id: FileId,
    /// The set of all global variables declared in the source file.
    pub globals: HashSet<Global<'a>>,
    /// The file's imported symbols.
    pub imports: Vec<Import<'a>>,
    /// The file's exported symbols>
    pub exports: Vec<Symbol<'a>>,
}

impl<'a> AST<'a> {
    /// Creates a new [`AST`] form the given statements and [`FileId`].
    pub fn new(body: Vec<Stmt<'a>>, file_id: FileId) -> Self {
        Self {
            body,
            file_id,
            globals: HashSet::new(),
            imports: Vec::new(),
            exports: Vec::new(),
        }
    }

    /// Creates a new [`AST`] form the given statements, globals, imports, exports, and [`FileId`].
    pub fn with(
        body: Vec<Stmt<'a>>,
        globals: HashSet<Global<'a>>,
        imports: Vec<Import<'a>>,
        exports: Vec<Symbol<'a>>,
        file_id: FileId,
    ) -> Self {
        Self {
            body,
            file_id,
            globals,
            imports,
            exports,
        }
    }

    /// Pretty-prints the AST into a string, using the file name and hash from the database.
    pub fn to_str_with_db<N: AsRef<str> + Clone + std::fmt::Display, S: AsRef<str>>(
        &self,
        db: &VesFileDatabase<N, S>,
    ) -> String {
        let rows = if db.name(self.file_id).is_ok() {
            vec![
                format!("Script: {}", db.name(self.file_id).unwrap()),
                format!("Hash:   {}", db.hash(self.file_id).to_hex()),
            ]
        } else {
            vec![
                "Script: <source>".to_string(),
                "Hash:   <missing hash>".to_string(),
            ]
        };
        let root = plain_msgbox::generate_with_caption(&rows, "program");
        format!(
            "{}\n{}",
            root,
            self.body
                .iter()
                .map(|stmt| stmt.ast_to_str())
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

/// The possible binary operators.
#[derive(Clone, PartialEq, Debug, Copy)]
pub enum BinOpKind {
    /// The `is` operator (type checking)
    Is,
    /// The `in` operator (field/item existence checking).
    In,
    /// The `+` operator (addition)
    Add,
    /// The `-` operator (subtraction)
    Sub,
    /// The `*` operator (multiplication)
    Mul,
    /// The `/` operator (division)
    Div,
    /// The `%` operator (modulus)
    Rem,
    /// The `**` operator (exponentiation)
    Pow,
    /// The `&&` operator (logical and)
    And,
    /// The `||` operator (logical or)
    Or,
    /// The `==` operator (equality)
    Eq,
    /// The `!=` operator (not equal to)
    Ne,
    /// The `<` operator (less than)
    Lt,
    /// The `<=` operator (less than or equal to)
    Le,
    /// The `>=` operator (greater than or equal to)
    Ge,
    /// The `>` operator (greater than)
    Gt,
}

/// The possible unary operators.
#[derive(Clone, PartialEq, Debug, Copy)]
pub enum UnOpKind {
    /// The `!` operator for logical inversion
    Not,
    /// The `-` operator for negation
    Neg,
    /// The `try` operator for error propagation.
    Try,
    /// The `ok` operator for marking values as `Ok`.
    Ok,
    /// The `err` operator for marking values as `Err`.
    Err,
}

/// Represents the value of a literal.
#[derive(Clone, PartialEq, AstToStr)]
pub enum LitValue<'a> {
    /// A 64-bit floating pointer number.
    Number(f64),
    /// A boolean.
    Bool(bool),
    /// A `none` value.
    None,
    /// A utf-8 string.
    Str(Cow<'a, str>),
}

impl<'a> std::fmt::Debug for LitValue<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LitValue::Number(n) => write!(f, "LitValue::Number({:?})", n),
            LitValue::Bool(b) => write!(f, "LitValue::Bool({:?})", b),
            LitValue::None => write!(f, "LitValue::None"),
            LitValue::Str(s) => write!(f, "LitValue::Str({:?})", s),
        }
    }
}

impl<'a> LitValue<'a> {
    pub fn into_string(self) -> Cow<'a, str> {
        match self {
            LitValue::Str(v) => v,
            _ => panic!("Cannot convert the literal into a string: {:?}", self),
        }
    }
}

/// Contains a literal and its token.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct Lit<'a> {
    /// The token that produced the literal.
    pub token: Token<'a>,
    /// The value of the literal.
    #[debug]
    pub value: LitValue<'a>,
}

/// A property access expression.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct GetProp<'a> {
    /// The expression to access the field on, e.g. a struct instance.
    pub node: Expr<'a>,
    /// The field to access.
    pub field: Token<'a>,
    /// Whether this access is part of an optional chain, e.g. `obj.prop?`.
    pub is_optional: bool,
}

/// A property assignment expression.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct SetProp<'a> {
    /// The object to assign the property on.
    pub node: Expr<'a>,
    /// The property to assign to.
    pub field: Token<'a>,
    /// The value to assign.
    pub value: Expr<'a>,
}

/// An item access expression, e.g. `obj[key]`.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct GetItem<'a> {
    /// The object to key.
    pub node: Expr<'a>,
    /// The key to use for the access.
    pub key: Expr<'a>,
}

/// An item assignment expression, e.g. `obj[key] = value`.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct SetItem<'a> {
    /// The object to assign on.
    pub node: Expr<'a>,
    /// The key to assign to.
    pub key: Expr<'a>,
    /// The value to assign.
    pub value: Expr<'a>,
}

/// A fragment of an interpolated string.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub enum FStringFrag<'a> {
    /// A string literal fragment.
    Str(Lit<'a>),
    /// An expression fragment.
    Expr(Expr<'a>),
}

/// An interpolated string literal.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct FString<'a> {
    /// The fragments of an interpolated string.
    pub fragments: Vec<FStringFrag<'a>>,
}

/// The kind of a prefix or postfix increment or decrement.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum IncDecKind {
    /// A `++`.
    Increment,
    /// A `--`.
    Decrement,
}

impl From<TokenKind<'_>> for IncDecKind {
    fn from(kind: TokenKind<'_>) -> Self {
        match kind {
            TokenKind::Increment => IncDecKind::Increment,
            TokenKind::Decrement => IncDecKind::Decrement,
            rest => unreachable!("Attempted to convert a wrong TokenKind into an increment or decrement operator: {:?}", rest),
        }
    }
}

/// An increment or decrement expression.
/// May operate only on variables, struct fields, and item accesses.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct IncDec<'a> {
    /// The expression to increment or decrement.
    pub expr: Expr<'a>,
    #[debug]
    /// The operation to perform.
    pub kind: IncDecKind,
}

/// A variable assignment expression.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct Assignment<'a> {
    /// The name of the variable to assign to.
    pub name: Token<'a>,
    /// The value to assign.
    pub value: Expr<'a>,
}

// TODO: tag tuples with `#[rename]`s
/// The possible parameters a function (or struct, excluding `rest`) can take.
#[derive(Default, Debug, Clone, PartialEq, AstToStr)]
pub struct Params<'a> {
    /// The positional arguments to this function / struct.
    pub positional: Vec<(Token<'a>, bool)>,
    /// The default arguments to this function / struct.
    pub default: Vec<(Token<'a>, Expr<'a>, bool)>,
    /// The rest argument to this function.
    pub rest: Option<Token<'a>>,
}

impl<'a> Params<'a> {
    pub fn is_empty(&self) -> bool {
        self.positional.is_empty() && self.default.is_empty() && self.rest.is_none()
    }

    pub fn is_instance_method_params(&self) -> bool {
        !self.is_empty() && self.positional[0].0.lexeme == "self"
    }
}

/// The possible kinds of a function.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum FnKind {
    /// A regular function.
    /// Example: `fn test() => 3`
    Function,
    /// A struct method.
    /// Example: `method(self) { return self; }`
    Method,
    /// A static method.
    /// Example: `pi() { return 3.141592; }`
    Static,
    /// An initializer block.
    /// Example: `init { print self.a; }`
    Initializer,
}

/// A function or  method declaration.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct FnInfo<'a> {
    /// The name of the function (auto-generated for lambdas).
    pub name: Token<'a>,
    /// The parameters this function defines.
    pub params: Params<'a>,
    /// The body of the function.
    pub body: Vec<Stmt<'a>>,
    #[debug]
    /// The kind of the function.
    pub kind: FnKind,
}

impl<'a> FnInfo<'a> {
    /// Returns `true` if the function is an instance or type method.
    #[inline]
    pub fn is_method(&self) -> bool {
        match self.kind {
            FnKind::Function => false,
            FnKind::Initializer | FnKind::Method | FnKind::Static => true,
        }
    }
}

/// The initializer block of a struct.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct Initializer<'a> {
    /// The body of the initializer.
    pub body: FnInfo<'a>,
    /// Whether the initializer is doing any suspicious operations
    /// that may lead to the struct escaping.
    /// NOTE: This field isn't currently used.
    pub may_escape: bool,
}

impl<'a> Initializer<'a> {
    /// Creates a new [`Initializer`] instance.
    pub fn new(body: FnInfo<'a>) -> Self {
        Self {
            body,
            may_escape: true,
        }
    }
}

/// The static properties of a struct.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct StructStaticProps<'a> {
    /// The static fields of the struct.
    pub fields: Vec<(Token<'a>, Option<Expr<'a>>)>,
    /// The static methods of the struct.
    pub methods: Vec<FnInfo<'a>>,
}

/// A struct declaration statement or expression.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct StructInfo<'a> {
    /// The name of the struct (auto generated for anonymous structs).
    pub name: Token<'a>,
    /// The fields defined on this struct.
    pub fields: Option<Params<'a>>,
    /// The methods defined on this struct.
    pub methods: Vec<FnInfo<'a>>,
    /// THe initializer block of this struct.
    pub initializer: Option<Initializer<'a>>,
    /// The static fields and methods defined on this struct.
    pub r#static: StructStaticProps<'a>,
}

/// A possible condition pattern.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub enum ConditionPattern<'a> {
    /// The value of the condition itself.
    Value,
    /// Whether the condition is `ok` plus a binding for the inner value.
    IsOk(#[rename = "binding"] Token<'a>),
    /// Whether the condition is `err` plus a binding for the inner value.
    IsErr(#[rename = "binding"] Token<'a>),
}

/// A condition of an if statement, while loop, or for loop.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct Condition<'a> {
    /// The value of the condition.
    pub value: Expr<'a>,
    /// The pattern of the condition. If the pattern is [`ConditionPattern::Value`], a simple
    /// truthiness check is performed.
    pub pattern: ConditionPattern<'a>,
}

/// An if statement.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct If<'a> {
    /// The if condition.
    pub condition: Condition<'a>,
    /// The code to execute if the condition is true.
    pub then: DoBlock<'a>,
    /// The code to execute if the condition is false.
    pub otherwise: Option<DoBlock<'a>>,
}

/// A `do` block.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct DoBlock<'a> {
    /// The statements in the do block.
    pub statements: Vec<Stmt<'a>>,
    /// The resulting value of the do block.
    pub value: Option<Expr<'a>>,
}

/// A function call or struct constructor.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct Call<'a> {
    /// The function or struct being called.
    pub callee: Expr<'a>,
    /// The arg passed to the call.
    pub args: Args<'a>,
    /// Whether the call can be compiled as tail call.
    pub tco: bool,
    // Whether the call has forwarded arguments
    pub rest: bool,
}

/// The range of a for loop.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct Range<'a> {
    /// The start of the range (value before the `..`).
    pub start: Expr<'a>,
    /// The end of the range (value before the `..`).
    pub end: Expr<'a>,
    /// The step of the range.
    pub step: Expr<'a>,
    /// Whether the range is inclusive (`..=`) or exclusive (`..`).
    pub inclusive: bool,
}

/// The entry inside of a map literal.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub enum MapEntry<'a> {
    /// A key-value pair.
    Pair(#[rename = "key"] Expr<'a>, #[rename = "value"] Expr<'a>),
    /// A spread expression.
    Spread(#[rename = "target"] Expr<'a>),
}

/// The kind of an expression.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub enum ExprKind<'a> {
    /// A struct declaration.
    Struct(#[forward] Ptr<StructInfo<'a>>),
    ///A function declaration.
    Fn(#[forward] Ptr<FnInfo<'a>>),
    /// An if expression.
    If(#[forward] Ptr<If<'a>>),
    /// A `do` block.
    DoBlock(#[forward] Ptr<DoBlock<'a>>),
    /// A binary operator, e.g. `a + b`
    Binary(
        #[debug]
        #[rename = "op"]
        BinOp,
        #[rename = "left"] ExprPtr<'a>,
        #[rename = "right"] ExprPtr<'a>,
    ),
    /// A unary operator,e e.g. `!a` or `try call()`
    Unary(
        #[debug]
        #[rename = "op"]
        UnOp,
        #[rename = "operand"] ExprPtr<'a>,
    ),
    /// A literal, e.g. a number, a string or an array
    Lit(#[forward] Ptr<Lit<'a>>),
    /// A C++-like comma operator
    Comma(#[rename = "operands"] Vec<Expr<'a>>),
    /// A function call or struct constructor.
    Call(#[forward] Ptr<Call<'a>>),
    /// A spread expression, e.g. `...arr`.
    Spread(#[rename = "value"] ExprPtr<'a>),
    /// A property access expression, e.g. `a.b` and `c?.d`.
    GetProp(#[forward] Ptr<GetProp<'a>>),
    /// A property assignment expression, e.g. `a.b = c`
    SetProp(#[forward] Ptr<SetProp<'a>>),
    /// An item access expression, e.g. `a[0]`.
    GetItem(#[forward] Ptr<GetItem<'a>>),
    /// An item assignment expression, e.g. `a[0] = 3`
    SetItem(#[forward] Ptr<SetItem<'a>>),
    /// A utf-8 string that contains one or more interpolation fragments.
    FString(#[forward] FString<'a>),
    /// An array literal.
    Array(#[rename = "values"] Vec<Expr<'a>>),
    /// A dictionary literal.
    Map(#[rename = "values"] Vec<MapEntry<'a>>),
    /// A variable access expression (includes self).
    Variable(#[rename = "name"] Token<'a>),
    /// A range specified, e.g. `0..10` or `start..end, -2`.
    Range(#[forward] Ptr<Range<'a>>),
    /// A prefix increment or decrement
    PrefixIncDec(#[rename = "inner"] Ptr<IncDec<'a>>),
    /// A postfix increment or decrement
    PostfixIncDec(#[rename = "inner"] Ptr<IncDec<'a>>),
    /// An assignment expression
    Assignment(#[forward] Ptr<Assignment<'a>>),
    /// A grouping expression, e.g. `(a + b)`.
    Grouping(#[rename = "inner"] ExprPtr<'a>),
    /// An "at identifier", e.g. `@outer`
    AtIdent(#[rename = "name"] Token<'a>),
}

/// An expression.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct Expr<'a> {
    #[forward]
    /// The kind of the expression.
    pub kind: ExprKind<'a>,
    /// The span of the entire expression.
    pub span: Span,
}

/// The kind of a variable declaration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VarKind {
    /// An immutable `let` variable.
    Let,
    /// A mutable `mut` variable.
    Mut,
    /// A function declaration.
    Fn,
    /// A struct declaration.
    Struct,
}

/// A variable declaration statement.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct Var<'a> {
    /// The name of the variable being declared.
    pub name: Token<'a>,
    #[debug]
    /// The kind of the variable.
    pub kind: VarKind,
    /// The initial value of the variable.
    pub initializer: Option<Expr<'a>>,
    /// The number of uses this variable has.
    #[callback(|c: &std::rc::Rc<Cell<usize>>| c.get())]
    pub n_uses: std::rc::Rc<Cell<usize>>,
}

/// A loop statement.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct Loop<'a> {
    /// The body of the loop.
    pub body: Stmt<'a>,
    /// The loop label for this loop.
    pub label: Option<Token<'a>>,
}

/// A for loop statement.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct For<'a> {
    /// The list of the loop initializers.
    pub initializers: Vec<Assignment<'a>>,
    /// The loop condition.
    pub condition: Option<Expr<'a>>,
    /// The loop update expression.
    pub increment: Option<Expr<'a>>,
    /// The body of the loop.
    pub body: Stmt<'a>,
    /// The loop label for this loop.
    pub label: Option<Token<'a>>,
}

/// A foreach loop statement, e.g. `for a in 0..10 {}`
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct ForEach<'a> {
    /// The variable to bind the elements to.
    pub variable: Token<'a>,
    /// The iterator to iterate over.
    pub iterator: Expr<'a>,
    /// The loop body.
    pub body: Stmt<'a>,
    /// The loop label for this loop.
    pub label: Option<Token<'a>>,
}

/// A while loop statement, e.g. `while true {}`
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct While<'a> {
    /// The condition of the loop.
    pub condition: Condition<'a>,
    /// The loop body.
    pub body: Stmt<'a>,
    /// The loop label for this loop.
    pub label: Option<Token<'a>>,
}

/// A statement kind.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub enum StmtKind<'a> {
    /// One or more variable declarations, e.g. `let a, b = 3, c`.
    /// All variables are guaranteed to be either all const or all non-const.
    Var(#[rename = "declarations"] Vec<Var<'a>>),
    /// A loop statement.
    Loop(#[forward] Ptr<Loop<'a>>),
    /// A for loop statement.
    For(#[forward] Ptr<For<'a>>),
    /// A foreach loop statement.
    ForEach(#[forward] Ptr<ForEach<'a>>),
    /// A while loop statement.
    While(#[forward] Ptr<While<'a>>),
    /// A block statement.
    Block(#[rename = "statements"] Vec<Stmt<'a>>),
    /// An expression statement.
    ExprStmt(#[rename = "expr"] ExprPtr<'a>),
    /// A print statement.
    Print(#[rename = "value"] ExprPtr<'a>),
    /// A return statement.
    Return(#[rename = "return_value"] Option<ExprPtr<'a>>),
    /// A break statement.
    Break(#[rename = "label"] Option<Token<'a>>),
    /// A continue statement.
    Continue(#[rename = "label"] Option<Token<'a>>),
    /// A `defer` statement. Must store only `Call` expressions.
    Defer(#[rename = "call"] Ptr<Expr<'a>>),
    /// An empty node that compiles to nothing.
    /// Used by the constant folder to remove dead code.
    _Empty,
}

/// A Ves statement.
#[derive(Debug, Clone, PartialEq, AstToStr)]
pub struct Stmt<'a> {
    #[forward]
    /// The kind of the statement.
    pub kind: StmtKind<'a>,
    /// The span of the whole statement.
    pub span: Span,
}

impl<'a> Stmt<'a> {
    /// Wraps the statement in a block if it's not already one.
    pub fn into_block(self) -> Stmt<'a> {
        match self.kind {
            StmtKind::Block(_) => self,
            _ => Stmt {
                span: self.span.clone(),
                kind: StmtKind::Block(vec![self]),
            },
        }
    }

    /// Creates an empty statement node with a synthetic span.
    pub fn empty() -> Self {
        Self {
            kind: StmtKind::_Empty,
            span: usize::MAX..usize::MAX,
        }
    }
}

impl<'a> ExprKind<'a> {
    pub fn call(callee: Expr<'a>, args: Args<'a>, rest: bool) -> Self {
        Self::Call(box Call {
            callee,
            args,
            tco: false,
            rest,
        })
    }
}

impl<'a> LitValue<'a> {
    pub fn is_truthy(&self) -> bool {
        match self {
            LitValue::Number(_) => !self.is_zero(),
            LitValue::Bool(b) => *b,
            LitValue::None => false,
            LitValue::Str(_) => true,
        }
    }

    pub fn is_number(&self) -> bool {
        matches!(self, LitValue::Number(_))
    }

    pub fn is_boolean(&self) -> bool {
        matches!(self, LitValue::Bool(_))
    }

    pub fn is_zero(&self) -> bool {
        if let LitValue::Number(n) = self {
            *n == 0.0
        } else {
            false
        }
    }
}

#[macro_export]
macro_rules! gen_from_for_enum {
    ($T:ty, $Enum:path, $variant:ident) => {
        impl<'a> From<$T> for $Enum {
            fn from(v: $T) -> Self {
                Self::$variant(v)
            }
        }
    };
}

gen_from_for_enum!(f64, LitValue<'a>, Number);
gen_from_for_enum!(bool, LitValue<'a>, Bool);
gen_from_for_enum!(Cow<'a, str>, LitValue<'a>, Str);

#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_ast_printing() {
        let mut db = VesFileDatabase::default();
        let id = db.add_file(
            "test".into(),
            r#"do { 
            try api_method()
        }"#,
        );
        let span = Span { start: 0, end: 1 };
        let ast = AST::new(
            vec![Stmt {
                kind: StmtKind::ExprStmt(box Expr {
                    kind: ExprKind::DoBlock(box DoBlock {
                        statements: vec![],
                        value: Some(Expr {
                            kind: ExprKind::Unary(
                                UnOpKind::Try,
                                box Expr {
                                    kind: ExprKind::Call(box Call {
                                        callee: Expr {
                                            kind: ExprKind::Variable(Token::new(
                                                "api_method",
                                                span.clone(),
                                                TokenKind::Identifier,
                                            )),
                                            span: span.clone(),
                                        },
                                        args: vec![],
                                        tco: false,
                                        rest: false,
                                    }),
                                    span: span.clone(),
                                },
                            ),
                            span: span.clone(),
                        }),
                    }),
                    span: span.clone(),
                }),
                span,
            }],
            id,
        );
        println!("{}", ast.to_str_with_db(&db));
        assert_eq!(
            ast.to_str_with_db(&db),
            r#"╭──────────────────────────╮
│ Script: test             │
│ Hash:   e6427151da26e8b2 │
<program>──────────────────╯
StmtKind::ExprStmt
╰─expr: DoBlock
  ├─statements=✕
  ╰─value: ExprKind::Unary
    ├─op: Try
    ╰─operand: Call
      ├─callee: ExprKind::Variable
      │ ╰─name: "api_method"
      ├─args=✕
      ├─tco: false
      ╰─rest: false"#
        );
    }
}
