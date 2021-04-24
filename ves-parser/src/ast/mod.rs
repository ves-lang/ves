use std::borrow::Cow;

use ves_error::FileId;

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
        false
    }
}

/// An Abstract Syntax Tree for a Ves source file.
#[derive(Debug, PartialEq)]
pub struct AST<'a> {
    /// The statements in the global scope.
    pub body: Vec<Stmt<'a>>,
    /// The id of the file the AST belongs to.
    pub file_id: FileId,
}

impl<'a> AST<'a> {
    /// Creates a new [`AST`] form the given statements and [`FileId`].
    pub fn new(body: Vec<Stmt<'a>>, file_id: FileId) -> Self {
        Self { body, file_id }
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
#[derive(Debug, Clone, PartialEq)]
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

impl<'a> LitValue<'a> {
    pub fn into_string(self) -> Cow<'a, str> {
        match self {
            LitValue::Str(v) => v,
            _ => panic!("Cannot convert the literal into a string: {:?}", self),
        }
    }
}

/// Contains a literal and its token.
#[derive(Debug, Clone, PartialEq)]
pub struct Lit<'a> {
    /// The token that produced the literal.
    pub token: Token<'a>,
    /// The value of the literal.
    pub value: LitValue<'a>,
}

/// A property access expression.
#[derive(Debug, Clone, PartialEq)]
pub struct GetProp<'a> {
    /// The expression to access the field on, e.g. a struct instance.
    pub node: Expr<'a>,
    /// The field to access.
    pub field: Token<'a>,
    /// Whether this access is part of an optional chain, e.g. `obj.prop?`.
    pub is_optional: bool,
}

/// A property assignment expression.
#[derive(Debug, Clone, PartialEq)]
pub struct SetProp<'a> {
    /// The object to assign the property on.
    pub node: Expr<'a>,
    /// The property to assign to.
    pub field: Token<'a>,
    /// The value to assign.
    pub value: Expr<'a>,
}

/// An item access expression, e.g. `obj[key]`.
#[derive(Debug, Clone, PartialEq)]
pub struct GetItem<'a> {
    /// The object to key.
    pub node: Expr<'a>,
    /// The key to use for the access.
    pub key: Expr<'a>,
}

/// An item assignment expression, e.g. `obj[key] = value`.
#[derive(Debug, Clone, PartialEq)]
pub struct SetItem<'a> {
    /// The object to assign on.
    pub node: Expr<'a>,
    /// The key to assign to.
    pub key: Expr<'a>,
    /// The value to assign.
    pub value: Expr<'a>,
}

/// A fragment of an interpolated string.
#[derive(Debug, Clone, PartialEq)]
pub enum FStringFrag<'a> {
    /// A string literal fragment.
    Str(Lit<'a>),
    /// An expression fragment.
    Expr(Expr<'a>),
}

/// An interpolated string literal.
#[derive(Debug, Clone, PartialEq)]
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

/// An increment or decrement expression.
/// May operate only on variables, struct fields, and item accesses.
#[derive(Debug, Clone, PartialEq)]
pub struct IncDec<'a> {
    /// The expression to increment or decrement.
    pub expr: ExprPtr<'a>,
    /// The operation to perform.
    pub kind: IncDecKind,
}

/// A variable assignment expression.
#[derive(Debug, Clone, PartialEq)]
pub struct Assignment<'a> {
    /// The name of the variable to assign to.
    pub name: Token<'a>,
    /// The value to assign.
    pub value: Expr<'a>,
}

/// The possible parameters a function (or struct, excluding `rest`) can take.
#[derive(Debug, Clone, PartialEq)]
pub struct Params<'a> {
    /// The positional arguments to this function / struct.
    pub positional: Vec<Token<'a>>,
    /// The default arguments to this function / struct.
    pub default: Vec<(Token<'a>, Expr<'a>)>,
    /// The rest argument to this function.
    pub rest: Option<Token<'a>>,
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
}

/// A function or  method declaration.
#[derive(Debug, Clone, PartialEq)]
pub struct FnInfo<'a> {
    /// The name of the function (auto-generated for lambdas).
    pub name: Token<'a>,
    /// The parameters this function defines.
    pub params: Params<'a>,
    /// The body of the function.
    pub body: Vec<Stmt<'a>>,
    /// The kind of the function.
    pub kind: FnKind,
}

impl<'a> FnInfo<'a> {
    /// Returns `true` if the function is an instance or type method.
    #[inline]
    pub fn is_method(&self) -> bool {
        match self.kind {
            FnKind::Function => false,
            FnKind::Method | FnKind::Static => true,
        }
    }
}

/// The initializer block of a struct.
#[derive(Debug, Clone, PartialEq)]
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

/// A struct declaration statement or expression.
#[derive(Debug, Clone, PartialEq)]
pub struct StructInfo<'a> {
    /// The name of the struct (auto generated for anonymous structs).
    pub name: Token<'a>,
    /// The fields defined on this struct.
    pub fields: Vec<Expr<'a>>,
    /// The methods defined on this struct.
    pub methods: Vec<FnInfo<'a>>,
    /// THe initializer block of this struct.
    pub initializer: Option<Initializer<'a>>,
    /// The static fields and methods defined on this struct.
    pub r#static: Box<StructInfo<'a>>,
}

/// A possible condition pattern.
#[derive(Debug, Clone, PartialEq)]
pub enum ConditionPattern<'a> {
    /// The value of the condition itself.
    Value,
    /// Whether the condition is `none`.
    IsNone,
    /// Whether the condition is `ok` plus a binding for the inner value.
    IsOk(Token<'a>),
    /// Whether the condition is `err` plus a binding for the inner value.
    IsErr(Token<'a>),
    /// Whether the condition is `some` plus a binding for the value (some is implicit).
    IsSome(Token<'a>),
}

/// A condition of an if statement, while loop, or for loop.
#[derive(Debug, Clone, PartialEq)]
pub struct Condition<'a> {
    /// The value of the condition.
    pub value: Expr<'a>,
    /// The pattern of the condition. If the pattern is [`ConditionPattern::Value`], a simple
    /// truthiness check is performed.
    pub pattern: ConditionPattern<'a>,
}

/// An if statement.
#[derive(Debug, Clone, PartialEq)]
pub struct If<'a> {
    /// The if condition.
    pub condition: Condition<'a>,
    /// The code to execute if the condition is true.
    pub then: DoBlock<'a>,
    /// The code to execute if the condition is false.
    pub otherwise: Option<DoBlock<'a>>,
}

/// A `do` block.
#[derive(Debug, Clone, PartialEq)]
pub struct DoBlock<'a> {
    /// The statements in the do block.
    statements: Vec<Stmt<'a>>,
    /// The resulting value of the do block.
    value: Option<Expr<'a>>,
}

/// A function call or struct constructor.
#[derive(Debug, Clone, PartialEq)]
pub struct Call<'a> {
    /// The function or struct being called.
    callee: ExprPtr<'a>,
    /// The arg passed to the call.
    args: Args<'a>,
    /// Whether the call can be compiled as tail call.
    tco: bool,
    // Whether the call has forwarded arguments
    rest: bool,
}

/// The range of a for loop.
#[derive(Debug, Clone, PartialEq)]
pub struct Range<'a> {
    /// The start of the range (value before the `..`).
    start: Expr<'a>,
    /// The end of the range (value before the `..`).
    end: Expr<'a>,
    /// The step of the range.
    step: Expr<'a>,
    /// Whether the range is inclusive (`..=`) or exclusive (`..`).
    inclusive: bool,
}

/// The kind of an expression.
#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind<'a> {
    /// A struct declaration.
    Struct(Ptr<StructInfo<'a>>),
    ///A function declaration.
    Fn(Ptr<FnInfo<'a>>),
    /// An if expression.
    If(Ptr<If<'a>>),
    /// A `do` block.
    DoBlock(Ptr<DoBlock<'a>>),
    /// A binary operator, e.g. `a + b`
    Binary(BinOp, ExprPtr<'a>, ExprPtr<'a>),
    /// A unary operator, e.g. `!a` or `try call()`
    Unary(UnOp, ExprPtr<'a>),
    /// A literal, e.g. a number or a string
    Lit(Ptr<Lit<'a>>),
    /// A C++-like comma operator
    Comma(Vec<Expr<'a>>),
    /// A function call or struct constructor.
    Call(Ptr<Call<'a>>),
    /// A spread expression, e.g. `...arr`.
    Spread(ExprPtr<'a>),
    /// A property access expression, e.g. `a.b` and `c?.d`.
    GetProp(Ptr<GetProp<'a>>),
    /// A property assignment expression, e.g. `a.b = c`
    SetProp(Ptr<SetProp<'a>>),
    /// An item access expression, e.g. `a[0]`.
    GetItem(ExprPtr<'a>, ExprPtr<'a>),
    /// An item assignment expression, e.g. `a[0] = 3`
    SetItem(Ptr<SetItem<'a>>),
    /// A utf-8 string that contains one or more interpolation fragments.
    FString(FString<'a>),
    /// An array literal.
    Array(Vec<Expr<'a>>),
    /// A dictionary literal.
    Map(Vec<(Expr<'a>, Expr<'a>)>),
    /// A variable access expression (includes self).
    Variable(Token<'a>),
    /// A range specified, e.g. `0..10` or `start..end, -2`.
    Range(Ptr<Range<'a>>),
    /// A prefix increment or decrement
    PrefixIncDec(Ptr<IncDec<'a>>),
    /// A postfix increment or decrement
    PostfixIncDec(Ptr<IncDec<'a>>),
    /// An assignment expression
    Assignment(Ptr<Assignment<'a>>),
    /// A grouping expression, e.g. `(a + b)`.
    Grouping(ExprPtr<'a>),
    /// A loop label, e.g. `@outer`
    Label(Token<'a>),
}

/// An expression.
#[derive(Debug, Clone, PartialEq)]
pub struct Expr<'a> {
    /// The kind of the expression.
    pub kind: ExprKind<'a>,
    /// The span of the entire expression.
    pub span: Span,
}

/// The kind of a variable declaration.
#[derive(Debug, Clone, PartialEq)]
pub enum VarKind {
    /// An immutable `let` variable.
    Let,
    /// A mutable `mut` variable.
    Mut,
}

/// A variable declaration statement.
#[derive(Debug, Clone, PartialEq)]
pub struct Var<'a> {
    /// The name of the variable being declared.
    pub name: Token<'a>,
    /// The kind of the variable.
    pub kind: VarKind,
    /// The initial value of the variable.
    pub initializer: Option<Expr<'a>>,
}

/// A for loop statement.
#[derive(Debug, Clone, PartialEq)]
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
#[derive(Debug, Clone, PartialEq)]
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

/// A foreach loop statement, e.g. `for a in 0..10 {}`
#[derive(Debug, Clone, PartialEq)]
pub struct While<'a> {
    /// The condition of the loop.
    pub condition: Condition<'a>,
    /// The loop body.
    pub body: Stmt<'a>,
    /// The loop label for this loop.
    pub label: Option<Token<'a>>,
}

/// A statement kind.
#[derive(Debug, Clone, PartialEq)]
pub enum StmtKind<'a> {
    /// One or more variable declarations, e.g. `let a, b = 3, c`.
    /// All variables are guaranteed to be either all const or all non-const.
    Var(Vec<Var<'a>>),
    /// A for loop statement.
    For(Ptr<For<'a>>),
    /// A foreach loop statement.
    ForEach(Ptr<ForEach<'a>>),
    /// A while loop statement.
    While(Ptr<While<'a>>),
    /// A block statement.
    Block(Vec<Stmt<'a>>),
    /// An expression statement.
    ExprStmt(ExprPtr<'a>),
    /// A print statement.
    Print(ExprPtr<'a>),
    /// An if statement.
    If(Ptr<If<'a>>),
    /// A return statement.
    Return(Option<ExprPtr<'a>>),
    /// A break statement.
    Break(Token<'a>),
    /// A continue statement.
    Continue(Token<'a>),
    /// A `defer` statement
    Defer(Ptr<Call<'a>>),
    /// An empty node that compiles to nothing.
    /// Used by the constant folder to remove dead code.
    _Empty,
}

/// A Ves statement.
#[derive(Debug, Clone, PartialEq)]
pub struct Stmt<'a> {
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
}

impl<'a> ExprKind<'a> {
    pub fn call(callee: ExprPtr<'a>, args: Args<'a>, rest: bool) -> Self {
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
