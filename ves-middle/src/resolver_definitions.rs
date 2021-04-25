use ves_parser::{ast::VarKind, Span};

/// The kind of the loop currently being resolved.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum LoopKind {
    None,
    While,
    For,
    ForEach,
}

/// The kind of the scope currently being resolved.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ScopeKind {
    /// The global scope.
    Global,
    /// A local scope (a block or a function).
    Local,
    /// A function scope.
    Function,
    /// An `init` block.
    Initializer,
    /// A static method scope.
    AssocMethod,
    /// A method scope.
    Method,
}

/// The kind of the name currently being resolved.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NameKind {
    /// A mutable variable.
    Mut,
    /// An immutable variable.
    Let,
    /// A function declaration.
    Fn,
    /// A struct declaration
    Struct,
}

impl From<VarKind> for NameKind {
    #[inline]
    fn from(var: VarKind) -> Self {
        match var {
            VarKind::Let => NameKind::Let,
            VarKind::Mut => NameKind::Mut,
        }
    }
}

/// The information about a variable's usage.
#[derive(Debug, Clone)]
pub struct VarUsage {
    /// Whether the variable has been declared.
    pub declared: bool,
    /// Whether the variable has been assigned to after its declaration.
    pub assigned: bool,
    /// Whether the variable has been used.
    pub used: bool,
    /// The kind of the variable. For example, whether it is `mut` or `let`.
    pub kind: NameKind,
    /// The span of the variable; used for error reporting.
    pub span: Span,
}

impl VarUsage {
    /// Returns true if the variable is a `let` or `mut` variable.
    pub fn is_var(&self) -> bool {
        matches!(self.kind, NameKind::Let | NameKind::Mut)
    }

    /// Returns true if variable is `let`.
    pub fn is_let(&self) -> bool {
        matches!(self.kind, NameKind::Let)
    }

    /// Returns true if the variable is `mut`.
    pub fn is_mut(&self) -> bool {
        matches!(self.kind, NameKind::Mut)
    }
}
