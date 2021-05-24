pub mod db;
pub mod diagnostics;

pub use codespan_reporting::files::Files;
pub use db::FileId;
pub use db::VesFileDatabase;

pub type Span = std::ops::Range<usize>;

/// A context for errors, warnings, and suggestions.
#[derive(Debug, Clone)]
pub struct ErrCtx {
    /// The list of the errors that have been recorded so far.
    pub errors: Vec<VesError>,
    /// The list of the warnings that have been issued so far.
    pub warnings: Vec<VesError>,
    /// The local file id for the errors in this context. This isn't used in any way internally.
    /// [`FileId::anon()`] by default.
    pub local_file_id: FileId,
}

impl ErrCtx {
    /// Creates a new error context
    pub fn new() -> ErrCtx {
        ErrCtx {
            local_file_id: FileId::anon(),
            errors: vec![],
            warnings: vec![],
        }
    }

    /// Creates a new error [`ErrCtx`] and record the given error.
    pub fn with_error(e: VesError) -> Self {
        let mut this = Self::new();
        this.record(e);
        this
    }

    /// Adds a new error or warning to the context.
    pub fn record(&mut self, e: VesError) {
        if e.kind == VesErrorKind::Warning {
            self.warnings.push(e)
        } else {
            self.errors.push(e)
        }
    }

    /// Moves all errors from the given context to this context.
    pub fn extend(&mut self, other: ErrCtx) {
        self.errors.extend(other.errors);
        self.warnings.extend(other.warnings);
    }

    /// Moves all errors from the given results into this context.
    pub fn extend_result(&mut self, res: Result<Self, Self>) {
        self.extend(match res {
            Ok(ex) => ex,
            Err(ex) => ex,
        });
    }

    /// Marks the last error in the errors list as a warning and moves it to the warnings list.
    pub fn mark_last_error_as_warning(&mut self) -> Option<()> {
        if let Some(e) = self.errors.pop() {
            self.warnings.push(e);
            Some(())
        } else {
            None
        }
    }

    /// Returns `true` if the context has at least one error.
    #[inline]
    pub fn had_error(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Returns `true` if the context has at least one warning.
    #[inline]
    pub fn had_warning(&self) -> bool {
        !self.warnings.is_empty()
    }
}

impl Default for ErrCtx {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum VesErrorKind {
    /// Represents a lex error.
    Lex,
    /// Represents a parse error.
    Parse,
    /// Represents an error during bytecode emit.
    Emit,
    /// Represents a resolution error.
    Resolution,
    /// Represents a resolution error that suggests to use a wildcard as a variable name.
    ResolutionSuggestWildcard,
    /// An attempt to use the `fn` keyword before a method declaration.
    FnBeforeMethod,
    /// An attempt to reassign to a `let` variable.
    LetReassignment,
    /// An attempt to assign to an optional access.
    OptionalAccessAssignment,
    /// An unused local variable.
    UnusedLocal,
    /// An unknown magic method or invalid magic method params
    BadMagicMethod,
    /// An error issued when the user attempts to shadow a local variable.
    AttemptedToShadowLocalVariable(Span),
    /// Attempted to use a global variable before its declaration.
    UsedGlobalBeforeDeclaration(Span),
    /// Attempted to shadow a struct field with a method.
    ShadowedField(Span),
    /// Attempted to access an unknown property inside a struct method.
    UnknownProperty { suggestion: Option<Span> },
    /// A module import error.
    Import,
    /// A `let` variable without an initializer
    LetWithoutValue,
    /// Represents an error that has occurred at runtime.
    Runtime,
    /// A runtime panic.
    Panic,
    /// Represents a warning that doesn't prevent the program from running.
    Warning,
    /// Represents a part of a traceback.
    Traceback,
}

/// A ves error. Contains the span, message, and source file id.
#[derive(Debug, Clone, PartialEq)]
pub struct VesError {
    /// The span of the error as a byte range in the source code.
    pub span: Span,
    /// The name of the function the error originates from.
    pub function: Option<String>,
    /// The error message.
    pub msg: String,
    /// The kind of the error.
    pub kind: VesErrorKind,
    /// The id of the source file this error comes from.
    pub file_id: FileId,
}

impl VesError {
    /// Creates a new error with the given data.
    pub fn new<S: Into<String>>(msg: S, span: Span, kind: VesErrorKind, file_id: FileId) -> Self {
        VesError {
            msg: msg.into(),
            function: None,
            span,
            kind,
            file_id,
        }
    }

    /// Creates a new [`VesErrorKind::Lex`] error.
    pub fn lex<S: Into<String>>(msg: S, span: Span, file_id: FileId) -> Self {
        VesError::new(msg, span, VesErrorKind::Lex, file_id)
    }

    /// Creates a new [`VesErrorKind::Parse`] error.
    pub fn parse<S: Into<String>>(msg: S, span: Span, file_id: FileId) -> Self {
        VesError::new(msg, span, VesErrorKind::Parse, file_id)
    }

    /// Creates a new [`VesErrorKind::Emit`] error.
    pub fn emit<S: Into<String>>(msg: S, span: Span, file_id: FileId) -> Self {
        VesError::new(msg, span, VesErrorKind::Emit, file_id)
    }

    /// Creates a new [`VesErrorKind::LetWithoutValue`] error.
    pub fn let_without_value<S: Into<String>>(msg: S, span: Span, file_id: FileId) -> Self {
        VesError::new(msg, span, VesErrorKind::LetWithoutValue, file_id)
    }

    /// Creates a new [`VesErrorKind::Resolution`] error.
    pub fn resolution<S: Into<String>>(msg: S, span: Span, file_id: FileId) -> Self {
        VesError::new(msg, span, VesErrorKind::Resolution, file_id)
    }

    /// Creates a new [`VesErrorKind::ResolutionSuggestWildcard`] error.
    pub fn resolution_wildcard<S: Into<String>>(msg: S, span: Span, file_id: FileId) -> Self {
        VesError::new(msg, span, VesErrorKind::ResolutionSuggestWildcard, file_id)
    }

    /// Creates a new [`VesErrorKind::Import`] error.
    pub fn import<S: Into<String>>(msg: S, span: Span, file_id: FileId) -> Self {
        VesError::new(msg, span, VesErrorKind::Import, file_id)
    }

    /// Creates a new [`VesErrorKind::RUntime`] error.
    pub fn runtime<S: Into<String>>(msg: S, span: Span, file_id: FileId) -> Self {
        VesError::new(msg, span, VesErrorKind::Runtime, file_id)
    }

    /// Adds the name of the function the error originates from to this error.
    pub fn with_function<S: Into<String>>(self, function: S) -> Self {
        Self {
            function: Some(function.into()),
            ..self
        }
    }
}

#[cfg(test)]
mod tests {
    use pretty_assertions::assert_eq;

    use super::*;
    use crate::db::VesFileDatabase;

    #[test]
    fn test_resolution_wildcard_diagnostic() {
        let source = r#"
fn test() {
    mut lol_no_type_system = 75
}
"#;
        let mut db = VesFileDatabase::default();
        let id = db.add_snippet(source);
        let error = VesError::resolution_wildcard(
            "Variable `lol_no_type_system` is never used",
            21..39,
            id,
        )
        .with_function("test");

        let result = db.report_one_to_string(&error).unwrap();
        assert_eq!(
            result,
            r#"error[ in test() ]: Variable `lol_no_type_system` is never used
  ┌─ <source: #4c49791bbec20ffa>:3:9
  │
3 │     mut lol_no_type_system = 75
  │         ^^^^^^^^^^^^^^^^^^
  │         │
  │         help: if this is intentional, replace or prefix it with an underscore: `_lol_no_type_system`

"#
        );
    }
}
