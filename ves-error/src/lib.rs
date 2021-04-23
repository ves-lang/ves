use db::FileId;

pub mod db;
pub mod diagnostics;

pub type Span = std::ops::Range<usize>;

/// A context for errors, warnings, and suggestions.
#[derive(Debug, Clone)]
pub struct ErrCtx {
    /// The list of the errors that have occurred so far in this context.
    pub errors: Vec<VesError>,
    /// The list of the warnings that have occurred os far in this context.
    pub warnings: Vec<VesError>,
}

impl ErrCtx {
    /// Adds a new error or warnings to the context.
    pub fn record(&mut self, e: VesError) {
        if e.kind == VesErrorKind::Warning {
            self.warnings.push(e)
        } else {
            self.errors.push(e)
        }
    }

    /// Returns `true` if the error context has at least one error.
    #[inline]
    pub fn had_error(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Returns `true` if the error context has at least one warning.
    #[inline]
    pub fn had_warning(&self) -> bool {
        !self.warnings.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum VesErrorKind {
    /// Represents a lex error.
    Lex,
    /// Represents a parse error.
    Parse,
    /// Represents a compile error.
    Compile,
    /// Represents a resolution error.
    Resolution,
    /// Represents a resolution error that
    /// suggests to use a wildcard as a variable name.
    ResolutionSuggestWildcard,
    /// Represents an error occurred at runtime.
    Runtime,
    /// A runtime panic.
    Panic,
    /// Represents a warning that does not prevent the program from running.
    Warning,
    /// Represents a part of a traceback.
    Traceback,
}

/// A ves error. Contains the span, message, source file id.
#[derive(Debug, Clone)]
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

    /// Creates a new [`VesErrorKind::Resolution`] error.
    pub fn resolution<S: Into<String>>(msg: S, span: Span, file_id: FileId) -> Self {
        VesError::new(msg, span, VesErrorKind::Resolution, file_id)
    }

    /// Creates a new [`VesErrorKind::ResolutionSuggestWildcard`] error.
    pub fn resolution_wildcard<S: Into<String>>(msg: S, span: Span, file_id: FileId) -> Self {
        VesError::new(msg, span, VesErrorKind::ResolutionSuggestWildcard, file_id)
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
        let id = db.add_snippet(source.into());
        let error =
            VesError::resolution_wildcard("Variable `lol_yes_generics` is never used", 21..39, id)
                .with_function("test");

        let result = db.report_one_to_string(&error).unwrap();
        assert_eq!(
            result,
            r#"error[ in test() ]: Variable `lol_yes_generics` is never used
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
