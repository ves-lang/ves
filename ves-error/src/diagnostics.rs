use codespan_reporting::{
    diagnostic::{Diagnostic, Label},
    files::Files,
};

use crate::{
    db::{FileId, VesFileDatabase},
    VesError,
};

/// Creates a new diagnostic message for the given [`VesError`].
pub fn build_diagnostic<
    N: AsRef<str> + std::fmt::Display + Clone + std::fmt::Display + Clone,
    S: AsRef<str>,
>(
    db: &VesFileDatabase<N, S>,
    e: &VesError,
) -> Diagnostic<FileId> {
    use crate::VesErrorKind::*;

    let base = match &e.kind {
        Lex
        | Parse
        | Resolution
        | ResolutionSuggestWildcard
        | OptionalAccessAssignment
        | LetWithoutValue
        | LetReassignment
        | FnBeforeMethod
        | UsedGlobalBeforeDeclaration(_)
        | AttemptedToShadowLocalVariable(_)
        | ShadowedField(_)
        | UnknownProperty { .. }
        | Import
        | BadMagicMethod => Diagnostic::error(),
        UnusedLocal => Diagnostic::warning(),
        Warning => Diagnostic::warning(),
        Emit => Diagnostic::error(),
        Runtime => Diagnostic::error(),
        Panic => unimplemented!(),
        Traceback => unimplemented!(),
    };

    let mut d = base
        .with_message(e.msg.clone())
        .with_labels(vec![Label::primary(e.file_id, e.span.clone())]);

    if matches!(e.kind, ResolutionSuggestWildcard | UnusedLocal) {
        d = add_wildcard_label(db, d, &e);
    } else if e.kind == LetWithoutValue {
        d = let_no_value_diag(db, d, &e);
    } else if e.kind == LetReassignment {
        d = let_reassignment_diag(db, d, &e);
    } else if e.kind == FnBeforeMethod {
        d = fn_before_method_diag(db, d, &e);
    } else if let AttemptedToShadowLocalVariable(_) = e.kind {
        d = attempted_to_shadow_unused_diag(db, d, &e);
    } else if let UsedGlobalBeforeDeclaration(_) = e.kind {
        d = used_global_before_declaration_diag(db, d, &e);
    } else if let ShadowedField(_) = e.kind {
        d = shadowed_field_diag(db, d, &e);
    } else if let UnknownProperty { .. } = e.kind {
        d = unknown_property_diag(db, d, &e);
    }

    if let Some(code) = e.function.clone() {
        d.with_code(format!(" in {}() ", code))
    } else {
        d
    }
}

/// Adds a label suggesting to replace or prefix the variable with a underscore.
fn add_wildcard_label<N: AsRef<str> + std::fmt::Display + Clone, S: AsRef<str>>(
    db: &VesFileDatabase<N, S>,
    mut diag: Diagnostic<FileId>,
    e: &VesError,
) -> Diagnostic<FileId> {
    let variable = &db
        .source(e.file_id)
        .map_err(|db_error| {
            format!(
                "Couldn't retrieve the file with id = {:?} from the database: {}",
                e.file_id, db_error
            )
        })
        .unwrap()[e.span.clone()];
    diag.labels.push(
        Label::secondary(e.file_id, e.span.clone()).with_message(format!(
            "help: if this is intentional, replace or prefix it with an underscore: `_{}`",
            variable,
        )),
    );
    diag
}

/// Adds a note explaining the error.
fn let_no_value_diag<N: AsRef<str> + std::fmt::Display + Clone, S: AsRef<str>>(
    _db: &VesFileDatabase<N, S>,
    mut diag: Diagnostic<FileId>,
    e: &VesError,
) -> Diagnostic<FileId> {
    diag.notes
        .push("note: `let` variables cannot be changed so they must have a value".into());
    diag.labels
        .push(Label::secondary(e.file_id, e.span.clone()).with_message(
            "help: consider using `mut` or explicitly initializing the variable with `none`",
        ));
    diag
}

fn let_reassignment_diag<N: AsRef<str> + std::fmt::Display + Clone, S: AsRef<str>>(
    db: &VesFileDatabase<N, S>,
    mut diag: Diagnostic<FileId>,
    e: &VesError,
) -> Diagnostic<FileId> {
    let name = &db.source(e.file_id).unwrap()[e.span.clone()];
    diag.labels.push(
        Label::secondary(e.file_id, e.span.clone()).with_message(format!(
            "Consider marking `{0}` as `mut` to make it mutable: `mut {0}`",
            name
        )),
    );
    diag
}

fn fn_before_method_diag<N: AsRef<str> + std::fmt::Display + Clone, S: AsRef<str>>(
    _db: &VesFileDatabase<N, S>,
    mut diag: Diagnostic<FileId>,
    _e: &VesError,
) -> Diagnostic<FileId> {
    let lbl = diag.labels.pop().unwrap();
    diag.labels.push(Label {
        message: "help: omit the `fn` keyword".into(),
        ..lbl
    });
    diag
}

fn attempted_to_shadow_unused_diag<N: AsRef<str> + std::fmt::Display + Clone, S: AsRef<str>>(
    db: &VesFileDatabase<N, S>,
    mut diag: Diagnostic<FileId>,
    e: &VesError,
) -> Diagnostic<FileId> {
    let first = diag.labels.pop().unwrap();
    let span = match &e.kind {
        crate::VesErrorKind::AttemptedToShadowLocalVariable(span) => span.clone(),
        _ => unreachable!(),
    };
    let line = db.line_index(e.file_id, span.start).unwrap() + 1;
    diag.with_labels(vec![
        first.with_message("Later shadowed here"),
        Label::secondary(e.file_id, span).with_message(format!("First declared on line {}", line)),
    ])
}

fn used_global_before_declaration_diag<N: AsRef<str> + std::fmt::Display + Clone, S: AsRef<str>>(
    db: &VesFileDatabase<N, S>,
    mut diag: Diagnostic<FileId>,
    e: &VesError,
) -> Diagnostic<FileId> {
    let first = diag.labels.pop().unwrap();
    let span = match &e.kind {
        crate::VesErrorKind::UsedGlobalBeforeDeclaration(span) => span.clone(),
        _ => unreachable!(),
    };
    let line = db.line_index(e.file_id, span.start).unwrap() + 1;
    diag.with_labels(vec![
        first,
        Label::secondary(e.file_id, span).with_message(format!("First declared on line {}", line)),
    ])
}

fn shadowed_field_diag<N: AsRef<str> + std::fmt::Display + Clone, S: AsRef<str>>(
    db: &VesFileDatabase<N, S>,
    mut diag: Diagnostic<FileId>,
    e: &VesError,
) -> Diagnostic<FileId> {
    let first = diag.labels.pop().unwrap();
    let span = match &e.kind {
        crate::VesErrorKind::ShadowedField(span) => span.clone(),
        _ => unreachable!(),
    };
    let line = db.line_index(e.file_id, span.start).unwrap() + 1;
    diag.with_labels(vec![
        first,
        Label::secondary(e.file_id, span).with_message(format!("Field declared on line {}", line)),
    ])
}

fn unknown_property_diag<N: AsRef<str> + std::fmt::Display + Clone, S: AsRef<str>>(
    db: &VesFileDatabase<N, S>,
    diag: Diagnostic<FileId>,
    e: &VesError,
) -> Diagnostic<FileId> {
    let suggestion = match &e.kind {
        crate::VesErrorKind::UnknownProperty { suggestion } => suggestion.clone(),
        _ => unreachable!(),
    };
    if let Some(span) = suggestion {
        let name = &db.source(e.file_id).unwrap()[span.clone()];
        diag.with_labels(vec![Label::secondary(e.file_id, span).with_message(
            format!("A property with a similar name exists: `{}`", name),
        )])
    } else {
        diag
    }
}
