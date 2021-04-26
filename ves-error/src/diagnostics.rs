use codespan_reporting::{
    diagnostic::{Diagnostic, Label},
    files::Files,
};

use crate::{
    db::{FileId, VesFileDatabase},
    VesError,
};

/// Creates a new diagnostic message for the given [`VesError`].
pub fn build_diagnostic<'a>(db: &VesFileDatabase<'a>, e: &VesError) -> Diagnostic<FileId> {
    use crate::VesErrorKind::*;

    let base = match &e.kind {
        Lex | Parse | ResolutionSuggestWildcard | OptionalAccessAssignment | LetWithoutValue => {
            Diagnostic::error()
        }
        AttemptedToShadowUnusedLocal(_span) => unimplemented!(),
        UsedGlobalBeforeDeclaration(_span) => unimplemented!(),
        Warning => Diagnostic::warning(),
        Compile => unimplemented!(),
        Resolution => unimplemented!(),
        Runtime => unimplemented!(),
        Panic => unimplemented!(),
        Traceback => unimplemented!(),
    };

    let mut d = base
        .with_message(e.msg.clone())
        .with_labels(vec![Label::primary(e.file_id, e.span.clone())]);

    if e.kind == ResolutionSuggestWildcard {
        d = add_wildcard_label(db, d, &e);
    } else if e.kind == LetWithoutValue {
        d = let_no_value_diag(db, d, &e);
    }

    if let Some(code) = e.function.clone() {
        d.with_code(format!(" in {}() ", code))
    } else {
        d
    }
}

/// Adds a label suggesting to replace or prefix the variable with a underscore.
fn add_wildcard_label<'a>(
    db: &VesFileDatabase<'a>,
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
fn let_no_value_diag<'a>(
    _db: &VesFileDatabase<'a>,
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
