use std::borrow::Cow;

use codespan_reporting::{
    diagnostic::Diagnostic,
    files::{self, Files, SimpleFiles},
    term::{
        termcolor::{ColorChoice, StandardStream, WriteColor},
        Config,
    },
};

use crate::{diagnostics::build_diagnostic, ErrCtx, VesError};

/// The id of a file stored in the database
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FileId(usize);

impl FileId {
    /// Returns a special file id indicating the absence of a file.
    pub const fn anon() -> Self {
        FileId(usize::MAX)
    }
}

/// A ves source code file.
#[derive(Debug, Clone)]
struct VesFile<'a> {
    /// The source of the file
    source: Cow<'a, str>,
    /// The BLAKE hash of the source file.
    hash: blake2s_simd::Hash,
    // TODO: name of the module
    module: (),
}

impl<'a> AsRef<str> for VesFile<'a> {
    #[inline]
    fn as_ref(&self) -> &str {
        &*self.source
    }
}

/// A database of the currently active Ves source code files.
/// Used for error reporting.
#[derive(Debug)]
pub struct VesFileDatabase<'a> {
    db: SimpleFiles<Cow<'a, str>, VesFile<'a>>,
    config: Config,
}

impl<'a> VesFileDatabase<'a> {
    /// Creates a new file database.
    pub fn new() -> Self {
        Self {
            db: SimpleFiles::new(),
            config: Config::default(),
        }
    }

    /// Adds the given config to the database.
    pub fn with_config(self, config: Config) -> Self {
        Self { config, ..self }
    }

    /// Adds a new file to the database.
    pub fn add_file(&mut self, name: Cow<'a, str>, source: Cow<'a, str>) -> FileId {
        let hash = hash(&source);
        let file = VesFile {
            source,
            hash,
            module: (),
        };
        FileId(self.db.add(name, file))
    }

    /// Adds a snippet that doesn't come from a file to the database, using
    /// the hash of the file as its name.
    pub fn add_snippet(&mut self, source: Cow<'a, str>) -> FileId {
        let hash = hash(&source);
        let name = Cow::Owned(format!("<source: #{}>", &hash.to_hex()));
        let file = VesFile {
            source,
            hash,
            module: (),
        };
        FileId(self.db.add(name, file))
    }

    /// Returns a tuple of (line, column) for the given span and file id.
    ///
    /// # Panics
    /// Panics if the given file id is not present in the database.
    pub fn location(&self, id: FileId, span: &crate::Span) -> (usize, usize) {
        let line = self
            .line_index(id, span.start)
            .expect("Attempted to query a nonexistent file.");
        let column = self.column_number(id, line, span.start).unwrap();
        (line + 1, column)
    }

    /// Returns the BLAKE hash of the file with the given id.
    #[inline]
    pub fn hash(&'a self, id: FileId) -> &blake2s_simd::Hash {
        &self
            .db
            .get(id.0)
            .expect("Attempted to query a nonexistent file")
            .source()
            .hash
    }

    /// Reports the errors form the [`ErrCtx`] to STDERR.
    pub fn report(&self, ex: &ErrCtx) -> Result<(), files::Error> {
        let buf = StandardStream::stderr(ColorChoice::Auto);
        self.report_to_buffer(&mut buf.lock(), ex)?;
        Ok(())
    }

    /// Reports a single [`VesError`] to a STDERR.
    pub fn report_one(&self, e: &VesError) -> Result<(), files::Error> {
        let buf = StandardStream::stderr(ColorChoice::Auto);
        self.report_diagnostic(&mut buf.lock(), &build_diagnostic(&self, e))?;
        Ok(())
    }

    /// Reports the errors from the [`ErrCtx`] to a string.
    ///
    /// # Panics
    /// Panics if the diagnostic output isn't valid UTF-8.
    pub fn report_to_string(&self, ex: &ErrCtx) -> Result<String, files::Error> {
        let mut buf = StringBuffer(String::with_capacity(1024)); // preallocate 1kb
        self.report_to_buffer(&mut buf, ex)?;
        Ok(buf.0)
    }

    /// Reports a single [`VesError`] to a string.
    ///
    /// # Panics
    /// Panics if the diagnostic output isn't valid UTF-8.
    pub fn report_one_to_string(&self, e: &VesError) -> Result<String, files::Error> {
        let mut buf = StringBuffer(String::with_capacity(1024)); // preallocate 1kb
        self.report_diagnostic(&mut buf, &build_diagnostic(&self, e))?;
        Ok(buf.0)
    }

    /// Reports the errors from the [`ErrCtx`] to the given buffer.
    pub fn report_to_buffer<W: WriteColor>(
        &self,
        buf: &mut W,
        ex: &ErrCtx,
    ) -> Result<(), files::Error> {
        for d in self.build_diagnostics(ex) {
            self.report_diagnostic(buf, &d)?;
        }
        Ok(())
    }

    /// Reports a single diagnostic to the given buffer.
    fn report_diagnostic<W: WriteColor>(
        &self,
        buf: &mut W,
        d: &Diagnostic<FileId>,
    ) -> Result<(), files::Error> {
        codespan_reporting::term::emit(buf, &self.config, self, d)
    }

    /// Creates an array of diagnostic from the given [`ErrCtx`].
    #[inline]
    fn build_diagnostics(&self, ex: &ErrCtx) -> Vec<Diagnostic<FileId>> {
        ex.errors
            .iter()
            .chain(ex.warnings.iter())
            .map(|e| build_diagnostic(&self, e))
            .collect()
    }
}

/// A wrapper for strings that implements the [`WriteColor`] trait, which also requires implementing [`std::io::Write`].
/// Note that writing invalid UTF-8 will result into a panic.
pub struct StringBuffer(String);

impl std::io::Write for StringBuffer {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0.push_str(
            std::str::from_utf8(buf)
                .expect("Attempted to write a non-utf8 sequence to the wrapped string."),
        );
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

impl WriteColor for StringBuffer {
    fn supports_color(&self) -> bool {
        false
    }

    fn set_color(
        &mut self,
        _spec: &codespan_reporting::term::termcolor::ColorSpec,
    ) -> std::io::Result<()> {
        Ok(())
    }

    fn reset(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

macro_rules! check_fid {
    ($id:expr) => {
        debug_assert!(
            $id != FileId::anon(),
            "Attempted to report a diagnostic on anonymous source file."
        );
    };
}

impl<'a> files::Files<'a> for VesFileDatabase<'a> {
    type FileId = FileId;
    type Name = Cow<'a, str>;
    type Source = Cow<'a, str>;

    #[inline]
    fn name(&'a self, id: Self::FileId) -> Result<Self::Name, files::Error> {
        self.db.name(id.0)
    }

    #[inline]
    fn source(&'a self, id: Self::FileId) -> Result<Self::Source, files::Error> {
        check_fid!(id);
        self.db.source(id.0).map(|s| Cow::Borrowed(s))
    }

    #[inline]
    fn line_index(&'a self, id: Self::FileId, byte_index: usize) -> Result<usize, files::Error> {
        check_fid!(id);
        self.db.line_index(id.0, byte_index)
    }

    #[inline]
    fn line_range(
        &'a self,
        id: Self::FileId,
        line_index: usize,
    ) -> Result<std::ops::Range<usize>, files::Error> {
        check_fid!(id);
        self.db.line_range(id.0, line_index)
    }
}

impl<'a> Default for VesFileDatabase<'a> {
    fn default() -> Self {
        Self::new()
    }
}

/// Computes a 64-bit BLAKE hash of the given source file.
fn hash(source: &str) -> blake2s_simd::Hash {
    blake2s_simd::Params::new()
        .hash_length(8)
        .hash(source.as_bytes())
}

#[cfg(test)]
pub mod test {
    use super::*;
    use crate::Span;

    #[test]
    fn test_line_queries() {
        let mut db = VesFileDatabase::new();
        let id = db.add_snippet(
            r#"line 1
        line 2
        line 3
        line 4"#
                .into(),
        );

        assert_eq!(db.location(id, &Span { start: 0, end: 0 }), (1, 1));
        assert_eq!(db.location(id, &Span { start: 5, end: 10 }), (1, 6));
        assert_eq!(db.location(id, &Span { start: 15, end: 25 }), (2, 9));
        assert_eq!(
            db.location(
                id,
                &Span {
                    start: 1000,
                    end: 3000
                }
            ),
            (4, 15)
        );
    }
}
