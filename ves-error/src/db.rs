use std::{borrow::Cow, cell::Cell, collections::HashMap, path::PathBuf};

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
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(usize);

impl FileId {
    /// Returns a special file id indicating the absence of a file.
    pub const fn anon() -> Self {
        FileId(usize::MAX)
    }
}

/// A ves source code file.
#[derive(Debug, Clone)]
pub struct VesFile<S: AsRef<str>> {
    /// The source of the file
    source: S,
    /// The BLAKE hash of the source file.
    hash: blake2s_simd::Hash,
    /// The name of the module.
    module: String,
    /// Whether the module has already been parsed.
    parsed: Cell<bool>,
}

impl<S: AsRef<str>> VesFile<S> {
    /// Get a reference to the ves file's source.
    pub fn source(&self) -> &S {
        &self.source
    }
}

impl<S: AsRef<str>> AsRef<str> for VesFile<S> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.source.as_ref()
    }
}

/// A database of the currently active Ves source code files.
/// Used for error reporting.
#[derive(Debug)]
pub struct VesFileDatabase<N: AsRef<str>, S: AsRef<str>> {
    db: SimpleFiles<N, VesFile<S>>,
    name_to_id: HashMap<String, FileId>,
    config: Config,
}

impl<N: AsRef<str> + std::fmt::Display + Clone, S: AsRef<str>> VesFileDatabase<N, S> {
    /// Creates a new file database.
    pub fn new() -> Self {
        Self {
            db: SimpleFiles::new(),
            name_to_id: HashMap::new(),
            config: Config::default(),
        }
    }

    /// Adds the given config to the database.
    pub fn with_config(self, config: Config) -> Self {
        Self { config, ..self }
    }

    /// Clones the database, returning a copy where every name and file is an owned [`String`].
    pub fn clone_owned(&mut self) -> VesFileDatabase<String, String> {
        let mut db = VesFileDatabase {
            config: self.config.clone(),
            db: SimpleFiles::new(),
            name_to_id: self.name_to_id.clone(),
        };

        let mut ids = self.name_to_id.values().copied().collect::<Vec<_>>();
        ids.sort();

        for id in ids {
            let file = self.file(id).unwrap();
            let new_file = VesFile {
                source: file.source.as_ref().to_owned(),
                hash: file.hash,
                module: file.module.clone(),
                parsed: file.parsed.clone(),
            };

            let name = self.name(id).unwrap().clone();
            db.db.add(name.as_ref().to_string(), new_file);
        }

        db
    }

    /// Adds a new file to the database.
    pub fn add_file(&mut self, name: N, source: S) -> FileId {
        let hash = hash(source.as_ref());
        let file = VesFile {
            source,
            hash,
            module: extract_module_name(&PathBuf::from(name.as_ref())),
            parsed: Cell::new(false),
        };
        self.add(name, file)
    }

    /// Adds a snippet that doesn't come from a file to the database, using
    /// the hash of the file as its name.
    pub fn add_snippet(&mut self, source: S) -> FileId
    where
        N: From<String>,
    {
        self.add_snippet_map(source, N::from)
    }

    /// Adds a snippet that doesn't come from a file to the database, using
    /// the hash of the file as its name. The given factory function may be used to transform the value and return
    /// an object of type [`N`].
    pub fn add_snippet_map(&mut self, source: S, factory: impl Fn(String) -> N) -> FileId {
        let hash = hash(source.as_ref());
        let name = factory(format!("<source: #{}>", &hash.to_hex()));
        let file = VesFile {
            source,
            hash,
            module: hash.to_hex().to_string(),
            parsed: Cell::new(false),
        };
        self.add(name, file)
    }

    /// Adds the file with the given name to the database.
    fn add(&mut self, name: N, file: VesFile<S>) -> FileId {
        let cloned = name.as_ref().to_string();
        let id = FileId(self.db.add(name, file));
        self.name_to_id.insert(cloned, id);
        id
    }

    /// Returns the id of the file with the given name if it exists.
    #[inline]
    pub fn get_id_by_name(&self, name: &str) -> Option<FileId> {
        self.name_to_id.get(name).copied()
    }

    /// Marks the given file as parsed.
    #[inline]
    pub fn mark_parsed(&self, file_id: FileId) -> Option<()> {
        self.file(file_id).map(|f| {
            f.parsed.set(true);
        })
    }

    /// Returns [`Some(parsed)`] if the file is in the database, [`None`] otherwise.
    #[inline]
    pub fn is_parsed(&self, file_id: FileId) -> Option<bool> {
        self.file(file_id).map(|f| f.parsed.get())
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
    pub fn hash(&self, id: FileId) -> &blake2s_simd::Hash {
        &self
            .db
            .get(id.0)
            .expect("Attempted to query a nonexistent file")
            .source()
            .hash
    }

    /// Returns a reference to the inner file object given a file id.
    #[inline]
    pub fn file(&self, id: FileId) -> Option<&VesFile<S>> {
        self.db.get(id.0).map(|f| f.source()).ok()
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

impl<'a, N: AsRef<str> + std::fmt::Display + Clone + 'a, S: AsRef<str> + 'a> files::Files<'a>
    for VesFileDatabase<N, S>
{
    type FileId = FileId;
    type Name = N;
    type Source = &'a str;

    #[inline]
    fn name(&'a self, id: Self::FileId) -> Result<Self::Name, files::Error> {
        self.db.name(id.0)
    }

    #[inline]
    fn source(&'a self, id: Self::FileId) -> Result<Self::Source, files::Error> {
        check_fid!(id);
        self.db.source(id.0)
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

impl<'a, 'b> Default for VesFileDatabase<Cow<'a, str>, &'b str> {
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

/// Extracts the name of the module from the given path.
fn extract_module_name(path: &std::path::Path) -> String {
    let path = PathBuf::from(path.to_string_lossy().replace('\\', "/"));
    path.file_stem()
        .expect("Attempted to read a path without a filename")
        .to_string_lossy()
        .into_owned()
}

#[cfg(test)]
pub mod test {
    use super::*;
    use crate::Span;

    #[test]
    fn test_line_queries() {
        let mut db = VesFileDatabase::default();
        let id = db.add_snippet(
            r#"line 1
        line 2
        line 3
        line 4"#,
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

    #[test]
    fn test_module_name_extraction() {
        let paths = vec![
            "test1.ves",
            "../../some-path.ves",
            "another_path.ves",
            "no_extension",
            "<source>",
            "./stuff/-in-/the/middle/of/the/path.ves",
            "/a/linux/path.ves",
            r"C:\a\windows\path.ves",
        ];

        let expected = vec![
            "test1",
            "some-path",
            "another_path",
            "no_extension",
            "<source>",
            "path",
            "path",
            "path",
        ];

        let mut db = VesFileDatabase::default();

        for (path, module) in paths.into_iter().zip(expected.into_iter()) {
            let id = db.add_file(path.into(), "");
            assert_eq!(db.file(id).unwrap().module, module);
        }
    }
}
