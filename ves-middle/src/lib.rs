#![feature(box_syntax, box_patterns, bindings_after_at)]

use std::{marker::PhantomData, path::Path, pin::Pin};

use imports::ImportConfig;
use ves_error::{ErrCtx, FileId, Files, VesFileDatabase};
use ves_parser::ast::AST;
mod macros;

pub mod constant_folder;
pub mod env;
pub mod imports;
pub mod resolver;
mod resolver_definitions;
pub mod ves_path;

/// A fat pointer to a pinned immutable string.
#[derive(Debug, Clone)]
struct PinnedStr<'a>(*const u8, usize, PhantomData<&'a ()>);

impl<'a> PinnedStr<'a> {
    #[inline]
    fn str<'b>(&'b self) -> &'a str {
        unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(self.0, self.1)) }
    }
}

impl<'a> std::fmt::Display for PinnedStr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_ref())
    }
}

impl<'a> std::ops::Deref for PinnedStr<'a> {
    type Target = str;

    fn deref(&self) -> &'_ Self::Target {
        self.str()
    }
}

impl<'a> AsRef<str> for PinnedStr<'a> {
    fn as_ref(&self) -> &'_ str {
        &*self
    }
}

#[derive(Debug)]
pub struct VesMiddle<'path, 'this> {
    sources: Vec<Pin<String>>,
    db: VesFileDatabase<String, PinnedStr<'this>>,
    trees: Vec<AST<'this>>,
    diagnostics: ErrCtx,
    pub(crate) import_config: ImportConfig<'path>,
}

impl<'path, 'this> VesMiddle<'path, 'this> {
    pub fn new(import_config: ImportConfig<'path>) -> Self {
        Self {
            sources: Vec::new(),
            import_config,
            trees: Vec::new(),
            db: VesFileDatabase::new(),
            diagnostics: ErrCtx::new(),
        }
    }

    pub fn process(
        &mut self,
        name: impl Into<String>,
        source: impl Into<String>,
    ) -> Result<&Self, &Self> {
        let name = name.into();
        let source = self.store_string(source.into());
        let id = self.db.add_file(name, source);
        self.resolve_module(id)
    }

    pub fn process_snippet<S: Into<String>>(&mut self, source: S) -> Result<&Self, &Self> {
        let source = self.store_string(source.into());
        let id = self.db.add_snippet(source);
        self.resolve_module(id)
    }

    #[inline]
    pub(crate) fn is_parsed(&self, file_id: FileId) -> bool {
        self.db.is_parsed(file_id).unwrap()
    }

    #[inline]
    pub(crate) fn default_base_path(&self) -> &Path {
        &self.import_config.ves_path.default_base
    }

    #[inline]
    pub(crate) fn name(&self, file_id: FileId) -> String {
        self.db.name(file_id).unwrap()
    }

    #[inline]
    pub(crate) fn id_by_name(&self, name: &str) -> Option<FileId> {
        self.db.get_id_by_name(name)
    }

    pub(crate) fn store(&mut self, name: String, source: String) -> (FileId, &'this str) {
        let name = name;
        let source = self.store_string(source);
        let id = self.db.add_file(name, source.clone());
        (id, source.str())
    }

    pub(crate) fn parse_single(&mut self, file_id: FileId) -> Result<AST<'this>, ErrCtx> {
        let source = self.db.file(file_id).unwrap().source().str();
        ves_parser::Parser::new(ves_parser::Lexer::new(source), file_id, &self.db).parse()
    }

    fn resolve_module(&mut self, id: FileId) -> Result<&Self, &Self> {
        let ast = match self.parse_single(id) {
            Ok(ast) => ast,
            Err(ex) => {
                self.diagnostics.extend(ex);
                return Err(self);
            }
        };

        let trees = match imports::resolve_module_graph(ast, self) {
            Ok((trees, diags)) => {
                self.diagnostics.extend(diags);
                trees
            }
            Err(errors) => {
                self.diagnostics.extend(errors);
                return Err(self);
            }
        };

        self.trees.extend(trees);

        Ok(self)
    }

    pub fn report_to_string(&self) -> String {
        self.db.report_to_string(&self.diagnostics).expect(
            "This should never happen as an error created inside this struct cannot be invalid",
        )
    }

    pub fn report(&self) {
        self.db.report(&self.diagnostics).expect(
            "This should never happen as an error created inside this struct cannot be invalid",
        );
    }

    fn resolve_module_graph(&mut self) {}

    fn store_string(&mut self, s: String) -> PinnedStr<'this> {
        self.sources.push(Pin::new(s));
        let last = self.sources.last().unwrap();
        let len = last.len();
        let ptr = last.as_ptr();
        PinnedStr(ptr, len, PhantomData)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ves_path::VesPath;
    use std::path::Path;

    use log::LevelFilter;

    static CRATE_ROOT: &str = env!("CARGO_MANIFEST_DIR");
    static TESTS_DIR: &str = "tests";

    #[test]
    fn test_middle_passes() {
        simple_logging::log_to_stderr(LevelFilter::Debug);
        let mut mid = VesMiddle::new(ImportConfig {
            dep_graph_output: None,
            ves_path: VesPath::new(
                &[
                    "./{}.ves",
                    "tests/test_module/{}.ves",
                    "tests/test_module/{}/{}.ves",
                ],
                Path::new(CRATE_ROOT).join(TESTS_DIR),
            )
            .unwrap(),
            variables: std::collections::HashMap::new(),
        });

        let source = "import thing\nimport \"./test_module/inner/inner.ves\" as _";
        let output = match mid.process_snippet(source) {
            Ok(mid) => mid.report_to_string(),
            Err(mid) => mid.report_to_string(),
        };

        eprintln!("{}", output);
    }
}
