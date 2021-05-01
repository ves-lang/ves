#![feature(box_syntax, box_patterns, bindings_after_at)]

use std::{marker::PhantomData, path::Path, pin::Pin};

use imports::ImportConfig;
use registry::ModuleRegistry;
use ves_error::{ErrCtx, FileId, Files, VesFileDatabase};
use ves_parser::ast::AST;
mod macros;

pub mod constant_folder;
pub mod env;
pub mod imports;
pub mod registry;
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
pub struct ProcessingResult<'path, T> {
    output: Vec<T>,
    pub diagnostics: ErrCtx,
    pub db: VesFileDatabase<String, String>,
    pub config: ImportConfig<'path>,
}

impl<'path, T> ProcessingResult<'path, T> {
    #[inline]
    pub fn had_error(&self) -> bool {
        self.diagnostics.had_error()
    }

    #[inline]
    pub fn get_output_unchecked(&mut self) -> Vec<T> {
        std::mem::take(&mut self.output)
    }

    pub fn report_to_string(&self) -> String {
        self.db
            .report_to_string(&self.diagnostics)
            .expect("Reporting the diagnostics to a String unexpectedly failed.")
    }

    pub fn get_output(&mut self) -> Result<Vec<T>, &mut Self> {
        if self.had_error() {
            Err(self)
        } else {
            Ok(self.get_output_unchecked())
        }
    }
}

pub struct VesMiddle<'path, 'this, T = ()> {
    sources: Vec<Pin<String>>,
    db: VesFileDatabase<String, PinnedStr<'this>>,
    trees: Vec<AST<'this>>,
    diagnostics: ErrCtx,
    registry: ModuleRegistry<T>,
    pub(crate) import_graph: petgraph::graphmap::GraphMap<FileId, (), petgraph::Directed>,
    pub(crate) import_config: ImportConfig<'path>,
}

impl<'path, 'this, M> VesMiddle<'path, 'this, M> {
    pub fn new(import_config: ImportConfig<'path>) -> Self {
        Self {
            sources: Vec::new(),
            import_config,
            import_graph: petgraph::graphmap::GraphMap::new(),
            registry: ModuleRegistry::new(),
            trees: Vec::new(),
            db: VesFileDatabase::new(),
            diagnostics: ErrCtx::new(),
        }
    }

    /// Adds the given registry to the struct.
    pub fn with_registry(self, registry: ModuleRegistry<M>) -> Self {
        Self { registry, ..self }
    }

    /// Returns a reference to the module registry.
    pub fn registry(&self) -> &ModuleRegistry<M> {
        &self.registry
    }

    /// Returns a mutable reference to the module registry.
    pub fn registry_mut(&mut self) -> &mut ModuleRegistry<M> {
        &mut self.registry
    }

    /// Parses and resolved the given source, saving the resulting AST only if all stages of the pipeline succeed.
    #[allow(clippy::result_unit_err)]
    pub fn process(
        &mut self,
        name: impl Into<String>,
        source: impl Into<String>,
    ) -> Result<(), ()> {
        let name = name.into();
        let source = self.store_string(source.into());
        let id = self.db.add_file(name, source);
        self.resolve_module(id)
    }

    /// Parses and resolved the given snippet, saving the resulting AST only if all stages of the pipeline succeed.
    #[allow(clippy::result_unit_err)]
    pub fn process_snippet<S: Into<String>>(&mut self, source: S) -> Result<(), ()> {
        let source = self.store_string(source.into());
        let id = self.db.add_snippet(source);
        self.resolve_module(id)
    }

    // TODO: this needs a way to reuse the pinned allocations
    /// Maps the given processor function to the AST of every module stored. The modules are guaranteed to be
    /// syntactically and semantically correct.
    pub fn map_modules<'a: 'this, F, T>(&'a mut self, mut processor: F) -> ProcessingResult<T>
    where
        F: FnMut(&'a AST<'a>) -> Result<T, ErrCtx>,
    {
        let mut errors = ErrCtx::default();
        let output = self
            .trees
            .iter_mut()
            .flat_map(|ast| match processor(ast) {
                Ok(res) => Some(res),
                Err(ex) => {
                    errors.extend(ex);
                    None
                }
            })
            .collect();

        self.diagnostics.extend(errors);
        let diagnostics = std::mem::take(&mut self.diagnostics);

        let db = self.db.clone_owned();
        ProcessingResult {
            output,
            diagnostics,
            db,
            config: self.import_config.clone(),
        }
    }

    /// Renders the dependency graph in the graphviz format.
    pub fn render_import_graph(&self) -> String {
        use petgraph::dot::Config;
        format!(
            "{:?}",
            petgraph::dot::Dot::with_attr_getters(
                &self.import_graph,
                &[petgraph::dot::Config::EdgeNoLabel, Config::NodeNoLabel],
                &|_, _| "".to_string(),
                &|_, node| {
                    format!(
                        "label = \"{}\" ",
                        self.name(node.0)
                            .trim_start_matches(&self.default_base_path().to_string_lossy()[..])
                    )
                }
            )
        )
    }

    pub fn clear(&mut self) {
        self.db = VesFileDatabase::new();
        self.trees.clear();
        self.sources.clear();
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

    fn resolve_module(&mut self, id: FileId) -> Result<(), ()> {
        let ast = match self.parse_single(id) {
            Ok(ast) => ast,
            Err(ex) => {
                self.diagnostics.extend(ex);
                return Err(());
            }
        };

        let trees = match imports::resolve_module_graph(ast, self) {
            Ok((trees, diags)) => {
                self.diagnostics.extend(diags);
                trees
            }
            Err(errors) => {
                self.diagnostics.extend(errors);
                return Err(());
            }
        };

        self.trees.extend(trees);

        Ok(())
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

    static CRATE_ROOT: &str = env!("CARGO_MANIFEST_DIR");
    static TESTS_DIR: &str = "tests";

    ves_testing::make_test_macros!(eq => CRATE_ROOT, TESTS_DIR, resolve_module);

    test_eq!(t11_cyclic_import);
    test_eq!(t12_shadowing_import);
    test_eq!(t13_missing_exports);

    fn resolve_module(source: String) -> String {
        // Note: Enable for debugging purposes
        // simple_logging::log_to_stderr(log::LevelFilter::Debug);

        let mut mid = VesMiddle::<()>::new(ImportConfig {
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

        let _ = mid.process_snippet(source);

        let graph = mid.render_import_graph();

        let mut results = mid.map_modules(|ast| Ok(ast_to_str(ast)));
        format!("{}\n{}\n{}", graph, results.report_to_string(), {
            let mut out = results.get_output_unchecked();
            out.sort();
            out.join("\n")
        })
        .replace(
            &results.config.ves_path.default_base.display().to_string(),
            "",
        )
    }

    fn ast_to_str(ast: &AST<'_>) -> String {
        use ves_parser::AstToStr;

        let imports = ast
            .imports
            .iter()
            .map(|import| import.ast_to_str())
            .collect::<Vec<_>>()
            .join("\n");
        let exports = ast
            .exports
            .iter()
            .map(|export| export.ast_to_str())
            .collect::<Vec<_>>()
            .join("\n");
        let body = ast
            .body
            .iter()
            .map(|stmt| stmt.ast_to_str())
            .collect::<Vec<_>>()
            .join("\n");
        format!(
            "{}{}{}{}{}",
            imports,
            if !imports.is_empty() { "\n" } else { "" },
            exports,
            if !exports.is_empty() { "\n" } else { "" },
            body
        )
    }
}
