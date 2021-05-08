#![feature(box_syntax, box_patterns, bindings_after_at)]

use std::{marker::PhantomData, path::Path, pin::Pin};

use registry::ModuleRegistry;
use ves_error::{ErrCtx, FileId, Files, VesFileDatabase};
use ves_parser::ast::AST;
use ves_path::VesPath;
mod macros;

pub mod constant_folder;
pub mod env;
pub mod imports;
pub mod registry;
pub mod resolver;
mod resolver_definitions;
pub mod ves_path;

pub use resolver::Resolver;

/// The default interning threshold for strings (20 characters).
pub const DEFAULT_INTERNING_THRESHOLD: usize = 20;
/// The default constant folding opt-in value (true).
pub const DEFAULT_DO_CONSTANT_FOLDING: bool = true;
/// The default dead store elimination opt-in value (true).
pub const DEFAULT_ELIMINATE_DEAD_STORES: bool = true;

/// A configuration struct for module imports.
#[derive(Clone, Debug)]
pub struct ImportConfig<'path> {
    /// The paths that will be used to to resolve "simple" imports.
    pub ves_path: VesPath<'path>,
    /// The list of variables to be used during substitution.
    pub variables: std::collections::HashMap<std::borrow::Cow<'static, str>, String>,
}

/// This config control ths constant folding pass.
#[derive(Debug, Clone, Copy)]
pub struct ConstantFoldingConfig {
    /// The interning threshold with the maximum length of an internable string.
    /// Any string longer than this value will not be constant-propagated.
    pub interning_threshold: usize,
    /// Whether to do constant folding (and very basic constant propagation) on the AST.
    pub constant_folding: bool,
    /// Whether to eliminate the dead stores left after the constant folding pass.
    pub dead_store_elimination: bool,
}

/// A struct with the parameters used by the intermediate compiler passes.
#[derive(Debug, Clone)]
pub struct VesMiddleConfig<'path> {
    /// The config that controls the constant folding pass.
    pub fold_config: ConstantFoldingConfig,
    /// The module resolution and import configuration.
    pub import_config: ImportConfig<'path>,
}

impl<'path> VesMiddleConfig<'path> {
    /// Creates a new [`VesMiddleConfig`] instance initialized with the default values.
    pub fn with_import_config(import_config: ImportConfig<'path>) -> Self {
        Self {
            fold_config: ConstantFoldingConfig::default(),
            import_config,
        }
    }
}

/// A struct used for resolving module graphs and running intermediate AST passes.
pub struct VesMiddle<'path, 'this, T = ()> {
    /// A vec of pinned string allocations used within the database and AST vec as `&'this` str slices.
    sources: Vec<Pin<String>>,
    /// A file database where sources are `PinnedStr<'this>` tha actually point into the strings in `sources`.
    db: VesFileDatabase<String, PinnedStr<'this>>,
    /// A vec of valid module ASTs where all lexemes are `&'this` strings slices of a source from `sources`.
    trees: Vec<AST<'this>>,
    /// The list of diagnostics from all modules processed so far.
    diagnostics: ErrCtx,
    /// The module registry used to resolve modules.
    registry: ModuleRegistry<T>,
    /// The module import dependency graph.
    pub(crate) import_graph: petgraph::graphmap::GraphMap<FileId, (), petgraph::Directed>,
    /// The import configuration.
    pub(crate) config: VesMiddleConfig<'path>,
}

impl<'path, 'this, M> VesMiddle<'path, 'this, M> {
    /// Creates a new [`VesMiddle`] with the given import config
    pub fn new(config: VesMiddleConfig<'path>) -> Self {
        Self {
            sources: Vec::new(),
            config,
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

    /// Returns a reference to the import config struct.
    #[inline]
    pub fn import_config(&self) -> &ImportConfig<'path> {
        &self.config.import_config
    }

    /// Parses and resolves the given source, saving the resulting AST if all stages of the pipeline were successful.
    /// Writes any errors or warnings into the internal diagnostic list.
    /// Returns an empty result indicating the success or failure of the operation -- use the `report_*` methods to obtain error reports.
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

    /// Parses and resolved the given snippet, saving the resulting  saving the resulting AST if all stages of the pipeline were successful.
    /// Writes any errors or warnings into the internal diagnostic list.
    /// Returns an empty result indicating the success or failure of the operation -- use the `report_*` methods to obtain error reports.
    #[allow(clippy::result_unit_err)]
    pub fn process_snippet<S: Into<String>>(&mut self, source: S) -> Result<(), ()> {
        let source = self.store_string(source.into());
        let id = self.db.add_snippet(source);
        self.resolve_module(id)
    }

    // TODO: this needs a way to reuse the pinned allocations
    /// Maps the given processor function to the AST of every module stored. The modules are guaranteed to be
    /// syntactically and semantically correct.
    /// Calling this function renders the entire module unusable
    pub fn map_modules<'a: 'this, F, T>(&'a mut self, mut processor: F) -> ProcessingResult<T, M>
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
            registry: std::mem::take(&mut self.registry),
            diagnostics,
            db,
            config: self.config.clone(),
        }
    }

    // TODO: add native imports to the graph.
    /// Renders the dependency graph in the graphviz (DOT) format.
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

    /// Clears the internal data structures, removing any stored ASTs, source code, diagnostics, and the dependency graph.
    pub fn clear(&mut self) {
        self.db = VesFileDatabase::new();
        self.diagnostics = ErrCtx::new();
        self.trees.clear();
        self.sources.clear();
        self.import_graph.clear();
    }

    /// Returns whether the files with the given id has already been parsed.
    #[inline]
    pub(crate) fn is_parsed(&self, file_id: FileId) -> bool {
        self.db.is_parsed(file_id).unwrap()
    }

    /// Returns the default base path supplied by the import configuration.
    #[inline]
    pub(crate) fn default_base_path(&self) -> &Path {
        &self.import_config().ves_path.default_base
    }

    /// Returns the name of or full path to the module with the given file id.
    #[inline]
    pub(crate) fn name(&self, file_id: FileId) -> String {
        self.db.name(file_id).unwrap()
    }

    ///  Returns the file id of the file with the given name or path.
    #[inline]
    pub(crate) fn id_by_name(&self, name: &str) -> Option<FileId> {
        self.db.get_id_by_name(name)
    }

    /// Stores the given (name, source) pair inside the database, returning a `&'this` reference to the source.
    /// This act is unsafe as `'this` isn't actually enforced to last as long as `self`.
    /// The code using this method must be careful not to leak the source reference to any external code.
    pub(crate) fn store(&mut self, name: String, source: String) -> (FileId, &'this str) {
        let name = name;
        let source = self.store_string(source);
        let id = self.db.add_file(name, source.clone());
        (id, source.str())
    }

    /// Lexes and parsers the file with the given id.
    pub(crate) fn parse_single(&mut self, file_id: FileId) -> Result<AST<'this>, ErrCtx> {
        let source = self.db.file(file_id).unwrap().source().str();
        ves_parser::Parser::new(ves_parser::Lexer::new(source), file_id, &self.db).parse()
    }

    /// Resolves the module with the given id by traversing and loading all its dependencies, saving them
    /// inside the struct. To obtain the resulting ASTs, use the `map_modules` method.
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

    /// Reports the errors, warnings, and diagnostics accumulated so far to a [`String`].
    pub fn report_to_string(&self) -> String {
        self.db.report_to_string(&self.diagnostics).expect(
            "This should never happen as an error created inside this struct cannot be invalid",
        )
    }

    /// Reports the errors, warnings, and diagnostics accumulated so far to STDERR.
    pub fn report(&self) {
        self.db.report(&self.diagnostics).expect(
            "This should never happen as an error created inside this struct cannot be invalid",
        );
    }

    /// Stores a the given string inside the [`sources`] ves, returning an unsafe wrapper [`PinnedStr`] with the lifetime of `'this`.
    /// Note that the actual lifetime of the string is `self`.
    fn store_string(&mut self, s: String) -> PinnedStr<'this> {
        self.sources.push(Pin::new(s));
        let last = self.sources.last().unwrap();
        let len = last.len();
        let ptr = last.as_ptr();
        PinnedStr(ptr, len, PhantomData)
    }
}

/// A module resolution result containing the file database, all errors, warnings, and suggestions,
/// the list of successfully processed modules, and the import configuration.j
#[derive(Debug)]
pub struct ProcessingResult<'path, T, M> {
    /// The list of outputs produced by the mapping function applied to all valid ASTs.
    output: Vec<T>,
    /// The module registry.
    pub registry: ModuleRegistry<M>,
    /// The list of diagnostics produced by all modules in the dependency graph.
    pub diagnostics: ErrCtx,
    /// The file database containing the names and sources of all modules in the dependency graph (including invalid ones).
    pub db: VesFileDatabase<String, String>,
    /// The configuration that was used by the pass.
    pub config: VesMiddleConfig<'path>,
}

impl<'path, T, M> ProcessingResult<'path, T, M> {
    /// Returns [`true`] if a module in the compilation unit had an error.
    #[inline]
    pub fn had_error(&self) -> bool {
        self.diagnostics.had_error()
    }

    /// Returns the list of all valid outputs without checking whether the whole pass has succeeded.
    #[inline]
    pub fn get_output_unchecked(&mut self) -> Vec<T> {
        std::mem::take(&mut self.output)
    }

    /// Returns the list of all valid outputs if the whole pas succeeded, and a reference to self otherwise.
    pub fn get_output(&mut self) -> Result<Vec<T>, &mut Self> {
        if self.had_error() {
            Err(self)
        } else {
            Ok(self.get_output_unchecked())
        }
    }

    /// A shortcut for `db.report_to_string().unwrap()`.
    pub fn report_to_string(&self) -> String {
        self.db
            .report_to_string(&self.diagnostics)
            .expect("Reporting the diagnostics to a String unexpectedly failed.")
    }
}

impl Default for ConstantFoldingConfig {
    fn default() -> Self {
        Self {
            interning_threshold: DEFAULT_INTERNING_THRESHOLD,
            constant_folding: DEFAULT_DO_CONSTANT_FOLDING,
            dead_store_elimination: DEFAULT_ELIMINATE_DEAD_STORES,
        }
    }
}

impl<'path> From<ImportConfig<'path>> for VesMiddleConfig<'path> {
    fn from(config: ImportConfig<'path>) -> Self {
        Self::with_import_config(config)
    }
}

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
    test_eq!(t14_registry_imports);

    fn resolve_module(source: String) -> String {
        // Note: Enable for debugging purposes
        // simple_logging::log_to_stderr(log::LevelFilter::Debug);

        let mut mid = VesMiddle::<()>::new(
            ImportConfig {
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
            }
            .into(),
        );

        mid.registry_mut()
            .add_native_module(
                "@std/io".into(),
                (),
                vec!["input", "open"]
                    .into_iter()
                    .map(ToOwned::to_owned)
                    .collect(),
            )
            .unwrap();

        mid.registry_mut()
            .add_native_module(
                "local".into(),
                (),
                vec!["exists"].into_iter().map(ToOwned::to_owned).collect(),
            )
            .unwrap();

        let _ = mid.process_snippet(source);

        let graph = mid.render_import_graph();

        let mut results = mid.map_modules(|ast| Ok(ast_to_str(ast)));
        format!("{}\n{}\n{}", graph, results.report_to_string(), {
            let mut out = results.get_output_unchecked();
            out.sort();
            out.join("\n")
        })
        .replace(
            &crate::imports::into_os_agnostic(
                results
                    .config
                    .import_config
                    .ves_path
                    .default_base
                    .display()
                    .to_string(),
            ),
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
