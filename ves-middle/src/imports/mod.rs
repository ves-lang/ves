pub mod ves_path;

use petgraph::{graphmap::GraphMap, Directed};
use std::{
    borrow::Cow,
    collections::HashMap,
    path::{Component, Path, PathBuf},
};

use ves_error::{ErrCtx, Files, VesError, VesFileDatabase};
use ves_parser::{ast::AST, lexer::Token, Lexer, Parser};

use self::ves_path::VesPath;

/// An emission strategy for a module's dependency graph.
#[derive(Debug, Clone)]
pub enum DepGraphOutput {
    /// Print the dep graph in the graphviz format to STDOUT.
    Stdout,
    /// Write the dep graph in the graphviz format to the given path.
    Disk(PathBuf),
}

/// A configuration struct for module imports.
/// Currently has only one setting.
#[derive(Clone, Debug)]
pub struct ImportConfig<'a, 'b, S: AsRef<str>> {
    /// The optional emission strategy for the dep graph.
    pub dep_graph_output: Option<DepGraphOutput>,
    /// The paths that will be used to to resolve "simple" imports.
    pub ves_path: VesPath<'a>,
    /// The list of variables to be used during substitution.
    pub variables: HashMap<Cow<'b, str>, S>,
}

// TODO: registry
pub fn resolve_module_graph<'source, 'a, 'b, S: AsRef<str>>(
    entry: AST<'source>,
    db: &'source mut VesFileDatabase<'source>,
    config: ImportConfig<'a, 'b, S>,
) -> Result<Vec<AST<'source>>, ErrCtx> {
    let root_id = entry.file_id;
    let local_path = VesPath::new(&["./{}.ves"], config.ves_path.default_base.clone()).unwrap();

    let mut errors = ErrCtx::new();
    let mut import_graph = GraphMap::<_, _, Directed>::new();
    let mut modules = ahash::AHashMap::new();
    modules.insert(root_id, entry);

    let mut stack = vec![root_id];
    while !stack.is_empty() {
        let id = stack.pop().unwrap();
        import_graph.add_node(id);

        if !db.is_parsed(id).unwrap() {
            let source = db
                .source_string(id)
                .expect("Attempted to parse a file not that's not in the database");

            // Temporarily transmute the lifetime of the source.
            // This should be fine since we (1) never mutate the source and (2) only immutably alias it.
            // After the we're done resolving imports, the AST is transmuted back 'source
            let source: &'static str = lifetime_fix_str(source);

            let ast = match Parser::new(Lexer::new(source), id, db).parse() {
                Ok(ast) => ast,
                Err(e) => {
                    errors.extend(e);
                    continue;
                }
            };
            modules.insert(ast.file_id, ast);
        }

        let mut base_path = PathBuf::from(db.name(id).unwrap().into_owned());
        if !base_path.exists() {
            base_path = config.ves_path.default_base.clone();
        }

        let module = modules.get(&id).unwrap();
        for import in &module.imports {
            use ves_parser::ast::{Import, ImportPath, Symbol};

            let (lookup_path, import_path) = match match match import {
                Import::Direct(path) => path,
                Import::Destructured(path, _) => path,
            } {
                ImportPath::Simple(sym) => (&config.ves_path, sym),
                ImportPath::Full(sym) => (&local_path, sym),
            } {
                (path, Symbol::Bare(import)) => (path, import),
                (path, Symbol::Aliased(import, _)) => (path, import),
            };

            let module_path =
                match try_resolve_path(lookup_path, &base_path, import_path, &config.variables) {
                    Ok(ok) => ok,
                    Err(e) => {
                        errors.record(VesError::import(e, import_path.span.clone(), id));
                        continue;
                    }
                };

            let filename = module_path.to_string_lossy().into_owned();
            let import_id = match db.get_id_by_name(&filename) {
                None => db.add_file(
                    Cow::Owned(filename.clone()),
                    match std::fs::read_to_string(Path::new(&filename[..])) {
                        Ok(source) => source,
                        Err(e) => {
                            errors.record(VesError::import(
                                format!(
                                    "File at `{}` was removed in the middle of being processed: {}",
                                    filename, e
                                ),
                                import_path.span.clone(),
                                id,
                            ));
                            continue;
                        }
                    }
                    .into(),
                ),
                Some(id) => id,
            };

            import_graph.add_edge(id, import_id, ());
        }
    }

    println!("{:?}", petgraph::dot::Dot::new(&import_graph));

    Ok(modules
        .into_iter()
        .map(|(_, ast)| lifetime_fix_ast(ast))
        .collect())
}

fn lifetime_fix_str<'a, 'b>(s: &'a str) -> &'b str {
    unsafe { std::mem::transmute(s) }
}
fn lifetime_fix_ast<'a, 'b>(s: AST<'a>) -> AST<'b> {
    unsafe { std::mem::transmute(s) }
}

fn try_resolve_path<'a, 'b, 'source, S: AsRef<str>>(
    path: &VesPath<'a>,
    base: &Path,
    import: &Token<'source>,
    vars: &HashMap<Cow<'b, str>, S>,
) -> Result<PathBuf, String> {
    for path in path.paths(&import.lexeme[..], vars).map(PathBuf::from) {
        let path = resolve_relative_path(Path::new(base), &path);

        if !path.exists() {
            continue;
        }
        if path.is_dir() {
            return Err(format!(
                "Successfully resolved `{}` to `{}`, but the path is a directory.",
                import.lexeme,
                path.display()
            ));
        }

        return Ok(path);
    }

    Err(format!("Failed to resolve `{}`", import.lexeme))
}

/// Resolves the given path relatively to the base path.
fn resolve_relative_path(base: &Path, relative: &Path) -> PathBuf {
    if relative.starts_with("./") || relative.starts_with("../") {
        let base = if !base.is_dir() {
            base.parent().unwrap_or(base)
        } else {
            base
        };
        normalize_path(&base.join(relative))
    } else {
        relative.to_owned()
    }
}

/// Borrowed from Cargo:
/// [`https://github.com/rust-lang/cargo/blob/58a961314437258065e23cb6316dfc121d96fb71/crates/cargo-util/src/paths.rs#L81`]
pub fn normalize_path(path: &Path) -> PathBuf {
    let mut components = path.components().peekable();
    let mut ret = if let Some(c @ Component::Prefix(..)) = components.peek().cloned() {
        components.next();
        PathBuf::from(c.as_os_str())
    } else {
        PathBuf::new()
    };

    for component in components {
        match component {
            Component::Prefix(..) => unreachable!(),
            Component::RootDir => {
                ret.push(component.as_os_str());
            }
            Component::CurDir => {}
            Component::ParentDir => {
                ret.pop();
            }
            Component::Normal(c) => {
                ret.push(c);
            }
        }
    }
    ret
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::path::Path;

    #[test]
    fn test_relative_path_resolution() {
        let tests = vec![(
            "/home/ves/test/file.ves",
            vec!["../inner/another.ves", "./same_dir.ves", "/a/root/path.ves"],
        )];
        let expected = vec![vec![
            "/home/ves/inner/another.ves",
            "/home/ves/test/same_dir.ves",
            "/a/root/path.ves",
        ]];

        for ((base, relative), exp) in tests.into_iter().zip(expected.into_iter()) {
            for (r, e) in relative.iter().zip(exp.iter()) {
                assert_eq!(
                    resolve_relative_path(Path::new(base), Path::new(r)),
                    Path::new(e)
                );
            }
        }
    }

    static CRATE_ROOT: &str = env!("CARGO_MANIFEST_DIR");
    static TESTS_DIR: &str = "tests";

    #[test]
    fn test_module_parsing() {
        let mut db = VesFileDatabase::new();
        let config = ImportConfig {
            dep_graph_output: None,
            ves_path: VesPath::new(
                &["./{}.ves", "tests/test_module/inner/inner.ves"],
                Path::new(CRATE_ROOT).join(TESTS_DIR),
            )
            .unwrap(),
            variables: HashMap::<_, &'static str>::new(),
        };
        let id =
            db.add_snippet("import thing; import \"tests/test_module/inner/inner.ves\";".into());

        let ast = Parser::new(Lexer::new(&db.source(id).unwrap()), id, &db)
            .parse()
            .unwrap();

        let modules = resolve_module_graph(ast, &mut db, config);
    }
}
