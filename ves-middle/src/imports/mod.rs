use petgraph::{dot::Config, graphmap::GraphMap, Directed};
use std::{
    borrow::Cow,
    collections::HashMap,
    path::{Component, Path, PathBuf},
};

use ves_error::{ErrCtx, FileId, Files, VesError, VesFileDatabase};
use ves_parser::{ast::AST, lexer::Token, Lexer, Parser};

use crate::{constant_folder::ConstantFolder, resolver::Resolver, VesMiddle};

use crate::ves_path::VesPath;

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
pub struct ImportConfig<'path> {
    /// The optional emission strategy for the dep graph.
    pub dep_graph_output: Option<DepGraphOutput>,
    /// The paths that will be used to to resolve "simple" imports.
    pub ves_path: VesPath<'path>,
    /// The list of variables to be used during substitution.
    pub variables: HashMap<Cow<'static, str>, String>,
}

// TODO: registry
pub(super) fn resolve_module_graph<'path, 'source>(
    entry: AST<'source>,
    middle: &mut VesMiddle<'path, 'source>,
) -> Result<(Vec<AST<'source>>, ErrCtx), ErrCtx> {
    let root_id = entry.file_id;
    let local_path =
        VesPath::new(&["{}", "./{}.ves"], middle.default_base_path().to_owned()).unwrap();

    let mut errors = ErrCtx::new();
    let mut import_graph = GraphMap::<_, _, Directed>::new();
    let mut modules = ahash::AHashMap::new();
    modules.insert(root_id, entry);

    let mut visited = std::collections::HashSet::new();
    let mut stack = vec![root_id];
    while !stack.is_empty() {
        let id = stack.pop().unwrap();
        // TODO: search for the module in the registry instead
        if visited.contains(&id) {
            continue;
        }
        log::debug!(
            "[VES_MID] Resolving the file `{}`",
            middle.db.name(id).unwrap()
        );
        import_graph.add_node(id);
        visited.insert(id);

        if !middle.is_parsed(id) {
            let ast = match middle.parse_single(id) {
                Ok(ast) => ast,
                Err(e) => {
                    errors.extend(e);
                    continue;
                }
            };
            modules.insert(ast.file_id, ast);
        }

        let mut base_path = PathBuf::from(middle.name(id));
        if !base_path.exists() {
            base_path = middle.default_base_path().to_owned();
        }

        let module = modules.get_mut(&id).unwrap();
        for import in &mut module.imports {
            use ves_parser::ast::{ImportPath, ImportStmt, Symbol};

            let (lookup_path, import_path) = match match match &import.import {
                ImportStmt::Direct(path) => path,
                ImportStmt::Destructured(path, _) => path,
            } {
                ImportPath::Simple(sym) => (&middle.import_config.ves_path, sym),
                ImportPath::Full(sym) => (&local_path, sym),
            } {
                (path, Symbol::Bare(import)) => (path, import),
                (path, Symbol::Aliased(import, _)) => (path, import),
            };

            let module_path = match try_resolve_path(
                lookup_path,
                &base_path,
                import_path,
                &middle.import_config.variables,
            ) {
                Ok(ok) => ok,
                Err(e) => {
                    errors.record(VesError::import(e, import_path.span.clone(), id));
                    continue;
                }
            };

            let filename = module_path.to_string_lossy().into_owned();
            let import_id = match middle.id_by_name(&filename) {
                None => {
                    middle
                        .store(
                            filename.clone(),
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
                            },
                        )
                        .0
                }
                Some(id) => id,
            };

            import.resolved_path = Some(filename);
            import_graph.add_edge(id, import_id, ());
            stack.push(import_id);
        }
    }

    for (id, module) in &mut modules {
        let _ = Resolver::new()
            .resolve(module)
            .map(|e| {
                // Avoid doing constant folding if one of the modules had an error
                if !errors.had_error() {
                    // TODO: make this configurable
                    ConstantFolder::new(20, true).fold(module);
                }
                errors.extend(e)
            })
            .map_err(|e| errors.extend(e));
    }

    // TODO: configurable graph export
    println!(
        "{:?}",
        petgraph::dot::Dot::with_attr_getters(
            &import_graph,
            &[petgraph::dot::Config::EdgeNoLabel, Config::NodeNoLabel],
            &|_, _| "".to_string(),
            &|_, node| {
                format!(
                    "label = \"{}\"",
                    middle
                        .name(node.0)
                        .trim_start_matches(&middle.default_base_path().to_string_lossy()[..])
                )
            }
        )
    );

    // TODO: optionally detect cycles
    #[cfg(feature = "")]
    let resolution_order = match petgraph::algo::toposort(&import_graph, None) {
        Ok(order) => order,
        Err(e) => {
            errors.record(VesError::import(
                format!("An import within the module graph creates a cycle"),
                span,
                file_id,
            ));
            return Err(errors);
        }
    };

    if errors.had_error() {
        Err(errors)
    } else {
        Ok((modules.into_iter().map(|(_, v)| v).collect(), errors))
    }
}

fn try_resolve_path<'a, 'b, 'source, S: AsRef<str>>(
    path: &VesPath<'a>,
    base: &Path,
    import: &Token<'source>,
    vars: &HashMap<Cow<'b, str>, S>,
) -> Result<PathBuf, String> {
    let import_path = import.lexeme.trim_matches({
        let x: &[_] = &['\'', '"'];
        x
    });
    for path in path.paths(import_path, vars).map(PathBuf::from) {
        let path = resolve_relative_path(Path::new(base), &path);
        log::debug!(
            "[VES_MID] Resolving the import `{}`: Looking at `{}` ...",
            import_path,
            path.display()
        );

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

        log::debug!(
            "[VES_MID] Resolving the import `{}`: Successfully resolved the import",
            import_path
        );

        return Ok(std::fs::canonicalize(path).unwrap());
    }

    Err(format!("Failed to resolve `{}`", import_path))
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
}
