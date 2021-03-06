use std::{
    borrow::Cow,
    collections::HashMap,
    path::{Component, Path, PathBuf},
};

use ves_error::{ErrCtx, Files, VesError, VesErrorKind};
use ves_parser::{ast::AST, lexer::Token};

use crate::{constant_folder::ConstantFolder, resolver::Resolver, VesMiddle};

use crate::ves_path::VesPath;

/// The substitutions used to resolve local imports, ex. `import "thing"`.
static DEFAULT_LOCAL_IMPORT_PATH: &[&str] = &["{}", "./{}.ves"];

/// Resolves the all dependencies in the module graph with the given entry point according to the
/// import resolution config supplied by `middle.import_config()`.
pub(super) fn resolve_module_graph<'path, 'source, T>(
    entry: AST<'source>,
    middle: &mut VesMiddle<'path, 'source, T>,
) -> Result<(Vec<AST<'source>>, ErrCtx), ErrCtx> {
    let root_id = entry.file_id;
    let local_path = VesPath::new(
        DEFAULT_LOCAL_IMPORT_PATH,
        middle.default_base_path().to_owned(),
    )
    .unwrap();

    let mut errors = ErrCtx::new();
    let mut modules = ahash::AHashMap::new();
    modules.insert(root_id, entry);

    // We perform a depth-first traversal of the module graph by attempting to resolve every dependency of every module
    // using its location as the base path for the dependency.
    let mut visited = std::collections::HashSet::new();
    let mut stack = vec![root_id];
    while let Some(id) = stack.pop() {
        if visited.contains(&id) {
            continue;
        }
        log::debug!(
            "[VES_MID] Resolving the file `{}`",
            middle.db.name(id).unwrap()
        );
        middle.import_graph.add_node(id);
        visited.insert(id);

        // We might need to parse the module if we it hasn't bee pre-loaded.
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

        // Try to use the path of the module being resolved as the base path.
        // If it isn't available (for example, if the module was supplied in-memory), use the default base path.
        let mut base_path = PathBuf::from(middle.name(id));
        if !base_path.exists() {
            base_path = middle.default_base_path().to_owned();
        }

        let module = modules.get_mut(&id).unwrap();
        for import in &mut module.imports {
            use ves_parser::ast::{ImportPath, ImportStmt, Symbol};

            // This nested match expression extracts the path to the dependency that needs to be resolved.
            let (lookup_path, import_path) = match match match &import.import {
                ImportStmt::Direct(path) => path,
                ImportStmt::Destructured(path, _) => path,
            } {
                ImportPath::Simple(sym) => (&middle.import_config().ves_path, sym),
                ImportPath::Full(sym) => (&local_path, sym),
            } {
                (path, Symbol::Bare(import)) => (path, import),
                (path, Symbol::Aliased(import, _)) => (path, import),
            };

            log::debug!(
                "[VES_MID] Resolving the import `{}`: is_root_or_relative_import() = {}",
                import_path.lexeme,
                is_root_or_relative_import(&import_path.lexeme)
            );

            // Try to look the import in the registry firs if it:
            // 1) Isn't a root import (e.g. /root or C:\root)
            // 2) Isn't a relative import such as ./module or ../parent
            if !is_root_or_relative_import(&import_path.lexeme)
                && middle
                    .registry()
                    .has_module(trim_quotes(&import_path.lexeme))
            {
                log::debug!(
                    "[VES_MID] Found the module `{}` in the registry",
                    import_path.lexeme
                );
                import.resolved_path = Some(trim_quotes(&import_path.lexeme).to_string());
                continue;
            }

            // Didn't find the import in the registry, try to look it up by substituting whatever is in the [`VesPath`].
            let module_path = match try_resolve_path(
                lookup_path,
                &base_path,
                import_path,
                &middle.import_config().variables,
            ) {
                Ok(ok) => ok,
                Err(e) => {
                    errors.record(VesError::import(e, import_path.span.clone(), id));
                    continue;
                }
            };

            // Found a module on the disk, try to load it and store in the database
            let filename = module_path.to_string_lossy().into_owned();
            let agnostic = into_os_agnostic(filename.clone());
            let import_id = match middle.id_by_name(&agnostic) {
                None => {
                    middle
                        .store(
                            agnostic.clone(),
                            match std::fs::read_to_string(Path::new(&filename[..])) {
                                Ok(source) => source,
                                Err(e) => {
                                    errors.record(VesError::import(
                                        format!(
                                            "File at `{}` was removed while being processed: {}",
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

            // Add the import to the graph and push it onto the stack.
            import.resolved_path = Some(agnostic);
            middle.import_graph.add_edge(id, import_id, ());
            stack.push(import_id);
        }
    }

    // Add all parsed modules to the registry before running the resolver.
    for (id, module) in &modules {
        let path = middle.name(*id);
        match middle.registry_mut().add_ves_module(path.clone(), module) {
            Ok(_) => {}
            Err(_) => {
                errors.record(VesError::new(
                    format!(
                        "Attempted to resolve two different modules with the same name: `{}`",
                        path
                    ),
                    0..1,
                    VesErrorKind::Resolution,
                    *id,
                ));
            }
        }
    }

    // Resolve all modules.
    let fold = middle.config.fold_config;
    for (_, module) in &mut modules {
        let _ = Resolver::new()
            .resolve_with_registry(module, middle.registry_mut())
            .map(|e| {
                // Avoid doing constant folding if one of the modules had an error
                if !errors.had_error() && fold.constant_folding {
                    // TODO: make this configurable
                    ConstantFolder::new(fold.interning_threshold, fold.dead_store_elimination)
                        .fold(module);
                }
                errors.extend(e)
            })
            .map_err(|e| errors.extend(e));
    }

    if errors.had_error() {
        Err(errors)
    } else {
        Ok((modules.into_iter().map(|(_, v)| v).collect(), errors))
    }
}

/// Returns `true` if the import is rooted (e.g. `/root`) or relative (e.g. `../parent/mod.ves`).
#[inline]
fn is_root_or_relative_import(import: &str) -> bool {
    let path = Path::new(trim_quotes(import));
    path.has_root() || path.starts_with("./") || path.starts_with("../")
}

/// Trims the quotes around the given string.
#[inline]
fn trim_quotes(s: &str) -> &str {
    s.trim_matches({
        let x: &[_] = &['\'', '"'];
        x
    })
}

/// Attempts to the resolve the given import relatively to the base path by repeatedly
/// substituting the import via [`VesPath`]. The first resolved path will be returned as soon as it's found.
fn try_resolve_path<'a, 'b, 'source, S: AsRef<str>>(
    path: &VesPath<'a>,
    base: &Path,
    import: &Token<'source>,
    vars: &HashMap<Cow<'b, str>, S>,
) -> Result<PathBuf, String> {
    let import_path = trim_quotes(&import.lexeme);
    for path in path.paths(import_path, vars).map(PathBuf::from) {
        let path = into_os_specific(path);
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

        #[allow(clippy::useless_conversion)] // windows support
        return Ok(PathBuf::from(adjust_canonicalization(
            std::fs::canonicalize(path).unwrap(),
        )));
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

#[cfg(not(target_os = "windows"))]
fn into_os_specific(path: PathBuf) -> PathBuf {
    path
}

#[cfg(target_os = "windows")]
fn into_os_specific(path: PathBuf) -> PathBuf {
    PathBuf::from(
        path.to_string_lossy()
            .replace('/', &std::path::MAIN_SEPARATOR.to_string()[..]),
    )
}

#[cfg(not(target_os = "windows"))]
pub(super) fn into_os_agnostic(path: String) -> String {
    path
}

#[cfg(target_os = "windows")]
pub(super) fn into_os_agnostic(path: String) -> String {
    path.replace(std::path::MAIN_SEPARATOR, "/")
}

#[cfg(not(target_os = "windows"))]
fn adjust_canonicalization(p: PathBuf) -> PathBuf {
    p
}

#[cfg(target_os = "windows")]
fn adjust_canonicalization(p: PathBuf) -> String {
    const VERBATIM_PREFIX: &str = r#"\\?\"#;
    let p = p.display().to_string();
    p.strip_prefix(VERBATIM_PREFIX)
        .map(String::from)
        .unwrap_or(p)
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
