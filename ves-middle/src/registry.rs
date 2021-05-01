use std::collections::{HashMap, HashSet};

use ves_error::FileId;
use ves_parser::ast::AST;

/// The implementation of a module.
pub enum ModuleImpl<T> {
    /// A native module of type [`T`].
    Native(T),
    /// A ves module that comes from a source file.
    Ves(FileId),
}

/// A module with a defined list of exports.
pub struct Module<T> {
    /// The implementation of the module.
    pub implementation: ModuleImpl<T>,
    /// The symbols that this module exports.
    pub exports: HashSet<String>,
}

impl<T> Module<T> {
    /// Returns `true` if the given symbol is present in the module.
    #[inline]
    pub fn has_symbol(&self, sym: &str) -> bool {
        self.exports.contains(sym)
    }
}

/// A module registry that holds
pub struct ModuleRegistry<T> {
    /// A map from (module path) to (module interface).
    pub modules: HashMap<String, Module<T>>,
}

impl<T> ModuleRegistry<T> {
    /// Returns `true` if the given module exists and has the symbol [`sym`].
    #[inline]
    pub fn has_symbol(&self, module: &str, sym: &str) -> bool {
        self.modules
            .get(module)
            .map(|m| m.has_symbol(sym))
            .unwrap_or(false)
    }
}

/// An error returned when trying to add a new module.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ModuleError {
    /// A module with this name already exists.
    ModuleCollision,
}

impl<T> ModuleRegistry<T> {
    /// Creates an empty module registry.
    pub fn new() -> Self {
        Self {
            modules: HashMap::new(),
        }
    }

    /// Adds a new `Ves` module to the registry.
    pub fn add_ves_module<'a>(&mut self, path: String, ast: &AST<'a>) -> Result<(), ModuleError> {
        if let Some(module) = self.modules.get(&path) {
            match &module.implementation {
                ModuleImpl::Native(_) => {
                    return Err(ModuleError::ModuleCollision);
                }
                ModuleImpl::Ves(id) => {
                    if *id != ast.file_id {
                        return Err(ModuleError::ModuleCollision);
                    }
                }
            }
        }

        self.modules.insert(
            path,
            Module {
                implementation: ModuleImpl::Ves(ast.file_id),
                exports: ast
                    .exports
                    .iter()
                    .map(|e| {
                        match e {
                            ves_parser::ast::Symbol::Bare(name) => &name.lexeme,
                            ves_parser::ast::Symbol::Aliased(_, alias) => &alias.lexeme,
                        }
                        .clone()
                        .into_owned()
                    })
                    .collect(),
            },
        );
        Ok(())
    }
}

impl<T> Default for ModuleRegistry<T> {
    fn default() -> Self {
        Self::new()
    }
}
