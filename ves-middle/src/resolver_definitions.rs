use std::{borrow::Cow, cell::Cell, collections::HashMap, rc::Rc};

use ves_parser::{
    ast::{FnKind, VarKind},
    Span,
};

/// The kind of the loop currently being resolved.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum LoopKind {
    None,
    Loop,
    While,
    For,
    ForEach,
}

/// The kind of the scope currently being resolved.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ScopeKind {
    /// The global scope.
    Global,
    /// A local scope (a block or a function).
    Local,
    /// A function scope.
    Function,
    /// An `init` block.
    Initializer,
    /// A method scope.
    Method,
}

/// The kind of the name currently being resolved.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NameKind {
    /// A mutable variable.
    Mut,
    /// An immutable variable.
    Let,
    /// An immutable for-each loop variable
    ForEachVar,
    /// A function parameter
    Param,
    /// A function declaration.
    Fn,
    // A method declaration.
    Method,
    /// A struct declaration
    Struct,
    /// An imported module.
    Module,
}

impl NameKind {
    pub fn for_param(is_mutable: bool) -> NameKind {
        if is_mutable {
            NameKind::Mut
        } else {
            NameKind::Let
        }
    }
}

impl From<VarKind> for NameKind {
    #[inline]
    fn from(var: VarKind) -> Self {
        match var {
            VarKind::Let => NameKind::Let,
            VarKind::Mut => NameKind::Mut,
            VarKind::Fn => NameKind::Fn,
            VarKind::Struct => NameKind::Struct,
        }
    }
}

impl From<FnKind> for NameKind {
    #[inline]
    fn from(kind: FnKind) -> Self {
        match kind {
            FnKind::Function => NameKind::Fn,
            FnKind::Method => NameKind::Method,
            FnKind::Initializer => NameKind::Method,
            FnKind::MagicMethod => NameKind::Method,
        }
    }
}

/// The information about a variable's usage.
#[derive(Debug, Clone)]
pub struct VarUsage {
    /// Whether the variable has been declared.
    pub declared: bool,
    /// Whether the variable has been assigned to after its declaration.
    pub assigned: bool,
    /// The number of times this variable has been used.
    pub uses: Rc<Cell<usize>>,
    /// The kind of the variable. For example, whether it is `mut` or `let`.
    pub kind: NameKind,
    /// The span of the variable; used for error reporting.
    pub span: Span,
    ///  The name of the source module
    pub source_module: Option<String>,
}

impl VarUsage {
    #[inline]
    pub fn used(&self) -> bool {
        self.uses.get() > 0
    }

    /// Returns true if the variable is a `let` or `mut` variable.
    pub fn is_var(&self) -> bool {
        matches!(
            self.kind,
            NameKind::Let | NameKind::Mut | NameKind::Param | NameKind::ForEachVar
        )
    }

    /// Returns true if variable is `let`.
    pub fn is_let(&self) -> bool {
        matches!(
            self.kind,
            NameKind::Let
                | NameKind::Fn
                | NameKind::Struct
                | NameKind::ForEachVar
                | NameKind::Param
                | NameKind::Module
        )
    }
}

#[derive(Debug, Clone)]
pub struct StructInterface<'a> {
    pub fields: HashMap<Cow<'a, str>, Span>,
    pub methods: HashMap<Cow<'a, str>, Span>,
}

impl<'a> StructInterface<'a> {
    #[inline]
    pub fn has_property(&self, name: &str) -> bool {
        self.fields.contains_key(name) || self.methods.contains_key(name)
    }
}

// Calculates the Jaro similarity between two sequences. The returned value
/// is between 0.0 and 1.0 (higher value means more similar).
///
// Adapted from https://docs.rs/strsim/0.10.0/.
fn jaro(a: &str, b: &str) -> f64 {
    let a_len = a.chars().count();
    let b_len = b.chars().count();

    // The check for lengths of one here is to prevent integer overflow when
    // calculating the search range.
    if a_len == 0 && b_len == 0 {
        return 1.0;
    } else if a_len == 0 || b_len == 0 {
        return 0.0;
    } else if a_len == 1 && b_len == 1 {
        return if a == b { 1.0 } else { 0.0 };
    }

    let search_range = (std::cmp::max(a_len, b_len) / 2) - 1;

    let mut b_consumed = Vec::with_capacity(b_len);
    for _ in 0..b_len {
        b_consumed.push(false);
    }
    let mut matches = 0.0;

    let mut transpositions = 0.0;
    let mut b_match_index = 0;

    for (i, a_elem) in a.chars().enumerate() {
        let min_bound =
            // prevent integer wrapping
            if i > search_range {
                std::cmp::max(0, i - search_range)
            } else {
                0
            };

        let max_bound = std::cmp::min(b_len - 1, i + search_range);

        if min_bound > max_bound {
            continue;
        }

        for (j, b_elem) in b.chars().enumerate() {
            if min_bound <= j && j <= max_bound && a_elem == b_elem && !b_consumed[j] {
                b_consumed[j] = true;
                matches += 1.0;

                if j < b_match_index {
                    transpositions += 1.0;
                }
                b_match_index = j;

                break;
            }
        }
    }

    if matches == 0.0 {
        0.0
    } else {
        (1.0 / 3.0)
            * ((matches / a_len as f64)
                + (matches / b_len as f64)
                + ((matches - transpositions) / matches))
    }
}

/// The Jaro-Winkler metric adapted from https://docs.rs/strsim/.
pub fn string_distance(a: &str, b: &str) -> f64 {
    let jaro_distance = jaro(a, b);

    // Don't limit the length of the common prefix
    let prefix_length = a
        .chars()
        .zip(b.chars())
        .take_while(|&(ref a_elem, ref b_elem)| a_elem == b_elem)
        .count();

    let jaro_winkler_distance =
        jaro_distance + (0.1 * prefix_length as f64 * (1.0 - jaro_distance));

    if jaro_winkler_distance <= 1.0 {
        jaro_winkler_distance
    } else {
        1.0
    }
}
