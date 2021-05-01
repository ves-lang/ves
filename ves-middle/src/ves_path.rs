use std::{borrow::Cow, collections::HashMap, path::PathBuf};

/// An ordered list of paths that will be used for module lookups.
#[derive(Debug, Clone)]
pub struct VesPath<'a> {
    /// The list of paths with substitutions
    paths: Vec<PathSubstitutions<'a>>,
    /// The default base path to use if the root module doesn't have one.
    pub default_base: PathBuf,
}

impl<'a> VesPath<'a> {
    /// A list of unix-like paths. On windows, the caller must replace `\` with `/`.
    pub fn new<S: AsRef<str>>(
        raw: &'a [S],
        default_base: PathBuf,
    ) -> Result<Self, (&'a str, SubstitutionError)> {
        let mut paths = Vec::with_capacity(raw.len());

        for path in raw {
            let path = path.as_ref();
            paths.push(PathSubstitutions::parse(path).map_err(|e| (path, e))?);
        }

        Ok(Self {
            paths,
            default_base,
        })
    }

    // TODO: make the return type more sensible.
    /// Constructs a new [`VesPath`] initialized with the default parameters.
    pub fn default() -> Result<Result<Self, (&'a str, SubstitutionError<'a>)>, std::io::Error> {
        std::env::current_dir().map(|dir| Self::new(&["./{}.ves"], dir))
    }

    /// Returns an iterator over the paths' substitutions for the given import.
    pub fn paths<'b, 'c, 'd, S: AsRef<str>>(
        &self,
        import: &'c str,
        vars: &'d HashMap<Cow<'b, str>, S>,
    ) -> VesPathIterator<'a, '_, 'c, 'd, 'b, S> {
        VesPathIterator {
            path: self,
            current: 0,
            import,
            vars,
        }
    }
}

/// An error that can occur while performing substitutions.
#[derive(Debug, Clone, PartialEq)]
pub enum SubstitutionError<'a> {
    MissingImportFormatter,
    UnterminatedFragment,
    MissingVariable(Cow<'a, str>),
}

/// A path substitution fragment.
///
/// For example, the path `{cwd}/src/{}.ves` will be parsed as:
/// ```ignore`
/// 1. [PathSubst::Var("cwd")]
/// 2. [PathSubst::Path("src")]
/// 3. [PathSubst::Import, PathSubst::Path(".ves")]
/// ```
#[derive(Debug, Clone, PartialEq)]
pub enum PathSubst<'a> {
    /// A path segment.
    Path(Cow<'a, str>),
    /// An empty substitution fragment.
    Import,
    /// A variable inside a substitution fragment.
    Var(Cow<'a, str>),
}

// A list of the substitution fragments of a path.
#[derive(Debug, Clone, PartialEq)]
pub struct PathSubstitutions<'a> {
    /// The substitution fragments of the path.
    /// The substitutions in the inner vec are concatenated directly.
    /// The substitutions in the outer ves are concatenated with a `/`.
    substitutions: Vec<Vec<PathSubst<'a>>>,
}

impl<'a> PathSubstitutions<'a> {
    pub fn parse(path: &'a str) -> Result<Self, SubstitutionError> {
        #[derive(Clone, Copy)]
        enum ParseState {
            ConsumeUntilLeftBrace,
            ConsumeUntilRightBrace,
        }

        // TODO: support for utf-8 paths

        let mut state = ParseState::ConsumeUntilLeftBrace;
        let mut substs = Vec::new();
        let mut current_subst = Vec::new();
        let mut range = 0..0;
        let mut found_import_formatter = false;

        let bytes = path.char_indices();
        for (i, ch) in bytes {
            match (ch, state) {
                ('{', ParseState::ConsumeUntilLeftBrace) => {
                    range.end = i;
                    let buf = &path[range.clone()];
                    if !buf.is_empty() {
                        current_subst.push(PathSubst::Path(buf.into()));
                    }

                    state = ParseState::ConsumeUntilRightBrace;
                    range.start = i + 1;
                }
                ('}', ParseState::ConsumeUntilRightBrace) => {
                    range.end = i;
                    let buf = &path[range.clone()];
                    current_subst.push(if buf.is_empty() {
                        found_import_formatter = true;
                        PathSubst::Import
                    } else {
                        PathSubst::Var(buf.into())
                    });
                    state = ParseState::ConsumeUntilLeftBrace;
                    range.start = i + 1;
                }
                ('/', ParseState::ConsumeUntilLeftBrace) => {
                    if i == 0 {
                        // The path starts with a slash. Push an empty string to preserve it after "/".join().
                        substs.push(vec![PathSubst::Path("".into())])
                    } else {
                        range.end = i;
                        let buf = &path[range.clone()];
                        if !buf.is_empty() {
                            current_subst.push(PathSubst::Path(buf.into()));
                        }
                        substs.push(current_subst);
                        current_subst = Vec::new();
                    }
                    range.start = i + 1;
                }
                (_, _) => {}
            }
        }

        if matches!(state, ParseState::ConsumeUntilRightBrace) {
            return Err(SubstitutionError::UnterminatedFragment);
        }

        if !found_import_formatter {
            return Err(SubstitutionError::MissingImportFormatter);
        }

        if matches!(state, ParseState::ConsumeUntilLeftBrace) {
            range.end = path.len();
            let buf = &path[range];
            if !buf.is_empty() {
                current_subst.push(PathSubst::Path(buf.into()));
            }
        }

        if !current_subst.is_empty() {
            substs.push(current_subst);
        }

        Ok(PathSubstitutions {
            substitutions: substs,
        })
    }

    /// Substitutes the formatters in the path with the given import and variables.
    pub fn substitute<'b, S: AsRef<str>>(
        &self,
        import: &str,
        vars: &HashMap<Cow<'b, str>, S>,
    ) -> Result<String, SubstitutionError> {
        let mut output = Vec::with_capacity(self.substitutions.len());

        for segment in &self.substitutions {
            let mut result = String::new();

            for subst in segment {
                match subst {
                    PathSubst::Path(path) => result.push_str(&**path),
                    PathSubst::Import => result.push_str(import),
                    PathSubst::Var(v) => {
                        let value = vars
                            .get(&**v)
                            .ok_or_else(|| SubstitutionError::MissingVariable(v.clone()))?;
                        result.push_str(value.as_ref());
                    }
                }
            }

            output.push(result)
        }

        Ok(output.join("/"))
    }
}

/// An iterator over the paths' substitutions..
#[derive(Debug, Clone)]
pub struct VesPathIterator<'a, 'b, 'c, 'd, 'e, S>
where
    S: AsRef<str>,
{
    path: &'b VesPath<'a>,
    current: usize,
    import: &'c str,
    vars: &'d HashMap<Cow<'e, str>, S>,
}

impl<'a, 'b, 'c, 'd, 'e, S> Iterator for VesPathIterator<'a, 'b, 'c, 'd, 'e, S>
where
    S: AsRef<str>,
{
    type Item = String;

    fn next(&mut self) -> Option<Self::Item> {
        match self.path.paths.get(self.current) {
            Some(path) => {
                self.current += 1;
                Some(path.substitute(self.import, self.vars).unwrap())
            }
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_path_substitutions() {
        let path = VesPath::new(
            &[
                "./{}",
                "/{}.ves",
                "../{}.ves",
                "/some/random-dir/{}/{}.ves",
                "{cwd}/123/{}.ves",
                "{}{}{}{}",
                "{custom-variable 123}/{}.ves",
            ],
            std::env::current_dir().unwrap(),
        )
        .unwrap();

        let expected = vec![
            "./thing",
            "/thing.ves",
            "../thing.ves",
            "/some/random-dir/thing/thing.ves",
            "/home/ves/test/123/thing.ves",
            "thingthingthingthing",
            "./src/thing.ves",
        ];

        let import = "thing";
        let vars = vec![
            ("cwd".into(), "/home/ves/test"),
            ("custom-variable 123".into(), "./src"),
        ]
        .into_iter()
        .collect::<HashMap<Cow<'_, str>, _>>();

        let substs = path.paths(import, &vars).collect::<Vec<_>>();
        ves_testing::pretty_assertions::assert_eq!(substs, expected);
    }

    #[test]
    fn test_import_parsing_errors() {
        assert_eq!(
            PathSubstitutions::parse("no import formatter"),
            Err(SubstitutionError::MissingImportFormatter)
        );
        assert_eq!(
            PathSubstitutions::parse(""),
            Err(SubstitutionError::MissingImportFormatter)
        );
        assert_eq!(
            PathSubstitutions::parse("{unterminated"),
            Err(SubstitutionError::UnterminatedFragment)
        );
        assert_eq!(
            PathSubstitutions::parse("{"),
            Err(SubstitutionError::UnterminatedFragment)
        );
    }

    #[test]
    fn test_path_parsing() {
        let paths = vec![
            "./{}",
            "/{}.ves",
            "../{}.ves",
            "/some/random-dir/{}/{}.ves",
            "{cwd}/test/{}.ves",
            "{}{}{}{}",
            "/{custom-variable 123}/{}.ves",
        ];

        let expected = vec![
            PathSubstitutions {
                substitutions: vec![vec![PathSubst::Path(".".into())], vec![PathSubst::Import]],
            },
            PathSubstitutions {
                substitutions: vec![
                    vec![PathSubst::Path("".into())],
                    vec![PathSubst::Import, PathSubst::Path(".ves".into())],
                ],
            },
            PathSubstitutions {
                substitutions: vec![
                    vec![PathSubst::Path("..".into())],
                    vec![PathSubst::Import, PathSubst::Path(".ves".into())],
                ],
            },
            PathSubstitutions {
                substitutions: vec![
                    vec![PathSubst::Path("".into())],
                    vec![PathSubst::Path("some".into())],
                    vec![PathSubst::Path("random-dir".into())],
                    vec![PathSubst::Import],
                    vec![PathSubst::Import, PathSubst::Path(".ves".into())],
                ],
            },
            PathSubstitutions {
                substitutions: vec![
                    vec![PathSubst::Var("cwd".into())],
                    vec![PathSubst::Path("test".into())],
                    vec![PathSubst::Import, PathSubst::Path(".ves".into())],
                ],
            },
            PathSubstitutions {
                substitutions: vec![vec![
                    PathSubst::Import,
                    PathSubst::Import,
                    PathSubst::Import,
                    PathSubst::Import,
                ]],
            },
            PathSubstitutions {
                substitutions: vec![
                    vec![PathSubst::Path("".into())],
                    vec![PathSubst::Var("custom-variable 123".into())],
                    vec![PathSubst::Import, PathSubst::Path(".ves".into())],
                ],
            },
        ];

        for (p, e) in paths.into_iter().zip(expected.into_iter()) {
            let substs = PathSubstitutions::parse(p).unwrap();
            println!("{:#?}\n{:#?}", substs, e);
            ves_testing::pretty_assertions::assert_eq!(substs, e, "{}", p);
        }
    }
}
