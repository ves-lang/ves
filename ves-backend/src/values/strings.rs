use std::{
    borrow::Cow,
    cell::Cell,
    fmt::{self, Display, Formatter},
    hash::{BuildHasher, Hasher},
};

use ahash::RandomState;
use derive_trace::Trace;

use crate::{gc::GcObj, value::Stringify, values::handle::Handle, Object};

#[derive(Debug, Clone, Copy, Trace)]
pub struct StrView {
    handle: Handle<ImmutableString>,
}

impl StrView {
    pub fn new(ptr: GcObj) -> Self {
        Self {
            handle: Handle::new(ptr, Object::as_str_mut_unwrapped),
        }
    }

    #[inline]
    pub fn str(&self) -> &Cow<'static, str> {
        self.inner()
    }
}

#[derive(Debug, Trace)]
pub struct ImmutableString {
    s: Cow<'static, str>,
    hash: Cell<Option<u64>>,
}

impl ImmutableString {
    pub fn new(s: Cow<'static, str>) -> Self {
        Self {
            s,
            hash: Cell::new(None),
        }
    }

    #[inline]
    pub fn inner(&self) -> &Cow<'static, str> {
        &self.s
    }

    #[inline]
    pub fn clone_inner(&self) -> Cow<'static, str> {
        self.s.clone()
    }

    pub fn compute_hash(&self) -> u64 {
        if let Some(hash) = self.hash.get() {
            hash
        } else {
            let hash = hash(&self.s);
            self.hash.set(Some(hash));
            hash
        }
    }
}

impl From<&'static str> for ImmutableString {
    fn from(s: &'static str) -> Self {
        Self::new(Cow::Borrowed(s))
    }
}

impl From<String> for ImmutableString {
    fn from(s: String) -> Self {
        Self::new(Cow::Owned(s))
    }
}

impl std::ops::Deref for ImmutableString {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &*self.s
    }
}

impl Stringify for ImmutableString {
    fn stringify(
        &self,
        _vm: &mut dyn crate::vm::vm::VmInterface,
    ) -> std::result::Result<String, ves_error::VesError> {
        Ok(self.to_string())
    }
}

impl Display for ImmutableString {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.s)
    }
}

impl std::cmp::PartialEq for StrView {
    fn eq(&self, other: &Self) -> bool {
        match (self.hash.get(), other.hash.get()) {
            (Some(l), Some(r)) => l == r,
            _ => self.s == other.s,
        }
    }
}

impl std::ops::Deref for StrView {
    type Target = ImmutableString;

    fn deref(&self) -> &Self::Target {
        self.handle.get()
    }
}

impl std::cmp::Eq for StrView {}

impl<'a> std::cmp::PartialEq<str> for StrView {
    fn eq(&self, other: &str) -> bool {
        &(*self.s)[..] == other
    }
}

impl std::hash::Hash for StrView {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        if let Some(hash) = self.hash.get() {
            state.write_u64(hash)
        } else {
            let hash = hash(&self.s);
            self.hash.set(Some(hash));
            state.write_u64(hash);
        }
    }
}

pub(super) fn hash(s: &str) -> u64 {
    use std::hash::Hash;
    let mut r = RandomState::with_seeds(
        const_random::const_random!(u64),
        const_random::const_random!(u64),
        const_random::const_random!(u64),
        const_random::const_random!(u64),
    )
    .build_hasher();
    s.hash(&mut r);
    r.finish()
}
