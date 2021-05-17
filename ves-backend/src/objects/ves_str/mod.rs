pub mod view;

use std::{
    borrow::Cow,
    cell::Cell,
    fmt::{self, Display, Formatter},
};

use derive_trace::Trace;

#[derive(Debug, Trace)]
pub struct VesStr {
    s: Cow<'static, str>,
    hash: Cell<Option<u64>>,
}

impl VesStr {
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
            let hash = super::ves_str::view::hash(&self.s);
            self.hash.set(Some(hash));
            hash
        }
    }
}

impl From<&'static str> for VesStr {
    fn from(s: &'static str) -> Self {
        Self::new(Cow::Borrowed(s))
    }
}

impl From<String> for VesStr {
    fn from(s: String) -> Self {
        Self::new(Cow::Owned(s))
    }
}

impl std::ops::Deref for VesStr {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &*self.s
    }
}

impl Display for VesStr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.s)
    }
}
