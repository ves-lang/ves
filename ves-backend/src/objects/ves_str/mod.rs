pub mod view;

use std::{
    borrow::Cow,
    cell::Cell,
    fmt::{self, Display, Formatter},
};

use crate::gc::Trace;

#[derive(Debug)]
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

unsafe impl Trace for VesStr {
    fn trace(&mut self, _tracer: &mut dyn FnMut(&mut crate::gc::GcObj)) {}
}

impl Display for VesStr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.s)
    }
}
