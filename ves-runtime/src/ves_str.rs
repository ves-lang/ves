use std::{borrow::Cow, cell::Cell};

use ves_cc::{Cc, CcContext, Trace};

#[derive(Debug)]
pub struct VesStr {
    s: Cow<'static, str>,
    hash: Cell<Option<u64>>,
}

trait StrCcExt<T> {
    fn view(&self) -> T;
}

impl StrCcExt<VesStrView> for Cc<VesStr> {
    fn view(&self) -> VesStrView {
        VesStrView(self.clone())
    }
}

impl VesStr {
    pub fn new(s: Cow<'static, str>) -> Self {
        Self {
            s,
            hash: Cell::new(None),
        }
    }

    pub fn on_heap<S: Into<Cow<'static, str>>>(ctx: &CcContext, s: S) -> Cc<Self> {
        ctx.cc(Self::new(s.into()))
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

impl Trace for VesStr {
    fn trace(&self, _tracer: &mut ves_cc::Tracer) {}
}

#[derive(Debug, Clone)]
pub struct VesStrView(Cc<VesStr>);

impl std::cmp::PartialEq for VesStrView {
    fn eq(&self, other: &Self) -> bool {
        match (self.hash.get(), other.hash.get()) {
            (Some(l), Some(r)) => l == r,
            _ => self.s == other.s,
        }
    }
}

impl std::ops::Deref for VesStrView {
    type Target = VesStr;

    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

impl std::cmp::Eq for VesStrView {}

impl<'a> std::cmp::PartialEq<str> for VesStrView {
    fn eq(&self, other: &str) -> bool {
        &(*self.s)[..] == other
    }
}

impl std::hash::Hash for VesStrView {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        if let Some(hash) = self.hash.get() {
            state.write_u64(hash)
        } else {
            self.s.hash(state);
            self.hash.set(Some(state.finish()));
        }
    }
}
