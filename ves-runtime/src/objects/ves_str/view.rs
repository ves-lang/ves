use ves_cc::{Cc, Trace};

use super::VesStr;

#[derive(Debug, Clone)]
pub struct VesStrView(pub(super) Cc<VesStr>);

impl Trace for VesStrView {
    fn trace(&self, tracer: &mut ves_cc::Tracer) {
        self.0.trace(tracer)
    }
}

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
