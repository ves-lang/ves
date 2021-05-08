use std::{
    borrow::Cow,
    hash::{BuildHasher, Hasher},
};

use ahash::RandomState;

use crate::{
    gc::{GcObj, Trace},
    objects::peel::Peeled,
    VesObject,
};

use super::VesStr;

#[derive(Debug, Clone, Copy)]
pub struct VesStrView {
    peeled: Peeled<VesStr>,
}

impl VesStrView {
    pub fn new(ptr: GcObj) -> Self {
        Self {
            peeled: Peeled::new(ptr, VesObject::as_str_mut_unwrapped),
        }
    }

    #[inline]
    pub fn str(&self) -> &Cow<'static, str> {
        self.inner()
    }
}

unsafe impl Trace for VesStrView {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        Trace::trace(&mut self.peeled, tracer);
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
        self.peeled.get()
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
            let hash = hash(&self.s);
            self.hash.set(Some(hash));
            state.write_u64(hash);
        }
    }
}

fn hash(s: &str) -> u64 {
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
