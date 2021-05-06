use std::{
    borrow::Cow,
    hash::{BuildHasher, Hasher},
    ptr::NonNull,
};

use ahash::RandomState;

use crate::gc::{GcObj, Trace};

use super::VesStr;

#[derive(Debug, Clone, Copy)]
pub struct VesStrView {
    _ptr: GcObj,
    raw: NonNull<VesStr>,
}

impl VesStrView {
    pub fn new(ptr: GcObj) -> Self {
        Self {
            _ptr: ptr,
            raw: Self::get_raw(ptr),
        }
    }

    #[inline]
    pub fn str(&self) -> &Cow<'static, str> {
        self.inner()
    }

    fn get_raw(mut ptr: GcObj) -> NonNull<VesStr> {
        match &mut *ptr {
            crate::VesObject::Str(s) => unsafe { NonNull::new_unchecked(s as *mut _) },
            _ => unreachable!(),
        }
    }
}

unsafe impl Trace for VesStrView {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj))
    where
        Self: Sized,
    {
        tracer(&mut self._ptr);
    }

    fn after_forwarding(&mut self) {
        self.raw = Self::get_raw(self._ptr);
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
        unsafe { self.raw.as_ref() }
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
