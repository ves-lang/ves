use std::{
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

use crate::{
    gc::{GcObj, Trace},
    VesObject,
};

pub struct Peeled<T> {
    _obj: GcObj,
    peel: for<'a> fn(&'a mut VesObject) -> &'a mut T,
    peeled: NonNull<T>,
}

impl<T> Clone for Peeled<T> {
    fn clone(&self) -> Self {
        Self {
            _obj: self._obj,
            peel: self.peel,
            peeled: self.peeled,
        }
    }
}
// XXX: This copy impl could also turn out to be a footgun if used carelessly.
impl<T> Copy for Peeled<T> {}

impl<T> std::fmt::Debug for Peeled<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Peeled {{ obj = {:?}, peeled = {:p} }}",
            self._obj, self.peeled
        )
    }
}

impl<T> Peeled<T> {
    pub fn new(mut obj: GcObj, peel: for<'a> fn(&'a mut VesObject) -> &'a mut T) -> Self {
        let peeled = unsafe { NonNull::new_unchecked(peel(&mut *obj)) };
        Self {
            _obj: obj,
            peel,
            peeled,
        }
    }

    #[inline]
    pub fn peeled_ptr(&self) -> &GcObj {
        &self._obj
    }
}

unsafe impl<T> Trace for Peeled<T> {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        tracer(&mut self._obj)
    }

    fn after_forwarding(&mut self) {
        self.peeled = unsafe { NonNull::new_unchecked((self.peel)(&mut *self._obj)) };
    }
}

/// NOTE: these deref impls may turn out to be a footgun. Should we use explicit methods instead?
impl<T> Deref for Peeled<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { self.peeled.as_ref() }
    }
}

impl<T> DerefMut for Peeled<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.peeled.as_mut() }
    }
}
