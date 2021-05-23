use std::ptr::NonNull;

use crate::{
    gc::{GcObj, Trace, Tracer},
    Object,
};

pub struct Handle<T> {
    _obj: GcObj,
    peel: for<'a> fn(&'a mut Object) -> &'a mut T,
    handle: NonNull<T>,
}

impl<T> Clone for Handle<T> {
    fn clone(&self) -> Self {
        Self {
            _obj: self._obj,
            peel: self.peel,
            handle: self.handle,
        }
    }
}
// XXX: This copy impl could also turn out to be a footgun if used carelessly.
impl<T> Copy for Handle<T> {}

impl<T> std::fmt::Debug for Handle<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Handle {{ obj = {:?}, handle = {:p} }}",
            self._obj, self.handle
        )
    }
}

impl<T> Handle<T> {
    pub fn new(mut obj: GcObj, peel: for<'a> fn(&'a mut Object) -> &'a mut T) -> Self {
        let handle = unsafe { NonNull::new_unchecked(peel(&mut *obj)) };
        Self {
            _obj: obj,
            peel,
            handle,
        }
    }

    #[inline]
    pub fn handle_ptr(&self) -> &GcObj {
        &self._obj
    }

    #[inline]
    pub fn get(&self) -> &T {
        unsafe { self.handle.as_ref() }
    }

    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { self.handle.as_mut() }
    }
}

unsafe impl<T> Trace for Handle<T> {
    fn trace(&mut self, tracer: &mut dyn Tracer) {
        tracer.trace_ptr(&mut self._obj)
    }

    fn after_forwarding(&mut self) {
        self.handle = unsafe { NonNull::new_unchecked((self.peel)(&mut *self._obj)) };
    }
}
