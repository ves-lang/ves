use std::ptr::NonNull;

use crate::VesObject;

pub mod proxy_allocator;

pub trait VesGc {}

pub trait Trace {
    unsafe fn trace(&mut self, tracer: impl Fn(&mut GcObj));
}

pub struct GcHeader {
    marked: bool,
    next: *mut GcBox,
    // more metadata here
}

pub struct GcBox {
    header: GcHeader,
    data: VesObject,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct GcObj {
    ptr: NonNull<GcBox>,
}

impl GcObj {
    #[inline]
    fn ptr_eq(&self, other: &GcObj) {
        self.ptr.as_ptr() == other.ptr.as_ptr()
    }
}

impl Trace for GcObj {
    #[inline]
    unsafe fn trace(&mut self, tracer: impl Fn(&mut GcObj)) {
        tracer(self)
    }
}

#[cfg(test)]
mod tests {}
