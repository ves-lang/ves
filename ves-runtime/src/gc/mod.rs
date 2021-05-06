use std::{
    cell::RefCell,
    ops::{Deref, DerefMut},
    ptr::NonNull,
    rc::Rc,
};

use crate::{NanBox, VesObject};

use self::proxy_allocator::ProxyAllocator;

pub mod naive;
pub mod proxy_allocator;

pub type SharedPtr<T> = Rc<T>;

/// A managed pointer to a [`VesObject`].
pub type VesRef = GcObj;
/// A non-null raw pointer to a managed [`VesObject`].
pub type VesPtr = NonNull<GcBox>;
/// A raw pointer to a managed [`VesObject`] that _may_ but _shouldn't_ be null.
pub type VesRawPtr = *mut GcBox;

pub type DefaultGc = naive::NaiveMarkAndSweep;

#[derive(Debug)]
pub struct GcHandle<T: VesGc> {
    gc: SharedPtr<RefCell<T>>,
}

impl<T: VesGc> Clone for GcHandle<T> {
    fn clone(&self) -> Self {
        Self {
            gc: SharedPtr::clone(&self.gc),
        }
    }
}

impl<T: VesGc> GcHandle<T> {
    pub fn new(gc: T) -> Self {
        Self {
            gc: SharedPtr::new(RefCell::new(gc)),
        }
    }

    fn gc_mut(&mut self) -> std::cell::RefMut<'_, T> {
        (*self.gc).borrow_mut()
    }

    fn gc(&self) -> std::cell::Ref<'_, T> {
        (*self.gc).borrow()
    }
}

impl<T: VesGc> VesGc for GcHandle<T> {
    #[inline]
    fn alloc<'s, 'data, I>(
        &mut self,
        v: impl Into<VesObject>,
        roots: Roots<'s, 'data, I>,
    ) -> Result<GcObj, std::alloc::AllocError>
    where
        I: Iterator<Item = &'data mut dyn Trace>,
    {
        self.gc_mut().alloc(v, roots)
    }

    #[inline]
    fn alloc_permanent(&mut self, v: impl Into<VesObject>) -> GcObj {
        self.gc_mut().alloc_permanent(v)
    }

    #[inline]

    fn force_collect<'s, 'data, I>(&mut self, roots: Roots<'s, 'data, I>)
    where
        I: Iterator<Item = &'data mut dyn Trace>,
    {
        self.gc_mut().force_collect(roots)
    }

    #[inline]
    fn make_shared(&mut self, obj: GcObj) -> GcRcObj {
        self.gc_mut().make_shared(obj)
    }

    #[inline]
    fn bytes_allocated(&self) -> usize {
        self.gc().bytes_allocated()
    }

    #[inline]
    fn proxy(&self) -> ProxyAllocator {
        self.gc().proxy()
    }
}

pub struct Roots<'s, 'data, I>
where
    I: Iterator<Item = &'data mut dyn Trace>,
{
    pub stack: &'s mut Vec<NanBox>,
    pub data: I,
}

impl<'s, 'data> Roots<'s, 'data, std::iter::Empty<&'data mut dyn Trace>> {
    pub fn empty(stack: &'s mut Vec<NanBox>) -> Self {
        Self {
            stack,
            data: std::iter::empty(),
        }
    }
}

pub trait VesGc {
    fn alloc<'s, 'cs, 'data, I>(
        &mut self,
        v: impl Into<VesObject>,
        roots: Roots<'s, 'data, I>,
    ) -> Result<GcObj, std::alloc::AllocError>
    where
        I: Iterator<Item = &'data mut dyn Trace>;

    fn force_collect<'s, 'data, I>(&mut self, roots: Roots<'s, 'data, I>)
    where
        I: Iterator<Item = &'data mut dyn Trace>;

    /// Allocate the given object in the permanent space.
    fn alloc_permanent(&mut self, v: impl Into<VesObject>) -> GcObj;

    fn make_shared(&mut self, obj: GcObj) -> GcRcObj;

    fn bytes_allocated(&self) -> usize;

    fn proxy(&self) -> ProxyAllocator;
}

pub unsafe trait Trace {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj));

    fn after_forwarding(&mut self) {}
}

#[derive(Debug, Default)]
pub struct GcHeader {
    marked: bool,
    // more metadata here
}

#[derive(Debug)]
pub struct GcBox {
    header: GcHeader,
    data: VesObject,
}

// TODO: figure out a way to make this safer using lifetimes.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct GcObj {
    ptr: NonNull<GcBox>,
}

impl Deref for GcObj {
    type Target = VesObject;

    fn deref(&self) -> &Self::Target {
        unsafe { &self.ptr.as_ref().data }
    }
}

impl DerefMut for GcObj {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data().data
    }
}

impl GcObj {
    pub fn new(ptr: VesPtr) -> Self {
        Self { ptr }
    }

    #[inline]
    pub fn ptr_eq(&self, other: &GcObj) -> bool {
        self.ptr.as_ptr() == other.ptr.as_ptr()
    }

    pub(super) fn data(&mut self) -> &mut GcBox {
        unsafe { self.ptr.as_mut() }
    }

    pub fn ptr(&self) -> VesPtr {
        self.ptr
    }
}

unsafe impl Trace for GcObj {
    #[inline]
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        tracer(self)
    }

    fn after_forwarding(&mut self) {
        let obj = &mut **self;
        obj.after_forwarding();
    }
}

#[derive(Debug, Clone)]
pub struct GcRcObj {
    obj: Rc<GcObj>,
}

impl Deref for GcRcObj {
    type Target = GcObj;

    fn deref(&self) -> &Self::Target {
        &*self.obj
    }
}

#[cfg(test)]
mod tests {}
