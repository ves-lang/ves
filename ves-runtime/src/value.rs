//! Contains the implementation of the Ves [`Value`] type.
use std::{borrow::Cow, ptr::NonNull};

use ves_cc::{Cc, CcBox, Trace};

use crate::ves_str::VesStr;

pub type VesRef = Cc<HeapObject>;
pub type VesPtr = NonNull<CcBox<HeapObject>>;
pub type VesRawPtr = *mut CcBox<HeapObject>;

/// QQQ: Should this be called HeapObject?
#[derive(Debug, Clone)]
pub enum HeapObject {
    Str(Cc<VesStr>),
    /// A temporary stub for testing purposes.
    Obj(std::collections::HashMap<Cow<'static, str>, Value>),
}

impl Trace for HeapObject {
    fn trace(&self, tracer: &mut ves_cc::Tracer) {
        match self {
            HeapObject::Str(s) => s.trace(tracer),
            HeapObject::Obj(o) => {
                o.values().for_each(|v| v.trace(tracer));
            }
        }
    }
}

impl Trace for Value {
    fn trace(&self, tracer: &mut ves_cc::Tracer) {
        if let Value::Ptr(p) = self {
            p.with(|cc| cc.trace(tracer));
        }
    }
}

/// A guard that protects raw Cc pointers from being accidentally copied.
#[repr(transparent)]
#[derive(PartialEq, Hash)]
// NOTE: the implementation must never copy the pointer without precautions.
pub struct PtrGuard(VesPtr);

impl PtrGuard {
    #[inline]
    pub fn with<T, F>(&self, mut f: F) -> T
    where
        F: FnMut(&VesRef) -> T,
    {
        unsafe {
            // Safety: we uphold the invariants by immediately leaking the reconstructed Cc; at the same time,
            // the closure cannot do anything to the value since it's behind an immutable reference.
            let cc = Cc::from_raw(self.0);
            let result = f(&cc);
            Cc::leak(cc); // leak the reconstructed Cc
            result
        }
    }

    /// Consumes the guard and returns the inner pointer.
    #[inline]
    pub fn get(self) -> VesRef {
        // Safety: In order to avoid a redundant clone, we skip the drop of the guard and directly instantiate the Cc.
        // The result of from_raw() is immediately moved, while ManuallyDrop ensures that we don't decrease the refcount twice,
        // thus making the operation safe.
        let this = std::mem::ManuallyDrop::new(self);
        unsafe { Cc::from_raw(this.0) }
    }

    /// Returns the number of references currently being used (including this one).
    #[inline]
    pub fn ref_count(&self) -> usize {
        self.with(|cc| cc.strong_count())
    }

    /// Returns the inner pointer without any safety checks.
    ///
    /// # Safety
    /// The caller must ensure that the pointer is reconstructed into a Cc to avoid memory leaks.
    #[inline]
    pub unsafe fn get_unchecked(self) -> VesPtr {
        let this = std::mem::ManuallyDrop::new(self);
        this.0
    }

    /// Creates a new [`PtrGuard`] using the given [`VesPtr`].
    ///
    /// # Safety
    /// The caller must increment the pointer's refcount before passing it to this function.
    pub unsafe fn new_unchecked(ptr: VesPtr) -> Self {
        Self(ptr)
    }
}

impl Clone for PtrGuard {
    fn clone(&self) -> Self {
        // Safety: Cc::clone bumps the refcount for us, and the leak ensures that we don't decrease it
        PtrGuard(unsafe { Cc::leak(self.with(Cc::clone)) })
    }
}

impl Drop for PtrGuard {
    fn drop(&mut self) {
        // Safety: the other code guarantees that that the pointer is never copied without upholding the invariants.
        std::mem::drop(unsafe { Cc::from_raw(self.0) });
    }
}

impl std::fmt::Debug for PtrGuard {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if f.alternate() {
            let ptr = self.0;
            write!(
                f,
                "{}",
                self.with(|cc| format!("PtrGuard(ptr = {:#p}, obj = {:?})", ptr, cc))
            )
        } else {
            write!(f, "PtrGuard({:#p})", self.0)
        }
    }
}

/// A Ves value allocated on the stack. Note that cloning isn't *always* free since we need to properly handle reference-counted pointers.
/// However, for the primitive types, the additional cost is only a single if branch.
#[derive(Debug, PartialEq)]
pub enum Value {
    /// A 62-bit floating pointer number. The other 2 bits are reserved for NaN Boxing.
    Num(f64),
    /// A boolean value.
    Bool(bool),
    /// A null/none value.
    None,
    /// A reference-counted pointer to a heap-allocated Ves object.
    Ptr(PtrGuard),
}

impl Value {
    /// Returns the number of references used by this value. Returns `0` for the primitive types.
    #[inline]
    pub fn ref_count(&self) -> usize {
        if let Value::Ptr(ptr) = self {
            ptr.ref_count()
        } else {
            0
        }
    }

    /// Returns the inner pointer as a freshly allocated Cc instance.
    #[inline]
    pub fn as_ptr(&self) -> Option<VesRef> {
        if let Value::Ptr(ptr) = self {
            Some(ptr.clone().get())
        } else {
            None
        }
    }

    /// Returns the pointer guard stored inside the value.
    #[inline]
    pub fn as_ptr_guard(&self) -> Option<&PtrGuard> {
        if let Value::Ptr(ptr) = self {
            Some(&ptr)
        } else {
            None
        }
    }
}

impl From<VesRef> for Value {
    fn from(cc: VesRef) -> Self {
        // Safety: We immediately pass the leaked pointer to PtrGuard, which makes sure to properly deallocate it if needed.
        Self::Ptr(PtrGuard(unsafe { cc.leak() }))
    }
}

impl From<f64> for Value {
    fn from(f: f64) -> Self {
        Value::Num(f)
    }
}

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Value::Bool(b)
    }
}

impl Clone for Value {
    fn clone(&self) -> Self {
        if let Value::Ptr(guard) = self {
            Value::Ptr(guard.clone())
        } else {
            unsafe {
                // Safety: Num, Bool, and Nil are `Copy` while `self` is valid for reads, so this operation is safe.
                std::ptr::read(self as *const _)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use ves_cc::CcContext;

    use super::*;

    #[test]
    fn test_primitive_clones() {
        let num = Value::Num(std::f64::consts::PI);
        let r#bool = Value::Bool(true);
        let none = Value::None;

        assert_eq!(num.clone(), Value::Num(std::f64::consts::PI));
        assert_eq!(r#bool.clone(), Value::Bool(true));
        assert_eq!(none.clone(), Value::None);
    }

    #[test]
    fn test_rc_pointer_clones() {
        let ctx = CcContext::new();

        let ptr = ctx.cc(HeapObject::Str(ctx.cc("a string".into())));
        assert_eq!(ptr.strong_count(), 1);
        assert_eq!(ptr.weak_count(), 0);

        let val = Value::from(ptr);
        assert_eq!(val.ref_count(), 1);

        let cloned = val.clone();
        assert_eq!(val.ref_count(), 2);
        assert_eq!(cloned.ref_count(), 2);
        assert_eq!(val, cloned);

        std::mem::drop(val);
        assert_eq!(cloned.ref_count(), 1);

        match &*cloned.as_ptr().map(|cc| cc).unwrap() {
            HeapObject::Str(s) => {
                assert_eq!(&***s, "a string");
            }
            HeapObject::Obj(_) => unreachable!(),
        }

        assert_eq!(ctx.number_of_roots_buffered(), 1);

        std::mem::drop(cloned);
        ctx.collect_cycles();

        assert_eq!(ctx.number_of_roots_buffered(), 0);
    }
}
