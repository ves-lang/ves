//! Contains the implementation of the Ves [`Value`] type.
use std::ptr::NonNull;

use ves_cc::{Cc, CcBox, Trace};

/// QQQ: Should this be called HeapObject?
#[derive(Debug, Clone)]
pub enum HeapObject {
    /// XXX: Will be replaced with a native string type later on
    Str(String),
}

impl Trace for HeapObject {
    fn trace(&self, tracer: &mut ves_cc::Tracer) {
        match self {
            HeapObject::Str(s) => {
                // This does nothing, but we're keeping it to force us to fix the trace call when the str type get replaced
                s.trace(tracer)
            }
        }
    }
}

/// A guard that protects raw Cc pointers from being accidentally copied.
#[repr(transparent)]
#[derive(Debug, PartialEq, Hash)]
// NOTE: the implementation must never copy the pointer without precautions.
pub struct PtrGuard(NonNull<CcBox<HeapObject>>);

impl PtrGuard {
    #[inline]
    pub fn with<T, F>(&self, f: F) -> T
    where
        F: Fn(&Cc<HeapObject>) -> T,
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
    pub fn get(self) -> Cc<HeapObject> {
        // Safety: In order to avoid a redundant clone, we skip the drop of the guard and directly instantiate the Cc.
        // The result of from_raw() is immediately moved, while ManuallyDrop ensure that we don't decrease the refcount twice,
        // thus making the operation safe.
        let this = std::mem::ManuallyDrop::new(self);
        unsafe { Cc::from_raw(this.0) }
    }

    /// Returns the number of references currently being used (including this one).
    #[inline]
    pub fn ref_count(&self) -> usize {
        self.with(|cc| cc.strong_count())
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
        // Safety: the other code guarantees that that ptr is never copied without upholding the invariants.
        std::mem::drop(unsafe { Cc::from_raw(self.0) });
    }
}

/// A Ves value allocated on the stack. Note that cloning isn't *always* free since we need to properly handle reference counted pointers.
/// However, for the primitive types, the additional cost is only a single if branch.
#[derive(Debug, PartialEq)]
pub enum Value {
    /// A 62-bit floating pointer number. The other 2 bits are reserved for NaN Boxing.
    Num(f64),
    /// A boolean value.
    Bool(bool),
    /// A nil value.
    Nil,
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
    pub fn as_ptr(&self) -> Option<Cc<HeapObject>> {
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

impl From<Cc<HeapObject>> for Value {
    fn from(cc: Cc<HeapObject>) -> Self {
        // Safety: Value makes sure to call Cc::drop when it's dropped itself
        Self::Ptr(PtrGuard(unsafe { cc.leak() }))
    }
}

impl Clone for Value {
    fn clone(&self) -> Self {
        if let Value::Ptr(guard) = self {
            Value::Ptr(guard.clone())
        } else {
            unsafe {
                // Safety: Num, Bool, and Nil are `Copy` while self is valid for reads, so this operation is safe.
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
        let nil = Value::Nil;

        assert_eq!(num.clone(), Value::Num(std::f64::consts::PI));
        assert_eq!(r#bool.clone(), Value::Bool(true));
        assert_eq!(nil.clone(), Value::Nil);
    }

    #[test]
    fn test_rc_pointer_clones() {
        let ctx = CcContext::new();

        let ptr = ctx.cc(HeapObject::Str("a string".into()));
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
                assert_eq!(s, "a string");
            }
        }

        assert_eq!(ctx.number_of_roots_buffered(), 1);

        std::mem::drop(cloned);
        ctx.collect_cycles();

        assert_eq!(ctx.number_of_roots_buffered(), 0);
    }
}
