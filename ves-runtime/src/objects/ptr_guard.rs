//! Contains the implementation of the [`PtrGuard`] type used to enforce correct reference counting semantics within [`Value`]s.
use ves_cc::{Cc, Trace};

use crate::objects::{VesPtr, VesRef};

/// A guard that protects raw Cc pointers from being accidentally copied.
#[repr(transparent)]
#[derive(PartialEq, Hash)]
// NOTE: the implementation must never copy the pointer without precautions.
pub struct PtrGuard(VesPtr);

impl PtrGuard {
    /// Creates a new [`PtrGuard`] for the given [`VesRef`].
    pub fn new(r#ref: VesRef) -> Self {
        // Safety: We immediately pass the leaked pointer to PtrGuard, which makes sure to properly deallocate it if needed.
        Self(unsafe { r#ref.leak() })
    }

    /// Allows access of the inner [`VesPtr`] without affecting its reference count.
    ///
    /// # Examples
    ///
    /// ```
    /// # use ves_runtime::objects::{Value, VesObject, ptr_guard::PtrGuard};
    /// # use ves_cc::CcContext;
    /// let ctx = CcContext::new();
    /// let obj = ctx.cc(VesObject::new_str(&ctx, "a string"));
    /// let guard = PtrGuard::new(obj);
    /// guard.with(|cc| assert!(matches!(&**cc, VesObject::Str(_))))
    /// ```
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

impl Trace for PtrGuard {
    fn trace(&self, tracer: &mut ves_cc::Tracer) {
        self.with(|cc| cc.trace(tracer))
    }
}
