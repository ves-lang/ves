//! Contains the implementation of the Ves [`Value`] type.
use ves_cc::Trace;

use super::{ptr_guard::PtrGuard, ves_object::VesRef};

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
        Self::Ptr(PtrGuard::new(cc))
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

impl Trace for Value {
    fn trace(&self, tracer: &mut ves_cc::Tracer) {
        if let Value::Ptr(p) = self {
            p.trace(tracer)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::objects::VesObject;
    use ves_cc::CcContext;

    use super::*;

    #[allow(clippy::redundant_clone)]
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

        let ptr = ctx.cc(VesObject::new_str(&ctx, "a string"));
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

        match &*cloned.as_ptr().unwrap() {
            VesObject::Str(s) => {
                assert_eq!(&***s, "a string");
            }
            VesObject::Instance(_) => unreachable!(),
            VesObject::Struct(_) => unreachable!(),
        }

        assert_eq!(ctx.number_of_roots_buffered(), 2);

        std::mem::drop(cloned);
        ctx.collect_cycles();

        assert_eq!(ctx.number_of_roots_buffered(), 0);
    }
}
