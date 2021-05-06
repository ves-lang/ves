//! Contains the implementation of the Ves [`Value`] type.
use crate::gc::{Trace, VesRef};

/// A Ves value allocated on the stack. Note that cloning isn't *always* free since we need to properly handle reference-counted pointers.
/// However, for the primitive types, the additional cost is only a single if branch.
#[derive(Debug, Clone, Copy)]
pub enum Value {
    /// A 62-bit floating pointer number. The other 2 bits are reserved for NaN Boxing.
    Num(f64),
    /// A boolean value.
    Bool(bool),
    /// A null/none value.
    None,
    /// A managed pointer to a heap-allocated Ves object.
    Ref(VesRef),
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Num(l), Value::Num(r)) => {
                // IEEE-754? Don't make me laugh
                *l == *r || (l.is_nan() && r.is_nan())
            }
            (Value::Bool(l), Value::Bool(r)) => *l == *r,
            (Value::Ref(l), Value::Ref(r)) => *l == *r,
            _ => true,
        }
    }
}

impl Eq for Value {}

impl std::hash::Hash for Value {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Value::Num(n) => n.to_bits().hash(state),
            Value::Bool(b) => b.hash(state),
            Value::Ref(p) => p.hash(state),
            Value::None => {}
        }
    }
}

impl Value {
    /// Returns the inner [`GcObj`].
    #[inline]
    pub fn as_ptr(&self) -> Option<VesRef> {
        if let Value::Ref(ptr) = self {
            Some(*ptr)
        } else {
            None
        }
    }
}

impl From<VesRef> for Value {
    fn from(ptr: VesRef) -> Self {
        Self::Ref(ptr)
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

unsafe impl Trace for Value {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut VesRef)) {
        if let Value::Ref(p) = self {
            p.trace(tracer)
        }
    }

    fn after_forwarding(&mut self) {
        if let Value::Ref(p) = self {
            p.after_forwarding()
        }
    }
}

#[cfg(test)]
mod tests {}
