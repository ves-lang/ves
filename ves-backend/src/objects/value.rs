//! Contains the implementation of the Ves [`Value`] type.
use std::fmt::{self, Display, Formatter};

use crate::gc::{Trace, VesRef};

/// A Ves value allocated on the stack. Note that cloning isn't *always* free since we need to properly handle reference-counted pointers.
/// However, for the primitive types, the additional cost is only a single if branch.
#[derive(Debug, Clone, Copy)]
pub enum Value {
    /// A 48-bit integer
    Int(i32),
    /// A 62-bit floating pointer number. The other 2 bits are reserved for NaN Boxing.
    Float(f64),
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
            (Value::Int(l), Value::Int(r)) => *l == *r,
            // TODO: handle NaN, since they are now stored in constant pool
            (Value::Float(l), Value::Float(r)) => *l == *r,
            (Value::Bool(l), Value::Bool(r)) => *l == *r,
            (Value::Ref(l), Value::Ref(r)) => *l == *r,
            (Value::None, Value::None) => true,
            _ => false,
        }
    }
}

impl Eq for Value {}

impl std::hash::Hash for Value {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Value::Int(n) => n.hash(state),
            Value::Float(n) => n.to_bits().hash(state),
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

    pub fn is_truthy(&self) -> bool {
        match self {
            Value::None => false,
            Value::Int(v) => *v != 0,
            Value::Float(v) => *v != 0.0,
            Value::Bool(v) => *v,
            Value::Ref(_) => true,
        }
    }
}

impl From<VesRef> for Value {
    fn from(ptr: VesRef) -> Self {
        Self::Ref(ptr)
    }
}

impl From<i32> for Value {
    fn from(v: i32) -> Self {
        Value::Int(v)
    }
}

impl From<f64> for Value {
    fn from(f: f64) -> Self {
        Value::Float(f)
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

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(v) => v.fmt(f),
            Value::Float(v) => v.fmt(f),
            Value::Bool(v) => v.fmt(f),
            Value::None => write!(f, "none"),
            Value::Ref(v) => (*v).fmt(f),
        }
    }
}

#[cfg(test)]
mod tests {}
