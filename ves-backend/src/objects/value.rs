//! Contains the implementation of the Ves [`Value`] type.
use std::fmt::{self, Debug, Display, Formatter};

use ves_error::{FileId, VesError};

use crate::{
    gc::{Trace, VesRef},
    VesObject,
};

use super::{
    ves_fn::ClosureDescriptor, ves_int::VesInt, ves_str::VesStr, ves_struct::StructDescriptor,
};

// TODO: user-facing error type
#[derive(Clone, PartialEq)]
pub struct RuntimeError(pub VesError);
pub type Result<T> = std::result::Result<T, RuntimeError>;
impl RuntimeError {
    pub fn new<S: Into<String>>(msg: S) -> Self {
        Self(VesError::runtime(msg, 0..0, FileId::anon()))
    }
}
impl Debug for RuntimeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TypeId(pub usize);

/// A Ves value allocated on the stack. Note that cloning isn't *always* free since we need to properly handle reference-counted pointers.
/// However, for the primitive types, the additional cost is only a single if branch.
#[derive(Debug, Clone, Copy)]
pub enum Value {
    /// A 32-bit integer
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

    pub fn typeid(&self) -> TypeId {
        match self {
            Value::Int(_) => TypeId(0),
            Value::Float(_) => TypeId(1),
            Value::Bool(_) => TypeId(2),
            Value::None => TypeId(3),
            Value::Ref(v) => match &**v {
                VesObject::Str(_) => TypeId(4),
                VesObject::Int(_) => TypeId(5),
                VesObject::Fn(_)
                | VesObject::FnBound(_)
                | VesObject::FnNative(_)
                | VesObject::Closure(_) => TypeId(6),
                VesObject::Instance(v) => TypeId(v.ty_ptr().ptr().as_ptr() as usize),
                VesObject::Struct(_) => TypeId(v.ptr().as_ptr() as usize),
                VesObject::StructDescriptor(_) => unreachable!(),
                VesObject::ClosureDescriptor(_) => unreachable!(),
            },
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

    pub fn as_int(&self) -> Option<&i32> {
        if let Self::Int(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_float(&self) -> Option<&f64> {
        if let Self::Float(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_bool(&self) -> Option<&bool> {
        if let Self::Bool(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_ref(&self) -> Option<&VesRef> {
        if let Self::Ref(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_ref_mut(&mut self) -> Option<&mut VesRef> {
        if let Self::Ref(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_str(&self) -> Option<&VesStr> {
        if let Self::Ref(v) = self {
            if let VesObject::Str(v) = &**v {
                return Some(v);
            }
        }
        None
    }

    pub fn as_bigint(&self) -> Option<&VesInt> {
        if let Self::Ref(v) = self {
            if let VesObject::Int(v) = &**v {
                return Some(v);
            }
        }
        None
    }

    pub fn as_bigint_mut(&mut self) -> Option<&mut VesInt> {
        if let Self::Ref(v) = self {
            if let VesObject::Int(v) = &mut **v {
                return Some(v);
            }
        }
        None
    }

    pub fn as_closure_descriptor(&self) -> Option<&ClosureDescriptor> {
        if let Self::Ref(v) = self {
            if let VesObject::ClosureDescriptor(d) = &**v {
                return Some(d);
            }
        }
        None
    }

    pub fn as_struct_descriptor(&self) -> Option<&StructDescriptor> {
        if let Self::Ref(v) = self {
            if let VesObject::StructDescriptor(d) = &**v {
                return Some(d);
            }
        }
        None
    }

    pub fn as_struct_mut(&mut self) -> Option<&mut super::ves_struct::VesStruct> {
        if let Self::Ref(v) = self {
            if let VesObject::Struct(s) = &mut **v {
                return Some(s);
            }
        }
        None
    }

    pub fn as_instance_mut_unchecked(&mut self) -> &mut super::ves_struct::VesInstance {
        crate::unwrap_unchecked!(VesObject::Instance, &mut **self.as_ref_mut_unchecked())
    }

    pub fn as_struct_mut_unchecked(&mut self) -> &mut super::ves_struct::VesStruct {
        crate::unwrap_unchecked!(VesObject::Struct, &mut **self.as_ref_mut_unchecked())
    }

    pub fn as_struct_descriptor_mut_unchecked(
        &mut self,
    ) -> &mut super::ves_struct::StructDescriptor {
        crate::unwrap_unchecked!(
            VesObject::StructDescriptor,
            &mut **self.as_ref_mut_unchecked()
        )
    }

    pub fn as_int_unchecked(&self) -> &i32 {
        crate::unwrap_unchecked!(self, Int)
    }

    pub fn as_float_unchecked(&self) -> &f64 {
        crate::unwrap_unchecked!(self, Float)
    }

    pub fn as_bool_unchecked(&self) -> &bool {
        crate::unwrap_unchecked!(self, Bool)
    }

    pub fn as_ref_unchecked(&self) -> &VesRef {
        crate::unwrap_unchecked!(self, Ref)
    }

    pub fn as_ref_mut_unchecked(&mut self) -> &mut VesRef {
        crate::unwrap_unchecked!(self, Ref)
    }
}

pub trait IntoVes {
    /// May not fail
    fn into_ves(self) -> Value;
}
impl IntoVes for Value {
    fn into_ves(self) -> Value {
        self
    }
}
impl IntoVes for i32 {
    fn into_ves(self) -> Value {
        Value::Int(self)
    }
}
impl IntoVes for f64 {
    fn into_ves(self) -> Value {
        Value::Float(self)
    }
}
impl IntoVes for () {
    fn into_ves(self) -> Value {
        Value::None
    }
}
impl IntoVes for bool {
    fn into_ves(self) -> Value {
        Value::Bool(self)
    }
}
impl IntoVes for VesRef {
    fn into_ves(self) -> Value {
        Value::Ref(self)
    }
}
impl<T: IntoVes> IntoVes for Option<T> {
    fn into_ves(self) -> Value {
        match self {
            Some(v) => v.into_ves(),
            None => Value::None,
        }
    }
}

pub trait FromVes
where
    Self: Sized,
{
    fn from_ves(v: Value) -> Result<Self>;
}
impl FromVes for i32 {
    fn from_ves(value: Value) -> Result<Self> {
        match value {
            Value::Int(v) => Ok(v),
            _ => Err(RuntimeError::new("Invalid type")),
        }
    }
}
impl FromVes for f64 {
    fn from_ves(value: Value) -> Result<Self> {
        match value {
            Value::Float(v) => Ok(v),
            _ => Err(RuntimeError::new("Invalid type")),
        }
    }
}
impl FromVes for bool {
    fn from_ves(value: Value) -> Result<Self> {
        match value {
            Value::Bool(v) => Ok(v),
            _ => Err(RuntimeError::new("Invalid type")),
        }
    }
}
impl FromVes for () {
    fn from_ves(value: Value) -> Result<Self> {
        match value {
            Value::None => Ok(()),
            _ => Err(RuntimeError::new("Invalid type")),
        }
    }
}
impl FromVes for VesRef {
    fn from_ves(value: Value) -> Result<Self> {
        match value {
            Value::Ref(v) => Ok(v),
            _ => Err(RuntimeError::new("Invalid type")),
        }
    }
}
impl FromVes for Value {
    fn from_ves(value: Value) -> Result<Self> {
        Ok(value)
    }
}

impl<T: FromVes> FromVes for Option<T> {
    fn from_ves(v: Value) -> Result<Self> {
        match v {
            Value::None => Ok(None),
            _ => Some(FromVes::from_ves(v)).transpose(),
        }
    }
}

impl From<i32> for Value {
    fn from(v: i32) -> Self {
        Self::Int(v)
    }
}

impl From<f64> for Value {
    fn from(v: f64) -> Self {
        Self::Float(v)
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
            Value::Int(v) => Display::fmt(v, f),
            Value::Float(v) => Display::fmt(v, f),
            Value::Bool(v) => Display::fmt(v, f),
            Value::None => write!(f, "none"),
            Value::Ref(v) => Display::fmt(&**v, f),
        }
    }
}

#[cfg(test)]
mod tests {}
