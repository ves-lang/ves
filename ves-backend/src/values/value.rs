//! Contains the implementation of the Ves [`Value`] type.
use std::fmt::{self, Debug, Display, Formatter};

use ves_error::{FileId, VesError};

use crate::{gc::VesRef, Object};

use super::{
    functions::ClosureDescriptor, native::BigInt, strings::ImmutableString,
    structs::StructDescriptor,
};

use derive_enum_methods::*;
use derive_trace::Trace;

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
#[derive(Debug, Clone, Copy, Trace, is_enum_variant, as_enum_variant, unchecked_enum_variant)]
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
                Object::Str(_) => TypeId(4),
                Object::Int(_) => TypeId(5),
                Object::Fn(_) | Object::FnBound(_) | Object::FnNative(_) | Object::Closure(_) => {
                    TypeId(6)
                }
                Object::Instance(v) => TypeId(v.ty_ptr().ptr().as_ptr() as usize),
                Object::Struct(_) => TypeId(v.ptr().as_ptr() as usize),
                Object::StructDescriptor(_) => unreachable!(),
                Object::ClosureDescriptor(_) => unreachable!(),
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

    pub fn as_str(&self) -> Option<&ImmutableString> {
        if let Self::Ref(v) = self {
            if let Object::Str(v) = &**v {
                return Some(v);
            }
        }
        None
    }

    pub fn as_bigint(&self) -> Option<&BigInt> {
        if let Self::Ref(v) = self {
            if let Object::Int(v) = &**v {
                return Some(v);
            }
        }
        None
    }

    pub fn as_bigint_mut(&mut self) -> Option<&mut BigInt> {
        if let Self::Ref(v) = self {
            if let Object::Int(v) = &mut **v {
                return Some(v);
            }
        }
        None
    }

    pub fn as_closure_descriptor(&self) -> Option<&ClosureDescriptor> {
        if let Self::Ref(v) = self {
            if let Object::ClosureDescriptor(d) = &**v {
                return Some(d);
            }
        }
        None
    }

    pub fn as_struct_descriptor(&self) -> Option<&StructDescriptor> {
        if let Self::Ref(v) = self {
            if let Object::StructDescriptor(d) = &**v {
                return Some(d);
            }
        }
        None
    }

    pub fn as_struct_mut(&mut self) -> Option<&mut super::structs::Struct> {
        if let Self::Ref(v) = self {
            if let Object::Struct(s) = &mut **v {
                return Some(s);
            }
        }
        None
    }

    pub fn as_instance(&self) -> Option<&super::structs::Instance> {
        if let Self::Ref(v) = self {
            if let Object::Instance(i) = &**v {
                return Some(i);
            }
        }
        None
    }

    /// # Safety
    /// The caller *must* ensure that the value (1) contains a reference and (2) the reference is an instance.
    pub unsafe fn as_instance_mut_unchecked(&mut self) -> &mut super::structs::Instance {
        crate::unwrap_unchecked!(Object::Instance, &mut **self.as_ref_unchecked_mut())
    }

    /// # Safety
    /// The caller *must* ensure that the value (1) contains a reference and (2) the reference is a struct.
    pub unsafe fn as_struct_mut_unchecked(&mut self) -> &mut super::structs::Struct {
        crate::unwrap_unchecked!(Object::Struct, &mut **self.as_ref_unchecked_mut())
    }

    /// # Safety
    /// The caller *must* ensure that the value (1) contains a reference and (2) the reference is a struct descriptor.
    pub unsafe fn as_struct_descriptor_mut_unchecked(
        &mut self,
    ) -> &mut super::structs::StructDescriptor {
        crate::unwrap_unchecked!(Object::StructDescriptor, &mut **self.as_ref_unchecked_mut())
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

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Value::Int(v) => Display::fmt(v, f),
            Value::Float(v) => Display::fmt(v, f),
            Value::Bool(v) => Display::fmt(v, f),
            Value::None => write!(f, "none"),
            Value::Ref(v) => Display::fmt(v, f),
        }
    }
}

#[cfg(test)]
mod tests {}
