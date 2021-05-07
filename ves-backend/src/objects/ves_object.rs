//! Contains the implementation of the [`VesObject`] type.
use std::{
    borrow::Cow,
    fmt::{self, Display, Formatter},
};

use crate::{
    gc::{GcObj, Trace},
    objects::{
        ves_str::VesStr,
        ves_struct::{VesInstance, VesStruct},
    },
};

use super::ves_fn::{ClosureDescriptor, VesClosure, VesFn};

/// QQQ: should the contained values be Cc or just Box?
#[derive(Debug)]
pub enum VesObject {
    /// An immutable string.
    Str(VesStr),
    /// A ves struct instance.
    Instance(VesInstance),
    /// A struct type instance.
    Struct(VesStruct),
    /// A plain function with no upvalues.
    Fn(VesFn),
    /// A function with upvalues
    Closure(VesClosure),
    /// An object which describes how a closure should be created
    ClosureDescriptor(ClosureDescriptor),
}

// TODO: unsafe unchecked getters
impl VesObject {
    pub fn as_instance(&self) -> Option<&VesInstance> {
        if let Self::Instance(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_struct(&self) -> Option<&VesStruct> {
        if let Self::Struct(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_str(&self) -> Option<&VesStr> {
        if let Self::Str(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_fn(&self) -> Option<&VesFn> {
        if let Self::Fn(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl From<VesStr> for VesObject {
    fn from(s: VesStr) -> Self {
        Self::Str(s)
    }
}

impl From<VesStruct> for VesObject {
    fn from(v: VesStruct) -> Self {
        Self::Struct(v)
    }
}

impl From<VesInstance> for VesObject {
    fn from(v: VesInstance) -> Self {
        Self::Instance(v)
    }
}

impl From<String> for VesObject {
    fn from(s: String) -> Self {
        Self::from(VesStr::new(Cow::Owned(s)))
    }
}

impl From<&'static str> for VesObject {
    fn from(s: &'static str) -> Self {
        Self::from(VesStr::new(Cow::Borrowed(s)))
    }
}

impl From<ClosureDescriptor> for VesObject {
    fn from(v: ClosureDescriptor) -> Self {
        Self::ClosureDescriptor(v)
    }
}

impl From<VesClosure> for VesObject {
    fn from(v: VesClosure) -> Self {
        Self::Closure(v)
    }
}

impl From<VesFn> for VesObject {
    fn from(v: VesFn) -> Self {
        Self::Fn(v)
    }
}

unsafe impl Trace for VesObject {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        match self {
            VesObject::Str(s) => s.trace(tracer),
            VesObject::Instance(i) => Trace::trace(i, tracer),
            VesObject::Struct(s) => Trace::trace(s, tracer),
            VesObject::Fn(f) => f.trace(tracer),
            VesObject::Closure(c) => c.trace(tracer),
            // not traceable, only used as a constant
            VesObject::ClosureDescriptor(_) => (),
        }
    }

    fn after_forwarding(&mut self) {
        match self {
            VesObject::Str(s) => s.after_forwarding(),
            VesObject::Instance(i) => i.after_forwarding(),
            VesObject::Struct(s) => s.after_forwarding(),
            VesObject::Fn(f) => f.after_forwarding(),
            VesObject::Closure(c) => c.after_forwarding(),
            // not traceable, only used as a constant
            VesObject::ClosureDescriptor(_) => (),
        }
    }
}

impl Display for VesObject {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            VesObject::Str(v) => v.fmt(f),
            VesObject::Instance(v) => v.fmt(f),
            VesObject::Struct(v) => v.fmt(f),
            VesObject::Fn(v) => v.fmt(f),
            VesObject::Closure(v) => v.fmt(f),
            VesObject::ClosureDescriptor(v) => v.fmt(f),
        }
    }
}
