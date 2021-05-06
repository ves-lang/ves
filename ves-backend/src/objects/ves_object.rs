//! Contains the implementation of the [`VesObject`] type.
use std::borrow::Cow;

use crate::{
    gc::{GcObj, Trace},
    objects::{
        ves_str::VesStr,
        ves_struct::{VesInstance, VesStruct},
    },
};

/// QQQ: should the contained values be Cc or just Box?
#[derive(Debug)]
pub enum VesObject {
    /// An immutable string.
    Str(VesStr),
    /// A ves struct instance.
    Instance(VesInstance),
    /// A struct type instance.
    Struct(VesStruct),
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

unsafe impl Trace for VesObject {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        match self {
            VesObject::Str(s) => s.trace(tracer),
            VesObject::Instance(i) => Trace::trace(i, tracer),
            VesObject::Struct(s) => Trace::trace(s, tracer),
        }
    }

    fn after_forwarding(&mut self) {
        match self {
            VesObject::Str(s) => s.after_forwarding(),
            VesObject::Instance(i) => i.after_forwarding(),
            VesObject::Struct(s) => s.after_forwarding(),
        }
    }
}
