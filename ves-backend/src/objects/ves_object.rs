//! Contains the implementation of the [`VesObject`] type.
use std::{
    borrow::Cow,
    fmt::{self, Display, Formatter},
};

use ves_error::VesError;

use crate::{
    gc::{GcObj, Trace},
    objects::{
        ves_str::VesStr,
        ves_struct::{VesInstance, VesStruct},
    },
    runtime::vm::VmInterface,
    Value,
};

use super::{
    ves_fn::{ClosureDescriptor, VesClosure, VesFn},
    ves_int::VesInt,
};

pub type FnNative = dyn Fn(
    // Vm instance
    &mut dyn VmInterface,
    // Object being called
    GcObj,
    // Args
    Vec<crate::NanBox>,
) -> Result<Value, VesError>;

/// QQQ: should the contained values be Cc or just Box?
pub enum VesObject {
    /// An immutable string.
    Str(VesStr),
    /// A heap-allocated arbitrary precision integer.
    Int(VesInt),
    /// A ves struct instance.
    Instance(VesInstance),
    /// A struct type instance.
    Struct(VesStruct),
    /// A plain function with no upvalues.
    Fn(VesFn),
    /// A native function.
    FnNative(Box<FnNative>),
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

    pub fn as_struct_mut_unwrapped(&mut self) -> &mut VesStruct {
        if let Self::Struct(v) = self {
            v
        } else {
            panic!("Couldn't unwrap {:?} as VesObject::Fn", self)
        }
    }

    pub fn as_fn_mut_unwrapped(&mut self) -> &mut VesFn {
        if let Self::Fn(v) = self {
            v
        } else {
            panic!("Couldn't unwrap {:?} as VesObject::Fn", self)
        }
    }

    pub fn as_str_mut_unwrapped(&mut self) -> &mut VesStr {
        if let Self::Str(v) = self {
            v
        } else {
            panic!("Couldn't unwrap {:?} as VesObject::Str", self)
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

impl From<VesInt> for VesObject {
    fn from(v: VesInt) -> Self {
        Self::Int(v)
    }
}

unsafe impl Trace for VesObject {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        match self {
            VesObject::Str(s) => s.trace(tracer),
            VesObject::Int(s) => s.trace(tracer),
            VesObject::Instance(i) => Trace::trace(i, tracer),
            VesObject::Struct(s) => Trace::trace(s, tracer),
            VesObject::Fn(f) => f.trace(tracer),
            VesObject::Closure(c) => c.trace(tracer),
            // not traceable, only used as a constant
            VesObject::ClosureDescriptor(_) => (),
            VesObject::FnNative(_) => (),
        }
    }

    fn after_forwarding(&mut self) {
        match self {
            VesObject::Str(s) => s.after_forwarding(),
            VesObject::Int(i) => i.after_forwarding(),
            VesObject::Instance(i) => i.after_forwarding(),
            VesObject::Struct(s) => s.after_forwarding(),
            VesObject::Fn(f) => f.after_forwarding(),
            VesObject::Closure(c) => c.after_forwarding(),
            // not traceable, only used as a constant
            VesObject::ClosureDescriptor(_) => (),
            VesObject::FnNative(_) => (),
        }
    }
}

impl Display for VesObject {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            VesObject::Str(v) => v.fmt(f),
            VesObject::Int(v) => v.fmt(f),
            VesObject::Instance(v) => v.fmt(f),
            VesObject::Struct(v) => v.fmt(f),
            VesObject::Fn(v) => v.fmt(f),
            VesObject::FnNative(v) => write!(f, "<fn native at {:p}>", v),
            VesObject::Closure(v) => v.fmt(f),
            VesObject::ClosureDescriptor(v) => v.fmt(f),
        }
    }
}

impl std::fmt::Debug for VesObject {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use std::fmt::*;

        match (&*self,) {
            (&VesObject::Str(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "Str");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&VesObject::Int(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "Int");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&VesObject::Instance(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "Instance");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&VesObject::Struct(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "Struct");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&VesObject::Fn(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "Fn");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&VesObject::Closure(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "Closure");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&VesObject::ClosureDescriptor(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "ClosureDescriptor");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&VesObject::FnNative(ref func),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "FnNative");
                let _ =
                    DebugTuple::field(debug_trait_builder, &format!("<native fn at {:p}>", *func));
                DebugTuple::finish(debug_trait_builder)
            }
        }
    }
}
