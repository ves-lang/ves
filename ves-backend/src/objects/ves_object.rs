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
    ves_fn::{Args, Arity, ClosureDescriptor, VesClosure, VesFn, VesFnBound},
    ves_int::VesInt,
    ves_struct::StructDescriptor,
};

pub trait FnNative: Trace {
    fn call<'a>(&mut self, vm: &'a mut dyn VmInterface, args: Args<'a>) -> Result<Value, VesError>;
    fn arity(&self) -> Arity;
    fn name(&self) -> &Cow<'static, str>;
    fn is_magic(&self) -> bool;
}

pub enum VesObject {
    /// An immutable string.
    Str(VesStr),
    /// A heap-allocated arbitrary precision integer.
    Int(VesInt),
    /// A ves struct instance.
    Instance(VesInstance),
    /// A struct type instance.
    Struct(VesStruct),
    /// An object which describes how a struct should be created
    StructDescriptor(StructDescriptor),
    /// A plain function with no captures.
    Fn(VesFn),
    /// A native function.
    FnNative(Box<dyn FnNative>),
    /// A bound function.
    FnBound(VesFnBound),
    /// A function with captures
    Closure(VesClosure),
    /// An object which describes how a closure should be created
    ClosureDescriptor(ClosureDescriptor),
}

impl VesObject {
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

    pub fn as_int(&self) -> Option<&VesInt> {
        if let Self::Int(v) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn as_int_mut(&mut self) -> Option<&mut VesInt> {
        if let Self::Int(v) = self {
            Some(v)
        } else {
            None
        }
    }

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

    pub fn as_fn_native(&self) -> Option<&dyn FnNative> {
        if let Self::FnNative(v) = self {
            Some(&**v)
        } else {
            None
        }
    }

    pub fn as_closure(&self) -> Option<&VesClosure> {
        if let Self::Closure(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_closure_descriptor(&self) -> Option<&ClosureDescriptor> {
        if let Self::ClosureDescriptor(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Safety: The caller *must* ensure that `self` is the right variant
    pub fn as_str_unchecked(&self) -> &VesStr {
        crate::unwrap_unchecked!(self, Str)
    }

    /// Safety: The caller *must* ensure that `self` is the right variant
    pub fn as_fn_unchecked(&self) -> &VesFn {
        crate::unwrap_unchecked!(self, Fn)
    }

    /// Safety: The caller *must* ensure that `self` is the right variant
    pub fn as_int_unchecked(&self) -> &VesInt {
        crate::unwrap_unchecked!(self, Int)
    }

    /// Safety: The caller *must* ensure that `self` is the right variant
    pub fn as_instance_unchecked(&self) -> &VesInstance {
        crate::unwrap_unchecked!(self, Instance)
    }

    /// Safety: The caller *must* ensure that `self` is the right variant
    pub fn as_instance_mut_unchecked(&mut self) -> &mut VesInstance {
        crate::unwrap_unchecked!(self, Instance)
    }

    /// Safety: The caller *must* ensure that `self` is the right variant
    pub fn as_struct_unchecked(&self) -> &VesStruct {
        crate::unwrap_unchecked!(self, Struct)
    }

    /// Safety: The caller *must* ensure that `self` is the right variant
    pub fn as_fn_native_unchecked(&self) -> &dyn FnNative {
        &**crate::unwrap_unchecked!(self, FnNative)
    }

    /// Safety: The caller *must* ensure that `self` is the right variant
    pub fn as_closure_unchecked(&self) -> &VesClosure {
        crate::unwrap_unchecked!(self, Closure)
    }

    /// Safety: The caller *must* ensure that `self` is the right variant
    pub fn as_closure_unchecked_mut(&mut self) -> &mut VesClosure {
        crate::unwrap_unchecked!(self, Closure)
    }

    /// Safety: The caller *must* ensure that `self` is the right variant
    pub fn as_closure_descriptor_unchecked(&self) -> &ClosureDescriptor {
        crate::unwrap_unchecked!(self, ClosureDescriptor)
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

    /// Returns `true` if the ves_object is [`Fn`].
    pub fn is_fn(&self) -> bool {
        matches!(self, Self::Fn(..))
    }

    /// Returns `true` if the ves_object is [`StructDescriptor`].
    pub fn is_struct_descriptor(&self) -> bool {
        matches!(self, Self::StructDescriptor(..))
    }

    /// Returns `true` if the ves_object is [`ClosureDescriptor`].
    pub fn is_closure_descriptor(&self) -> bool {
        matches!(self, Self::ClosureDescriptor(..))
    }

    /// Returns `true` if the ves_object is [`Closure`].
    pub fn is_closure(&self) -> bool {
        matches!(self, Self::Closure(..))
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

impl From<StructDescriptor> for VesObject {
    fn from(v: StructDescriptor) -> Self {
        Self::StructDescriptor(v)
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

impl From<VesFnBound> for VesObject {
    fn from(v: VesFnBound) -> Self {
        Self::FnBound(v)
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

impl<F: FnNative + 'static> From<F> for VesObject {
    fn from(v: F) -> Self {
        Self::FnNative(Box::new(v))
    }
}

impl From<Box<dyn FnNative>> for VesObject {
    fn from(v: Box<dyn FnNative>) -> Self {
        Self::FnNative(v)
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
            VesObject::FnBound(f) => f.trace(tracer),
            VesObject::Closure(c) => c.trace(tracer),
            // not traceable, only used as a constant
            VesObject::StructDescriptor(_) => (),
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
            VesObject::FnBound(f) => f.after_forwarding(),
            VesObject::Closure(c) => c.after_forwarding(),
            // not traceable, only used as a constant
            VesObject::StructDescriptor(_) => (),
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
            VesObject::FnBound(v) => v.fmt(f),
            VesObject::FnNative(v) => write!(f, "<fn native at {:p}>", v),
            VesObject::Closure(v) => v.fmt(f),
            VesObject::StructDescriptor(v) => v.fmt(f),
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
            (&VesObject::StructDescriptor(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "StructDescriptor");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&VesObject::Fn(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "Fn");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&VesObject::FnBound(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "FnBound");
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
