//! Contains the implementation of the [`VesObject`] type.
use std::{
    borrow::Cow,
    fmt::{self, Display, Formatter},
};

use ves_error::VesError;

use crate::{
    gc::Trace,
    values::{
        strings::ImmutableString,
        structs::{Instance, Struct},
    },
    vm::vm::VmInterface,
    Value,
};

use super::{
    functions::{Args, Arity, ClosureDescriptor, FnBound, FnClosure, Function},
    native::BigInt,
    structs::StructDescriptor,
};

use derive_enum_methods::*;
use derive_trace::Trace;

pub trait FnNative: Trace {
    fn call<'a>(&mut self, vm: &'a mut dyn VmInterface, args: Args<'a>) -> Result<Value, VesError>;
    fn arity(&self) -> Arity;
    fn name(&self) -> &Cow<'static, str>;
    fn is_magic(&self) -> bool;
}

#[derive(Trace, is_enum_variant, as_enum_variant, unchecked_enum_variant)]
pub enum Object {
    /// An immutable string.
    Str(ImmutableString),
    /// A heap-allocated arbitrary precision integer.
    Int(BigInt),
    /// A ves struct instance.
    Instance(Instance),
    /// A struct type instance.
    Struct(Struct),
    /// An object which describes how a struct should be created
    StructDescriptor(StructDescriptor),
    /// A plain function with no captures.
    Fn(Function),
    /// A native function.
    FnNative(Box<dyn FnNative>),
    /// A bound function.
    FnBound(FnBound),
    /// A function with captures
    Closure(FnClosure),
    /// An object which describes how a closure should be created
    ClosureDescriptor(ClosureDescriptor),
}

impl Object {
    pub fn is_magic_method(&self) -> bool {
        match self {
            Object::Fn(r#fn) => r#fn.is_magic_method,
            Object::FnNative(r#fn) => r#fn.is_magic(),
            Object::FnBound(bound) => bound.inner().is_magic_method(),
            Object::Closure(r#fn) => r#fn.fn_ptr().get().is_magic_method,
            _ => false,
        }
    }

    pub fn as_struct_mut_unwrapped(&mut self) -> &mut Struct {
        if let Self::Struct(v) = self {
            v
        } else {
            panic!("Couldn't unwrap {:?} as VesObject::Fn", self)
        }
    }

    pub fn as_fn_mut_unwrapped(&mut self) -> &mut Function {
        if let Self::Fn(v) = self {
            v
        } else {
            panic!("Couldn't unwrap {:?} as VesObject::Fn", self)
        }
    }

    pub fn as_str_mut_unwrapped(&mut self) -> &mut ImmutableString {
        if let Self::Str(v) = self {
            v
        } else {
            panic!("Couldn't unwrap {:?} as VesObject::Str", self)
        }
    }
}

impl From<ImmutableString> for Object {
    fn from(s: ImmutableString) -> Self {
        Self::Str(s)
    }
}

impl From<Struct> for Object {
    fn from(v: Struct) -> Self {
        Self::Struct(v)
    }
}

impl From<StructDescriptor> for Object {
    fn from(v: StructDescriptor) -> Self {
        Self::StructDescriptor(v)
    }
}

impl From<Instance> for Object {
    fn from(v: Instance) -> Self {
        Self::Instance(v)
    }
}

impl From<String> for Object {
    fn from(s: String) -> Self {
        Self::from(ImmutableString::new(Cow::Owned(s)))
    }
}

impl From<&'static str> for Object {
    fn from(s: &'static str) -> Self {
        Self::from(ImmutableString::new(Cow::Borrowed(s)))
    }
}

impl From<ClosureDescriptor> for Object {
    fn from(v: ClosureDescriptor) -> Self {
        Self::ClosureDescriptor(v)
    }
}

impl From<FnClosure> for Object {
    fn from(v: FnClosure) -> Self {
        Self::Closure(v)
    }
}

impl From<FnBound> for Object {
    fn from(v: FnBound) -> Self {
        Self::FnBound(v)
    }
}

impl From<Function> for Object {
    fn from(v: Function) -> Self {
        Self::Fn(v)
    }
}

impl From<BigInt> for Object {
    fn from(v: BigInt) -> Self {
        Self::Int(v)
    }
}

impl<F: FnNative + 'static> From<F> for Object {
    fn from(v: F) -> Self {
        Self::FnNative(Box::new(v))
    }
}

impl From<Box<dyn FnNative>> for Object {
    fn from(v: Box<dyn FnNative>) -> Self {
        Self::FnNative(v)
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Object::Str(v) => v.fmt(f),
            Object::Int(v) => v.fmt(f),
            Object::Instance(v) => v.fmt(f),
            Object::Struct(v) => v.fmt(f),
            Object::Fn(v) => v.fmt(f),
            Object::FnBound(v) => v.fmt(f),
            Object::FnNative(v) => write!(f, "<fn native at {:p}>", v),
            Object::Closure(v) => v.fmt(f),
            Object::StructDescriptor(v) => v.fmt(f),
            Object::ClosureDescriptor(v) => v.fmt(f),
        }
    }
}

impl std::fmt::Debug for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use std::fmt::*;

        match (&*self,) {
            (&Object::Str(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "Str");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&Object::Int(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "Int");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&Object::Instance(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "Instance");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&Object::Struct(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "Struct");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&Object::StructDescriptor(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "StructDescriptor");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&Object::Fn(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "Fn");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&Object::FnBound(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "FnBound");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&Object::Closure(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "Closure");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&Object::ClosureDescriptor(ref __self_0),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "ClosureDescriptor");
                let _ = DebugTuple::field(debug_trait_builder, &&(*__self_0));
                DebugTuple::finish(debug_trait_builder)
            }
            (&Object::FnNative(ref func),) => {
                let debug_trait_builder = &mut Formatter::debug_tuple(f, "FnNative");
                let _ =
                    DebugTuple::field(debug_trait_builder, &format!("<native fn at {:p}>", *func));
                DebugTuple::finish(debug_trait_builder)
            }
        }
    }
}
