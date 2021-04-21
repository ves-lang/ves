//! Contains the implementation of the [`VesObject`] type.
use std::{borrow::Cow, ptr::NonNull};

use ves_cc::{Cc, CcBox, CcContext, Trace};

use crate::objects::{
    ves_str::{StrCcExt, VesStr, VesStrView},
    ves_struct::{VesInstance, VesStruct},
};

/// A reference-counted pointer to a [`VesObject`].
pub type VesRef = Cc<VesObject>;
/// A non-null raw pointer to a refcounted [`VesObject`].
pub type VesPtr = NonNull<CcBox<VesObject>>;
/// A raw pointer to a refcounted [`VesObject`] that _may_ but _shouldn't_ be null.
pub type VesRawPtr = *mut CcBox<VesObject>;

/// QQQ: should the contained values be Cc or just Box?
#[derive(Debug, Clone)]
pub enum VesObject {
    /// An immutable string.
    Str(VesStrView),
    /// A ves struct instance.
    Instance(Cc<VesInstance>),
    /// A struct type instance.
    Struct(Cc<VesStruct>),
}

impl VesObject {
    /// Creates a new [`VesObject`] containing a [`VesStrView`] referencing the given string.
    pub fn new_str<S: Into<Cow<'static, str>>>(ctx: &CcContext, s: S) -> Self {
        VesObject::Str(VesStr::on_heap(ctx, s).view())
    }
}

impl Trace for VesObject {
    fn trace(&self, tracer: &mut ves_cc::Tracer) {
        match self {
            VesObject::Str(s) => s.trace(tracer),
            VesObject::Instance(i) => Trace::trace(i, tracer),
            VesObject::Struct(s) => Trace::trace(s, tracer),
        }
    }
}
