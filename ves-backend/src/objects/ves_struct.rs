use std::{
    cell::UnsafeCell,
    fmt::{self, Display, Formatter},
    ops::{Deref, DerefMut},
    vec::from_elem_in,
};

use crate::{
    gc::{proxy_allocator::ProxyAllocator, GcObj, Trace},
    VesObject,
};
use ahash::RandomState;
use hashbrown::HashMap;

use super::{
    cache_layer::{CacheLayer, PropertyLookup},
    peel::Peeled,
    ves_fn::Arity,
    ves_str::view::VesStrView,
    Value,
};

pub type AHashMap<K, V, A> = HashMap<K, V, RandomState, A>;
pub type VesHashMap<K, V> = HashMap<K, V, RandomState, ProxyAllocator>;

pub struct ViewKey {
    pub(super) view: UnsafeCell<VesStrView>,
}

impl std::fmt::Debug for ViewKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ViewKey({:?})", unsafe { &*self.view.get() })
    }
}

impl From<GcObj> for ViewKey {
    fn from(obj: GcObj) -> Self {
        match &*obj {
            crate::VesObject::Str(_) => ViewKey {
                view: UnsafeCell::new(VesStrView::new(obj)),
            },
            _ => panic!("Expected Str, got {:?}", obj),
        }
    }
}

impl PartialEq for ViewKey {
    fn eq(&self, other: &Self) -> bool {
        unsafe { (&*self.view.get()).eq(&*other.view.get()) }
    }
}

impl std::hash::Hash for ViewKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        unsafe { (&*self.view.get()).hash(state) }
    }
}

impl Eq for ViewKey {}

#[derive(Debug)]
pub struct StructDescriptor {
    pub name: VesStrView,
    /// Field arity (rest field is ignored)
    pub arity: Arity,
}

#[derive(Debug)]
pub struct VesStruct {
    // TODO: store name
    // TODO: static fields
    methods: VesHashMap<ViewKey, GcObj>,
    fields: VesHashMap<ViewKey, u8>,
}

impl VesStruct {
    pub fn new(fields: VesHashMap<ViewKey, u8>, methods: VesHashMap<ViewKey, GcObj>) -> Self {
        Self { methods, fields }
    }
}

unsafe impl Trace for VesHashMap<ViewKey, GcObj> {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        for (name, v) in self {
            Trace::trace(unsafe { &mut *name.view.get() }, tracer);
            Trace::trace(v, tracer);
        }
    }
}

unsafe impl Trace for VesStruct {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        Trace::trace(&mut self.methods, tracer);
        for (name, _) in &mut self.fields {
            Trace::trace(unsafe { &mut *name.view.get() }, tracer);
        }
    }
}

impl PropertyLookup for Peeled<VesStruct> {
    #[inline]
    fn lookup_slot(&self, name: &VesStrView) -> Option<usize> {
        self.get()
            .fields
            .get(&ViewKey {
                view: UnsafeCell::new(*name),
            })
            .copied()
            .map(|x| x as _)
    }
}

#[derive(Debug)]
pub struct VesInstance {
    // Should also include bound methods (lazily copied by default).
    fields: CacheLayer<Peeled<VesStruct>, Value, ProxyAllocator>,
}

impl VesInstance {
    pub fn new(ty: GcObj, proxy: ProxyAllocator) -> Self {
        let fields = from_elem_in(Value::None, ty.as_struct().unwrap().fields.len(), proxy);
        let lookup = Peeled::new(ty, VesObject::as_struct_mut_unwrapped);
        Self {
            fields: CacheLayer::new(lookup, fields),
        }
    }

    #[inline]
    pub fn ty_ptr(&self) -> &GcObj {
        self.fields.lookup().peeled_ptr()
    }

    #[inline]
    pub fn ty(&self) -> &VesStruct {
        self.fields.lookup().get()
    }

    #[inline]
    pub fn ty_mut(&mut self) -> &mut VesStruct {
        self.fields.lookup_mut().get_mut()
    }
}

impl Deref for VesInstance {
    type Target = CacheLayer<Peeled<VesStruct>, Value, ProxyAllocator>;

    fn deref(&self) -> &Self::Target {
        &self.fields
    }
}

impl DerefMut for VesInstance {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.fields
    }
}

unsafe impl Trace for VesInstance {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        Trace::trace(&mut self.fields, tracer);
    }
}

impl Display for VesStruct {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // TODO: better formatting
        f.debug_struct("Struct").finish()
    }
}

impl Display for StructDescriptor {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // TODO: better formatting
        write!(
            f,
            "<{}, {}+{}>",
            self.name.str(),
            self.arity.positional,
            self.arity.default
        )
    }
}

impl Display for VesInstance {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // TODO: better formatting
        f.debug_struct("Instance").finish()
    }
}
