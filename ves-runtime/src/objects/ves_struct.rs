use std::{ptr::NonNull, vec::from_elem_in};

use crate::gc::{proxy_allocator::ProxyAllocator, GcObj, Trace};
use ahash::RandomState;
use hashbrown::HashMap;

use super::{ves_str::VesStrView, Value};

pub type AHashMap<K, V, A> = HashMap<K, V, RandomState, A>;
pub type VesHashMap<K, V> = HashMap<K, V, RandomState, ProxyAllocator>;

// NOTE: A stub until we implement the compiler
#[derive(Debug)]
pub struct Function {}

impl Trace for Function {
    fn trace(&self, tracer: impl FnMut(&mut GcObj)) {}
}

#[derive(Debug)]
pub struct VesStruct {
    methods: VesHashMap<GcObj, GcObj>,
    fields: VesHashMap<GcObj, u8>,
}

impl VesStruct {
    pub fn new(fields: VesHashMap<GcObj, u8>, methods: VesHashMap<GcObj, GcObj>) -> Self {
        Self { methods, fields }
    }
}

impl Trace for VesStruct {
    fn trace(&self, tracer: &mut ves_cc::Tracer) {
        for (k, v) in &self.methods {
            k.trace(tracer);
            Trace::trace(v, tracer);
        }
        for name in self.fields.keys() {
            name.trace(tracer);
        }
    }
}

#[derive(Debug)]
pub struct VesInstance {
    // Should also include bound methods (lazily copied by default).
    fields: Vec<Value, ProxyAllocator>,
    ty: Cc<VesStruct>,
}

impl VesInstance {
    pub fn new(ty: Cc<VesStruct>) -> Self {
        let fields = from_elem_in(
            Value::None,
            ty.fields.len(),
            ty.get_context().proxy_allocator(),
        );
        Self { fields, ty }
    }

    #[inline]
    pub fn ty(&self) -> &Cc<VesStruct> {
        &self.ty
    }

    #[inline]
    pub fn get_property_slot(&self, name: &VesStrView) -> Option<u8> {
        self.ty.fields.get(name).copied()
    }

    #[inline]
    pub fn get_property(&self, name: &VesStrView) -> Option<&Value> {
        self.get_property_slot(name)
            .map(|slot| &self.fields[slot as usize])
    }

    #[inline]
    pub fn get_property_mut(&mut self, name: &VesStrView) -> Option<&mut Value> {
        let slot = self.get_property_slot(name);
        if let Some(slot) = slot {
            Some(self.fields.get_mut(slot as usize).unwrap())
        } else {
            None
        }
    }

    #[inline]
    pub fn get_by_slot_index(&self, slot: usize) -> Option<&Value> {
        self.fields.get(slot)
    }

    #[inline]
    pub fn get_by_slot_index_unchecked(&self, slot: usize) -> &Value {
        debug_assert!(slot < self.fields.len());
        unsafe { self.fields.get_unchecked(slot) }
    }

    #[inline]
    pub fn get_by_slot_index_unchecked_mut(&mut self, slot: usize) -> &mut Value {
        debug_assert!(slot < self.fields.len());
        unsafe { self.fields.get_unchecked_mut(slot) }
    }

    #[inline]
    pub fn get_by_slot_index_mut(&mut self, slot: usize) -> Option<&mut Value> {
        self.fields.get_mut(slot)
    }
}

impl Trace for VesInstance {
    fn trace(&self, tracer: &mut ves_cc::Tracer) {
        Trace::trace(&self.ty, tracer);
        for v in &self.fields {
            v.trace(tracer);
        }
    }
}
