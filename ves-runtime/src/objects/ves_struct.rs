use std::vec::from_elem_in;

use ahash::RandomState;
use hashbrown::HashMap;
use ves_cc::{proxy_allocator::ProxyAllocator, Cc, Trace};

use super::{ves_str::VesStrView, Value};

pub type AHashMap<K, V, A> = HashMap<K, V, RandomState, A>;
pub type VesHashMap<K, V> = HashMap<K, V, RandomState, ProxyAllocator>;

// NOTE: A stub until we implement the compiler
#[derive(Debug)]
pub struct Function {}

impl Trace for Function {
    fn trace(&self, _tracer: &mut ves_cc::Tracer) {}
}

#[derive(Debug)]
pub struct VesStruct {
    methods: VesHashMap<VesStrView, Cc<Function>>,
    fields: VesHashMap<VesStrView, u8>,
}

impl VesStruct {
    pub fn new(
        fields: VesHashMap<VesStrView, u8>,
        methods: VesHashMap<VesStrView, Cc<Function>>,
    ) -> Self {
        Self { fields, methods }
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
    pub fn get_property(&self, name: &VesStrView) -> Option<&Value> {
        self.ty
            .fields
            .get(name)
            .copied()
            .map(|slot| &self.fields[slot as usize])
    }

    #[inline]
    pub fn get_property_mut(&mut self, name: &VesStrView) -> Option<&mut Value> {
        let slot = self.ty.fields.get(name).copied();
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
