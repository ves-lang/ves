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

impl Trace for VesStruct {
    fn trace(&self, tracer: &mut ves_cc::Tracer) {
        for func in self.methods.values() {
            func.trace(tracer);
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
    #[inline]
    pub fn get_property(&self, name: &VesStrView) -> Option<&Value> {
        self.ty
            .fields
            .get(name)
            .copied()
            .map(|slot| &self.fields[slot as usize])
    }

    #[inline]
    pub fn get_by_slot_index(&self, slot: usize) -> Option<&Value> {
        self.fields.get(slot)
    }
}

impl Trace for VesInstance {
    fn trace(&self, tracer: &mut ves_cc::Tracer) {
        self.ty.trace(tracer);
        for v in &self.fields {
            v.trace(tracer);
        }
    }
}
