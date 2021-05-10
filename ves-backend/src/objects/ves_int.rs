use std::{
    cell::{Ref, RefCell, RefMut, UnsafeCell},
    fmt::{self, Formatter},
};

use crate::gc::{proxy_allocator::ProxyAllocator, GcHandle, GcObj, SharedPtr, Trace, VesGc};
use ahash::RandomState;
use hashbrown::HashMap;
use ibig::IBig;

use super::{
    cache_layer::{CacheLayer, PropertyLookup},
    ves_str::view::VesStrView,
    ves_struct::ViewKey,
    Value,
};

pub type AHashMap<K, V, A> = HashMap<K, V, RandomState, A>;
pub type VesHashMap<K, V> = HashMap<K, V, RandomState, ProxyAllocator>;

#[derive(Debug)]
pub struct VesIntVTable {
    methods: VesHashMap<ViewKey, (u8, GcObj)>,
}

impl VesIntVTable {
    pub fn init<T: VesGc>(handle: GcHandle<T>) -> SharedPtr<RefCell<Self>> {
        // TODO: arithmetic methods here
        SharedPtr::new(RefCell::new(Self {
            methods: VesHashMap::new_in(handle.proxy()),
        }))
    }
}

unsafe impl Trace for VesIntVTable {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        for (name, v) in &mut self.methods {
            Trace::trace(unsafe { &mut *name.view.get() }, tracer);
            Trace::trace(&mut v.1, tracer);
        }
    }
}

#[derive(Clone, Debug)]
pub struct IntVTableLookup(SharedPtr<RefCell<VesIntVTable>>);
impl IntVTableLookup {
    pub fn new(table: SharedPtr<RefCell<VesIntVTable>>) -> Self {
        Self(table)
    }

    fn table_mut(&mut self) -> RefMut<'_, VesIntVTable> {
        (*self.0).borrow_mut()
    }

    fn table(&self) -> Ref<'_, VesIntVTable> {
        self.0.borrow()
    }

    fn get_methods(&self, proxy: ProxyAllocator) -> Vec<Value, ProxyAllocator> {
        let mut v = Vec::with_capacity_in(self.table().methods.len(), proxy);
        v.fill(Value::None);
        for (idx, method) in self.table().methods.values() {
            *v.get_mut(*idx as usize).unwrap() = Value::Ref(*method);
        }
        v
    }
}

unsafe impl Trace for IntVTableLookup {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        Trace::trace(&mut *self.table_mut(), tracer);
    }
}

impl PropertyLookup for IntVTableLookup {
    fn lookup_slot(&self, name: &VesStrView) -> Option<usize> {
        self.table()
            .methods
            .get(&ViewKey {
                view: UnsafeCell::new(*name),
            })
            .map(|(slot, _)| *slot as _)
    }
}

#[derive(Debug)]
pub struct VesInt {
    int: IBig,
    slots: CacheLayer<IntVTableLookup, Value, ProxyAllocator>,
}

impl VesInt {
    pub fn new(int: IBig, lookup: IntVTableLookup, proxy: ProxyAllocator) -> Self {
        let methods = lookup.get_methods(proxy);
        let slots = CacheLayer::new(lookup, methods);
        Self { int, slots }
    }
}

unsafe impl Trace for VesInt {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        Trace::trace(&mut self.slots, tracer);
    }
}

impl std::fmt::Display for VesInt {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.int)
    }
}
