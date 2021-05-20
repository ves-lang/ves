use std::{
    cell::{Ref, RefCell, RefMut, UnsafeCell},
    fmt::{self, Formatter},
};

use crate::{
    gc::{proxy_allocator::ProxyAllocator, GcHandle, GcObj, SharedPtr, VesGc},
    runtime::vm::VmInterface,
    value::RuntimeError,
};
use ahash::RandomState;
use hashbrown::HashMap;
use ibig::IBig;

use super::{
    cache_layer::{CacheLayer, PropertyLookup},
    ves_fn::wrap_native,
    ves_str::view::VesStrView,
    ves_struct::ViewKey,
    Value,
};

use super::macros;

use derive_trace::Trace;

pub type AHashMap<K, V, A> = HashMap<K, V, RandomState, A>;
pub type VesHashMap<K, V> = HashMap<K, V, RandomState, ProxyAllocator>;

#[derive(Debug, Trace)]
pub struct VesIntVTable {
    methods: VesHashMap<ViewKey, (u8, GcObj)>,
}

impl VesIntVTable {
    fn init<T: VesGc>(mut handle: GcHandle<T>, lookup: IntVTableLookup) -> Self {
        let proxy = handle.proxy();

        let methods = macros::define_int_methods!(handle, lookup, proxy,
            "add" => LHS +,
            "radd" => RHS +,
            "sub" => LHS -,
            "rsub" => RHS -,
            "mul" => LHS *,
            "rmul" => RHS *,
            "div" => LHS /,
            "rdiv" => RHS /,
            "rem" => LHS %,
            "rrem" => RHS %,
            "cmp" => CMP ?,
            "pow" => POW ?,
            "rpow" => RPOW ?
        );

        Self { methods }
    }
}

#[derive(Clone, Debug, Trace)]
pub struct IntVTableLookup(SharedPtr<RefCell<VesIntVTable>>);
impl IntVTableLookup {
    pub fn create<T: VesGc>(handle: GcHandle<T>) -> Self {
        let mut lookup = Self(SharedPtr::new(RefCell::new(VesIntVTable {
            methods: VesHashMap::new_in(handle.proxy()),
        })));
        let vtable = VesIntVTable::init(handle, lookup.clone());
        lookup.update(vtable);
        lookup
    }

    pub fn update(&mut self, table: VesIntVTable) {
        *self.table_mut() = table;
    }

    fn table_mut(&mut self) -> RefMut<'_, VesIntVTable> {
        (*self.0).borrow_mut()
    }

    fn table(&self) -> Ref<'_, VesIntVTable> {
        self.0.borrow()
    }

    fn get_methods(&self, proxy: ProxyAllocator) -> Vec<Value, ProxyAllocator> {
        let n = self.table().methods.len();
        let mut v = Vec::with_capacity_in(n, proxy);
        v.extend(std::iter::repeat(Value::None).take(n));
        for (idx, method) in self.table().methods.values() {
            *v.get_mut(*idx as usize).unwrap() = Value::Ref(*method);
        }
        v
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

#[derive(Debug, Trace)]
pub struct VesInt {
    pub value: IBig,
    slots: CacheLayer<IntVTableLookup, Value, ProxyAllocator>,
}

impl VesInt {
    pub fn new(int: IBig, lookup: IntVTableLookup, proxy: ProxyAllocator) -> Self {
        let methods = lookup.get_methods(proxy);
        let slots = CacheLayer::new(lookup, methods);
        Self { value: int, slots }
    }

    pub fn props(&self) -> &CacheLayer<IntVTableLookup, Value, ProxyAllocator> {
        &self.slots
    }

    pub fn props_mut(&mut self) -> &mut CacheLayer<IntVTableLookup, Value, ProxyAllocator> {
        &mut self.slots
    }
}

impl std::fmt::Display for VesInt {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}
