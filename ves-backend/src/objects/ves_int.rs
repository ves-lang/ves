use std::{
    cell::{Ref, RefCell, RefMut, UnsafeCell},
    fmt::{self, Formatter},
};

use crate::{
    gc::{proxy_allocator::ProxyAllocator, GcHandle, GcObj, SharedPtr, Trace, VesGc},
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

pub type AHashMap<K, V, A> = HashMap<K, V, RandomState, A>;
pub type VesHashMap<K, V> = HashMap<K, V, RandomState, ProxyAllocator>;

#[derive(Debug)]
pub struct VesIntVTable {
    methods: VesHashMap<ViewKey, (u8, GcObj)>,
}

impl VesIntVTable {
    fn init<T: VesGc>(mut handle: GcHandle<T>, lookup: IntVTableLookup) -> Self {
        let proxy = handle.proxy();
        let mut methods = VesHashMap::new_in(handle.proxy());

        // TODO: arithmetic methods here
        methods.insert(
            ViewKey::from(handle.alloc_permanent("add")),
            (
                0,
                handle.alloc_permanent(wrap_native(
                    move |vm: &mut dyn VmInterface, (left, right): (GcObj, Value)| {
                        let left = left.as_int_unchecked();

                        let result = match right {
                            Value::Int(i) => left.value.clone() + IBig::from(i),
                            Value::Ref(obj) if obj.as_int().is_some() => {
                                left.value.clone() + &obj.as_int_unchecked().value
                            }
                            rest => {
                                return Err(RuntimeError::new(format!(
                                    "Cannot add a big integer and `{}`",
                                    rest
                                )))
                            }
                        };

                        Ok(vm.alloc(VesInt::new(result, lookup.clone(), proxy.clone()).into()))
                    },
                    "add",
                    true,
                )),
            ),
        );

        Self { methods }
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

unsafe impl Trace for VesInt {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        Trace::trace(&mut self.slots, tracer);
    }
}

impl std::fmt::Display for VesInt {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}
