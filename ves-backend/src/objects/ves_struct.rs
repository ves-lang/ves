use std::{cell::UnsafeCell, ptr::NonNull, vec::from_elem_in};

use crate::gc::{proxy_allocator::ProxyAllocator, GcObj, Trace};
use ahash::RandomState;
use hashbrown::HashMap;

use super::{ves_str::view::VesStrView, Value};

pub type AHashMap<K, V, A> = HashMap<K, V, RandomState, A>;
pub type VesHashMap<K, V> = HashMap<K, V, RandomState, ProxyAllocator>;

pub struct ViewKey {
    view: UnsafeCell<VesStrView>,
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
            crate::VesObject::Instance(_) => panic!("Unexpected object type: instance"),
            crate::VesObject::Struct(_) => panic!("Unexpected object type: struct"),
            crate::VesObject::Fn(_) => panic!("Unexpected object type: fn"),
            crate::VesObject::Closure(_) => panic!("Unexpected object type: closure"),
            crate::VesObject::ClosureDescriptor(_) => {
                panic!("Unexpected object type: closure descriptor")
            }
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
pub struct VesStruct {
    methods: VesHashMap<ViewKey, GcObj>,
    fields: VesHashMap<ViewKey, u8>,
}

impl VesStruct {
    pub fn new(fields: VesHashMap<ViewKey, u8>, methods: VesHashMap<ViewKey, GcObj>) -> Self {
        Self { methods, fields }
    }
}

unsafe impl Trace for VesStruct {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        for (name, v) in &mut self.methods {
            Trace::trace(unsafe { &mut *name.view.get() }, tracer);
            Trace::trace(v, tracer);
        }
        for (name, _) in &mut self.fields {
            Trace::trace(unsafe { &mut *name.view.get() }, tracer);
        }
    }
}

#[derive(Debug)]
pub struct VesInstance {
    // Should also include bound methods (lazily copied by default).
    fields: Vec<Value, ProxyAllocator>,
    ty: GcObj,
    raw: NonNull<VesStruct>,
}

impl VesInstance {
    pub fn new(mut ty: GcObj, proxy: ProxyAllocator) -> Self {
        let raw = match &mut *ty {
            crate::VesObject::Struct(s) => NonNull::new(s as *mut _).unwrap(),
            rest => unreachable!("{:?}", rest),
        };
        let fields = from_elem_in(Value::None, ty.as_struct().unwrap().fields.len(), proxy);
        Self { fields, ty, raw }
    }

    #[inline]
    pub fn ty(&self) -> &VesStruct {
        unsafe { self.raw.as_ref() }
    }

    #[inline]
    pub fn ty_ptr(&self) -> &GcObj {
        &self.ty
    }

    #[inline]
    pub fn get_property_slot(&self, name: &VesStrView) -> Option<u8> {
        self.ty()
            .fields
            .get(&ViewKey {
                view: UnsafeCell::new(*name),
            })
            .copied()
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

unsafe impl Trace for VesInstance {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        Trace::trace(&mut self.ty, tracer);
        for v in &mut self.fields {
            v.trace(tracer);
        }
    }
}
