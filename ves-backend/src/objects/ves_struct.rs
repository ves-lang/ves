use std::{
    cell::UnsafeCell,
    fmt::{self, Debug, Display, Formatter},
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

impl ViewKey {
    #[inline]
    pub fn str(&self) -> &str {
        let view = unsafe { &*self.view.get() };
        view.str().as_ref()
    }
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
    pub fields: Vec<VesStrView, ProxyAllocator>,
    // The indices of the methods' constant slots.
    pub methods: Vec<(u32, u32), ProxyAllocator>,
    /// Field arity (rest field is ignored)
    pub arity: Arity,
}

unsafe impl Trace for StructDescriptor {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        Trace::trace(&mut self.name, tracer);
        for field in &mut self.fields {
            Trace::trace(field, tracer);
        }
    }
}

#[derive(Debug)]
pub struct VesStruct {
    name: VesStrView,
    pub arity: Arity,
    fields: VesHashMap<ViewKey, u8>,
    vtable: VesHashMap<ViewKey, (u8, GcObj)>,
}

impl VesStruct {
    #[allow(clippy::ptr_arg)]
    pub fn new(
        name: VesStrView,
        arity: Arity,
        fields: &Vec<VesStrView, ProxyAllocator>,
        vtable_size: usize,
    ) -> Self {
        Self {
            name,
            arity,
            vtable: VesHashMap::with_capacity_in(vtable_size, fields.allocator().clone()),
            fields: fields
                .iter()
                .enumerate()
                .map(|(i, name)| {
                    (
                        ViewKey {
                            view: UnsafeCell::new(*name),
                        },
                        i as u8,
                    )
                })
                .collect(),
        }
    }

    pub fn name(&self) -> &str {
        self.name.str()
    }

    /// Adds the given method to the struct's vtalbe.
    #[inline]
    pub fn add_method(&mut self, name: ViewKey, value: GcObj) {
        let n = self.vtable.len();
        self.vtable.insert(name, (n as u8, value));
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
        Trace::trace(&mut self.name, tracer);
        for (name, _) in &mut self.fields {
            Trace::trace(unsafe { &mut *name.view.get() }, tracer);
        }
        for (name, (_, ptr)) in &mut self.vtable {
            Trace::trace(unsafe { &mut *name.view.get() }, tracer);
            Trace::trace(ptr, tracer);
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

#[derive(Debug, Clone)]
pub struct MethodLookup(Peeled<VesStruct>);
impl PropertyLookup for MethodLookup {
    fn lookup_slot(&self, name: &VesStrView) -> Option<usize> {
        self.0
            .get()
            .vtable
            .get(&ViewKey {
                view: UnsafeCell::new(*name),
            })
            .copied()
            .map(|(x, _)| x as _)
    }
}

#[derive(Debug, Clone)]
pub struct MethodEntry {
    pub method: Value,
    pub is_bound: bool,
}

unsafe impl Trace for MethodEntry {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        Trace::trace(&mut self.method, tracer);
    }
}

unsafe impl Trace for MethodLookup {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        Trace::trace(&mut self.0, tracer);
    }
}

#[derive(Debug)]
pub struct VesInstance {
    // NOTE: Methods and fields are separated into two cache lines to optimize for field access speed.
    //       Since a method may need to be bound after retrieval, storing methods and fields together
    //       would introduce the check overhead to field access, which is not desirable as raw field accesses
    //       are much more common than raw method accesses.
    fields: CacheLayer<Peeled<VesStruct>, Value, ProxyAllocator>,
    methods: CacheLayer<MethodLookup, MethodEntry, ProxyAllocator>,
}

impl VesInstance {
    pub fn new(ty: GcObj, proxy: ProxyAllocator) -> Self {
        let ty_instance = ty.as_struct().unwrap();

        let fields = from_elem_in(Value::None, ty_instance.fields.len(), proxy.clone());
        let mut methods = from_elem_in(
            MethodEntry {
                is_bound: false,
                method: Value::None,
            },
            ty_instance.vtable.len(),
            proxy,
        );
        for (_, (i, obj)) in &ty_instance.vtable {
            methods[*i as usize].method = Value::Ref(*obj);
        }

        let lookup = Peeled::new(ty, VesObject::as_struct_mut_unwrapped);
        let method_lookup = MethodLookup(Peeled::new(ty, VesObject::as_struct_mut_unwrapped));
        Self {
            fields: CacheLayer::new(lookup, fields),
            methods: CacheLayer::new(method_lookup, methods),
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

    #[inline]
    pub fn fields(&self) -> &CacheLayer<Peeled<VesStruct>, Value, ProxyAllocator> {
        &self.fields
    }

    #[inline]
    pub fn fields_mut(&mut self) -> &mut CacheLayer<Peeled<VesStruct>, Value, ProxyAllocator> {
        &mut self.fields
    }

    #[inline]
    pub fn methods(&self) -> &CacheLayer<MethodLookup, MethodEntry, ProxyAllocator> {
        &self.methods
    }

    #[inline]
    pub fn methods_mut(&mut self) -> &mut CacheLayer<MethodLookup, MethodEntry, ProxyAllocator> {
        &mut self.methods
    }
}

unsafe impl Trace for VesInstance {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        Trace::trace(&mut self.fields, tracer);
        Trace::trace(&mut self.methods, tracer);
    }
}

impl Display for VesStruct {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "<struct {}>", self.name.str())
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

struct DebugAsDisplay<'a, T: Debug + Display>(&'a T);
impl<'a, T: Debug + Display> Debug for DebugAsDisplay<'a, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self.0, f)
    }
}

impl Display for VesInstance {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // TODO: better formatting
        let mut s = f.debug_struct(self.ty().name());
        // NOTE this nested loop is needed to maintain order without allocations
        for (i0, value) in self.fields().slots().iter().enumerate() {
            for (key, i1) in self.ty().fields.iter() {
                if *i1 as usize == i0 {
                    s.field(key.str(), &DebugAsDisplay(&value));
                }
            }
        }
        for (i0, _) in self.methods().slots().iter().enumerate() {
            for (key, (i1, method)) in self.ty().vtable.iter() {
                if *i1 as usize == i0 {
                    s.field(key.str(), &DebugAsDisplay(&method));
                }
            }
        }
        s.finish()
    }
}
