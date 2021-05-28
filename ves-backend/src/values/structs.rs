use std::{
    cell::UnsafeCell,
    fmt::{self, Debug, Display, Formatter},
    vec::from_elem_in,
};

use crate::{
    gc::{proxy_allocator::ProxyAllocator, GcObj},
    value::Stringify,
    NanBox, Object,
};
use ahash::RandomState;
use hashbrown::HashMap;

use super::{
    cache_layer::{CacheLayer, PropertyLookup},
    functions::Arity,
    handle::Handle,
    strings::StrView,
    Value,
};

use derive_trace::Trace;

pub type AHashMap<K, V, A> = HashMap<K, V, RandomState, A>;
pub type VesHashMap<K, V> = HashMap<K, V, RandomState, ProxyAllocator>;

pub struct ViewKey {
    pub(super) view: UnsafeCell<StrView>,
}

impl ViewKey {
    #[inline]
    pub fn str(&self) -> &str {
        let view = unsafe { &*self.view.get() };
        view.str().as_ref()
    }

    #[inline]
    pub fn raw_ptr(&self) -> *mut StrView {
        self.view.get()
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
            crate::Object::Str(_) => ViewKey {
                view: UnsafeCell::new(StrView::new(obj)),
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

#[derive(Debug, Trace)]
pub struct StructDescriptor {
    pub name: StrView,
    /// The initializer method of the struct.
    pub init: Option<u32>,
    pub fields: Vec<StrView, ProxyAllocator>,
    // The indices of the methods' constant slots.
    pub methods: Vec<(u32, u32), ProxyAllocator>,
    /// Field arity (rest field is ignored)
    pub arity: Arity,
}

#[derive(Debug, Trace)]
pub struct Struct {
    name: StrView,
    pub arity: Arity,
    init: Option<GcObj>,
    fields: VesHashMap<ViewKey, u8>,
    vtable: VesHashMap<ViewKey, (u8, GcObj)>,
}

impl Struct {
    #[allow(clippy::ptr_arg)]
    pub fn new(
        name: StrView,
        arity: Arity,
        init: Option<GcObj>,
        fields: &Vec<StrView, ProxyAllocator>,
        vtable_size: usize,
    ) -> Self {
        Self {
            name,
            arity,
            init,
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

    #[inline]
    pub fn init(&self) -> Option<&GcObj> {
        self.init.as_ref()
    }

    /// Adds the given method to the struct's vtalbe.
    #[inline]
    pub fn add_method(&mut self, name: ViewKey, value: GcObj) {
        let n = self.vtable.len();
        self.vtable.insert(name, (n as u8, value));
    }
}

impl PropertyLookup for Handle<Struct> {
    #[inline]
    fn lookup_slot(&self, name: &StrView) -> Option<usize> {
        self.get()
            .fields
            .get(&ViewKey {
                view: UnsafeCell::new(*name),
            })
            .copied()
            .map(|x| x as _)
    }
}

#[derive(Debug, Clone, Trace)]
pub struct MethodLookup(Handle<Struct>);
impl PropertyLookup for MethodLookup {
    fn lookup_slot(&self, name: &StrView) -> Option<usize> {
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

#[derive(Debug, Clone, Trace)]
pub struct MethodEntry {
    pub method: Value,
    pub is_bound: bool,
}

#[derive(Debug, Trace)]
pub struct Instance {
    // NOTE: Methods and fields are separated into two cache lines to optimize for field access speed.
    //       Since a method may need to be bound after retrieval, storing methods and fields together
    //       would introduce the check overhead to field access, which is not desirable as raw field accesses
    //       are much more common than raw method accesses.
    fields: CacheLayer<Handle<Struct>, NanBox, ProxyAllocator>,
    methods: CacheLayer<MethodLookup, MethodEntry, ProxyAllocator>,
}

impl Instance {
    pub fn new(ty: GcObj, proxy: ProxyAllocator) -> Self {
        let ty_instance = ty.as_struct().unwrap();

        let fields = from_elem_in(NanBox::none(), ty_instance.fields.len(), proxy.clone());
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

        let lookup = Handle::new(ty, Object::as_struct_mut_unwrapped);
        let method_lookup = MethodLookup(Handle::new(ty, Object::as_struct_mut_unwrapped));
        Self {
            fields: CacheLayer::new(lookup, fields),
            methods: CacheLayer::new(method_lookup, methods),
        }
    }

    #[inline]
    pub fn ty_ptr(&self) -> &GcObj {
        self.fields.lookup().handle_ptr()
    }

    #[inline]
    pub fn ty(&self) -> &Struct {
        self.fields.lookup().get()
    }

    #[inline]
    pub fn ty_mut(&mut self) -> &mut Struct {
        self.fields.lookup_mut().get_mut()
    }

    #[inline]
    pub fn fields(&self) -> &CacheLayer<Handle<Struct>, NanBox, ProxyAllocator> {
        &self.fields
    }

    #[inline]
    pub fn fields_mut(&mut self) -> &mut CacheLayer<Handle<Struct>, NanBox, ProxyAllocator> {
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

impl Stringify for Struct {
    fn stringify(
        &self,
        _vm: &mut dyn crate::vm::vm::VmInterface,
    ) -> std::result::Result<String, ves_error::VesError> {
        Ok(self.to_string())
    }
}

impl Display for Struct {
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

impl Stringify for Instance {
    fn stringify(
        &self,
        vm: &mut dyn crate::vm::vm::VmInterface,
    ) -> std::result::Result<String, ves_error::VesError> {
        // TODO: better formatting
        let mut fields = Vec::with_capacity(self.fields.slots().len());

        // NOTE this nested loop is needed to maintain order without allocations
        for (i0, value) in self.fields().slots().iter().enumerate() {
            for (key, i1) in self.ty().fields.iter() {
                if *i1 as usize == i0 {
                    fields.push(format!("{}: {}", key.str(), vm.stringify(&value.unbox())?));
                }
            }
        }
        for (i0, _) in self.methods().slots().iter().enumerate() {
            for (key, (i1, method)) in self.ty().vtable.iter() {
                if *i1 as usize == i0 {
                    fields.push(format!(
                        "{}: {}",
                        key.str(),
                        vm.stringify(&Value::Ref(*method))?
                    ));
                }
            }
        }

        Ok(format!("{} {{ {} }}", self.ty().name(), fields.join(", ")))
    }
}

impl Display for Instance {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // TODO: better formatting
        let mut s = f.debug_struct(self.ty().name());
        // NOTE this nested loop is needed to maintain order without allocations
        for (i0, value) in self.fields().slots().iter().enumerate() {
            for (key, i1) in self.ty().fields.iter() {
                if *i1 as usize == i0 {
                    s.field(key.str(), &DebugAsDisplay(&value.unbox()));
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
