use std::{borrow::Cow, cell::RefCell, convert::TryInto};

use ves_error::VesError;

use crate::{
    gc::{GcHandle, SharedPtr, Trace, VesGc},
    runtime::vm::VmInterface,
    value::{RuntimeError, TypeId},
    ves_object::FnNative,
    Value, VesObject,
};

use super::{ves_fn::Arity, ves_str::view::VesStrView, ves_struct::VesHashMap};

pub type R<T> = Result<T, VesError>;

pub trait ObjNative: Trace {
    // Type name and id
    fn type_id(&self) -> TypeId;
    fn type_name(&self) -> Cow<'static, str>;

    // Shortcuts commonly called methods.
    fn get_item(&self, vm: &mut dyn VmInterface, key: Value) -> R<Value>;
    fn set_item(&self, vm: &mut dyn VmInterface, key: Value, value: Value) -> R<Value>;
    fn to_string(&self, vm: &mut dyn VmInterface) -> R<String>;

    // Property accesses. How do we handle method binding? Do we disallow it?
    // If we allow it, how do we implement it? Should we automatically perform binding, or notify the user in some way?
    fn get_property(
        &mut self,
        vm: &mut dyn VmInterface,
        slot: usize,
        name: &VesStrView,
    ) -> R<(usize, Value)>;

    fn set_property(
        &mut self,
        vm: &mut dyn VmInterface,
        slot: usize,
        name: &VesStrView,
        value: Value,
    ) -> R<(usize, Value)>;

    fn has_property(&self, name: &VesStrView) -> bool;
}

// outline the proc macro design here
/*

ves_native! {
    pub struct Pair {
        #[field]
        x: Value,
        #[field]
        y: Value
    }

    impl Pair {
        #[init]
        pub fn new(x: Value, y: Value) -> Self {
            Self { x, y }
        }

        #[intercept(x)]
        pub fn x(&mut self, vm: &mut dyn VmInterface, value: Option<Value>) -> R<Value> {
            if let Some(value) = value {
                if let Some(s) = value.as_str() {
                    if &**s == "apples" {
                        return Err(vm.create_error("Pair.x cannot store apples!".into()))
                    }
                }

                self.x = value;
                Ok(Value::None)
            } else {
                Ok(self.x)
            }
        }

        #[intercept(missing)]
        pub fn rest(&mut self, vm: &mut dyn VmInterface, name: &VewStrView, value: Option<Value>) -> R<Value> {
            Err(vm.create_error("super creative custom error message".into()))
        }
    }
}

*/
pub struct PairData {
    x: Value,
    y: Value,
}

impl PairData {
    pub fn new(x: Value, y: Value) -> Self {
        Self { x, y }
    }

    pub fn x(&mut self, vm: &mut dyn VmInterface, value: Option<Value>) -> R<Value> {
        if let Some(value) = value {
            if let Some(s) = value.as_str() {
                if &**s == "apples" {
                    return Err(vm.create_error("Pair.x cannot store apples!".into()));
                }
            }

            self.x = value;
            Ok(Value::None)
        } else {
            Ok(self.x)
        }
    }

    pub fn rest(
        &mut self,
        vm: &mut dyn VmInterface,
        name: &VesStrView,
        value: Option<Value>,
    ) -> R<Value> {
        Err(vm.create_error("super creative custom error message".into()))
    }
}

unsafe impl Trace for PairData {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut crate::gc::GcObj)) {
        Trace::trace(&mut self.x, tracer);
        Trace::trace(&mut self.y, tracer);
    }
}

pub struct PairVTable {
    fields: VesHashMap<&'static str, usize>,
}

unsafe impl Trace for PairVTable {
    fn trace(&mut self, _tracer: &mut dyn FnMut(&mut crate::gc::GcObj)) {}
}

#[derive(Clone)]
pub struct PairType {
    name: Cow<'static, str>,
    vtable: SharedPtr<RefCell<PairVTable>>,
}

impl PairType {
    pub fn new<T: VesGc>(gc: GcHandle<T>) -> Self {
        let mut fields = VesHashMap::new_in(gc.proxy());
        fields.insert("x", 0);
        fields.insert("y", 1);
        let vtable = SharedPtr::new(RefCell::new(PairVTable { fields }));
        Self {
            name: "Pair".into(),
            vtable,
        }
    }
}

unsafe impl Trace for PairType {
    fn trace(&mut self, _tracer: &mut dyn FnMut(&mut crate::gc::GcObj)) {}
}

impl FnNative for PairType {
    fn call<'a>(
        &mut self,
        vm: &'a mut dyn VmInterface,
        args: super::ves_fn::Args<'a>,
    ) -> Result<Value, VesError> {
        let (_, x, y): (Value, Value, Value) = args.try_into().map_err(|x: RuntimeError| x.0)?;
        let instance = Box::new(PairInstance::new(x, y, self.vtable.clone()));
        Ok(Value::Ref(vm.alloc(VesObject::ObjNative(instance))))
    }

    fn arity(&self) -> Arity {
        Arity::new(2, 0, false)
    }

    fn name(&self) -> &Cow<'static, str> {
        &self.name
    }

    fn is_magic(&self) -> bool {
        false
    }
}

pub struct PairInstance {
    data: PairData,
    vtable: SharedPtr<RefCell<PairVTable>>,
}

impl PairInstance {
    pub fn new(x: Value, y: Value, vtable: SharedPtr<RefCell<PairVTable>>) -> Self {
        Self {
            data: PairData::new(x, y),
            vtable,
        }
    }
}

unsafe impl Trace for PairInstance {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut crate::gc::GcObj)) {
        Trace::trace(&mut self.data, tracer);
        Trace::trace(&mut *self.vtable.borrow_mut(), tracer);
    }
}

impl ObjNative for PairInstance {
    fn type_id(&self) -> TypeId {
        TypeId(SharedPtr::as_ptr(&self.vtable) as usize)
    }

    fn type_name(&self) -> Cow<'static, str> {
        "Pair".into()
    }

    fn get_item(&self, vm: &mut dyn VmInterface, key: Value) -> R<Value> {
        todo!()
    }

    fn set_item(&self, vm: &mut dyn VmInterface, key: Value, value: Value) -> R<Value> {
        todo!()
    }

    fn to_string(&self, vm: &mut dyn VmInterface) -> R<String> {
        let x = vm.to_string(&self.data.x)?;
        let y = vm.to_string(&self.data.y)?;
        Ok(format!("Pair {{ x: {}, y: {} }}", x, y))
    }

    fn get_property(
        &mut self,
        vm: &mut dyn VmInterface,
        slot: usize,
        name: &VesStrView,
    ) -> R<(usize, Value)> {
        let slot = if slot == usize::MAX {
            self.vtable
                .borrow()
                .fields
                .get(&**name.str())
                .copied()
                .unwrap_or(slot)
        } else {
            slot
        };
        match slot {
            0 => PairData::x(&mut self.data, vm, None).map(|x| (0, x)),
            _ => PairData::rest(&mut self.data, vm, name, None).map(|x| (1, x)),
        }
    }

    fn set_property(
        &mut self,
        vm: &mut dyn VmInterface,
        slot: usize,
        name: &VesStrView,
        value: Value,
    ) -> R<(usize, Value)> {
        let slot = if slot == usize::MAX {
            self.vtable
                .borrow()
                .fields
                .get(&**name.str())
                .copied()
                .unwrap_or(slot)
        } else {
            slot
        };
        match slot {
            0 => PairData::x(&mut self.data, vm, Some(value)).map(|x| (0, x)),
            _ => PairData::rest(&mut self.data, vm, name, None).map(|x| (1, x)),
        }
    }

    fn has_property(&self, name: &VesStrView) -> bool {
        self.vtable.borrow().fields.get(&**name.str()).is_some()
    }
}
