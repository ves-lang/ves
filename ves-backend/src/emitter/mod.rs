use std::{borrow::Cow, collections::HashMap};

use crate::{
    gc::{GcHandle, GcObj, VesGc},
    objects::ves_int::IntVTableLookup,
    Value, VesObject,
};

pub mod builder;
pub mod dis;
pub mod emit;
pub mod opcode;

pub type Result<T> = std::result::Result<T, ves_error::VesError>;

pub struct VTables {
    int: IntVTableLookup,
}

impl VTables {
    pub fn init<T: VesGc>(gc: GcHandle<T>) -> Self {
        Self {
            int: IntVTableLookup::create(gc),
        }
    }
}

pub struct CompilationContext<'a, 'b, T: VesGc> {
    pub(super) gc: GcHandle<T>,
    pub(super) strings: &'b mut HashMap<Cow<'a, str>, GcObj>,
    pub(super) vtables: &'b mut VTables,
}

impl<'a, 'b, T: VesGc> CompilationContext<'a, 'b, T> {
    pub fn new(
        gc: GcHandle<T>,
        strings: &'b mut HashMap<Cow<'a, str>, GcObj>,
        vtables: &'b mut VTables,
    ) -> Self {
        Self {
            gc,
            strings,
            vtables,
        }
    }

    pub fn alloc_or_intern(&mut self, s: impl Into<Cow<'a, str>>) -> GcObj {
        let s = s.into();
        if let Some(ptr) = self.strings.get(&s) {
            *ptr
        } else {
            let ptr = self.gc.alloc_permanent(s.to_string());
            self.strings.insert(s, ptr);
            ptr
        }
    }

    pub fn alloc_value(&mut self, v: impl Into<VesObject>) -> Value {
        Value::Ref(self.gc.alloc_permanent(v))
    }
}
