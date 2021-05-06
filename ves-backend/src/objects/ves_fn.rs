use std::ptr::NonNull;

use ves_error::FileId;

use super::ves_str::VesStr;

use crate::{
    emitter::{builder::Chunk, emit::UpvalueInfo},
    gc::{GcObj, Trace},
    Value,
};

#[derive(Debug)]
pub struct VesClosure {
    _fn: GcObj,
    r#fn: NonNull<VesFn>,
    pub upvalues: Vec<Value>,
}
impl VesClosure {
    pub fn new(r#fn: GcObj) -> Self {
        Self {
            r#fn: Self::get_raw(r#fn),
            _fn: r#fn,
            upvalues: vec![],
        }
    }
    fn get_raw(mut ptr: GcObj) -> NonNull<VesFn> {
        match &mut *ptr {
            crate::VesObject::Fn(f) => unsafe { NonNull::new_unchecked(f as *mut _) },
            _ => unreachable!(),
        }
    }
}

unsafe impl Trace for VesClosure {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        self._fn.trace(tracer);
        for value in self.upvalues.iter_mut() {
            value.trace(tracer);
        }
    }

    fn after_forwarding(&mut self) {
        self.r#fn = Self::get_raw(self._fn);
    }
}

#[derive(Debug, Clone)]
pub struct ClosureDescriptor {
    pub fn_constant_index: u32,
    pub upvalues: Vec<UpvalueInfo>,
}

#[derive(Debug)]
pub struct VesFn {
    name: VesStr,
    /// How many positional arguments this function accepts
    pub positionals: u32,
    /// How many default arguments this function accepts
    pub defaults: u32,
    /// Whether or not this function accepts rest arguments
    pub rest: bool,
    chunk: Chunk,
    /// This function's source file ID
    file_id: FileId,
}

unsafe impl Trace for VesFn {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        self.name.trace(tracer);
    }
}
