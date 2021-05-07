use std::{
    fmt::{self, Display, Formatter},
    ptr::NonNull,
};

use ves_error::FileId;

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
    pub name: GcObj,
    /// How many positional arguments this function accepts
    pub positionals: u32,
    /// How many default arguments this function accepts
    pub defaults: u32,
    /// Whether or not this function accepts rest arguments
    pub rest: bool,
    pub chunk: Chunk,
    /// This function's source file ID
    pub file_id: FileId,
}

unsafe impl Trace for VesFn {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        self.name.trace(tracer);
    }
}

impl Display for VesFn {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // TODO: better formatting
        write!(f, "<fn {}>", self.name.as_str().unwrap())
    }
}

impl Display for VesClosure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        unsafe { self.r#fn.as_ref().fmt(f) }
    }
}

impl Display for ClosureDescriptor {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Descriptor")
            .field(&self.fn_constant_index)
            .field(&self.upvalues.len())
            .finish()
    }
}
