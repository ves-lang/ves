use std::fmt::{self, Display, Formatter};

use ves_error::FileId;

use crate::{
    emitter::{builder::Chunk, emit::UpvalueInfo},
    gc::{GcObj, Trace},
    Value, VesObject,
};

use super::peel::Peeled;

#[derive(Debug)]
pub struct VesClosure {
    r#fn: Peeled<VesFn>,
    pub upvalues: Vec<Value>,
}
impl VesClosure {
    pub fn new(r#fn: GcObj) -> Self {
        Self {
            r#fn: Peeled::new(r#fn, VesObject::as_fn_mut_unwrapped),
            upvalues: vec![],
        }
    }

    pub fn r#fn(&self) -> &VesFn {
        self.r#fn.get()
    }

    pub fn fn_mut(&mut self) -> &mut VesFn {
        self.r#fn.get_mut()
    }
}

unsafe impl Trace for VesClosure {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        Trace::trace(&mut self.r#fn, tracer);
        for value in self.upvalues.iter_mut() {
            value.trace(tracer);
        }
    }
}

#[derive(Debug, Clone)]
pub struct ClosureDescriptor {
    pub fn_constant_index: u32,
    pub upvalues: Vec<UpvalueInfo>,
}

#[derive(Debug)]
pub struct VesFn {
    // QQQ: use a stringview instead?
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

impl VesFn {
    pub fn name(&self) -> &str {
        self.name.as_str().unwrap()
    }
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
        self.r#fn.get().fmt(f)
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
