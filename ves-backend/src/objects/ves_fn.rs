use std::fmt::{self, Display, Formatter};

use ves_error::FileId;

use crate::{
    emitter::{builder::Chunk, emit::UpvalueInfo},
    gc::{GcObj, Trace},
    Value, VesObject,
};

use super::{peel::Peeled, ves_str::view::VesStrView};

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

#[derive(Debug, Clone, Copy)]
pub struct Arity {
    /// The number of positional arguments this function accepts.
    pub positional: u32,
    /// The number of default arguments this function accepts.
    pub default: u32,
    /// Whether or not this function accepts rest arguments.
    pub rest: bool,
}

impl Arity {
    pub fn none() -> Self {
        Self {
            positional: 0,
            default: 0,
            rest: false,
        }
    }
}

impl std::fmt::Display for Arity {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[pos = {}, def = {}, rest =  {}]",
            self.positional, self.default, self.rest
        )
    }
}

#[derive(Debug)]
pub struct VesFn {
    pub name: VesStrView,
    /// The arity of the function
    pub arity: Arity,
    /// The function's code.
    pub chunk: Chunk,
    /// This function's source file ID
    pub file_id: FileId,
    /// Specifies whether the function is a magic method.
    pub is_magic_method: bool,
}

impl VesFn {
    pub fn name(&self) -> &str {
        self.name.str().as_ref()
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
        write!(f, "<fn {}>", self.name.str())
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
