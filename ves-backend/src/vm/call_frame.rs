use std::ptr::NonNull;

use ves_error::{FileId, Span};

use crate::{
    emitter::{builder::Chunk, opcode::Opcode},
    gc::{GcObj, Trace, Tracer},
    values::{functions::Function, handle::Handle},
    NanBox, Value,
};

use super::inline_cache::InlineCache;

pub struct CallFrame {
    r#fn: Handle<Function>,
    chunk: NonNull<Chunk>,
    code: NonNull<Opcode>,
    code_len: usize,
    cache: NonNull<InlineCache>,
    defer_stack: Vec<GcObj>,
    captures: *mut Vec<NanBox>,

    pub(crate) stack_index: usize,
    pub(crate) return_address: usize,
}

impl CallFrame {
    pub fn new(
        mut r#fn: Handle<Function>,
        captures: *mut Vec<NanBox>,
        stack_index: usize,
        return_address: usize,
    ) -> Self {
        let chunk = unsafe { NonNull::new_unchecked(&mut r#fn.get_mut().chunk) };
        let code = unsafe { NonNull::new_unchecked(r#fn.get_mut().chunk.code.as_mut_ptr()) };
        let code_len = r#fn.get().chunk.code.len();
        let cache = unsafe { NonNull::new_unchecked(&mut r#fn.get_mut().chunk.cache) };

        Self {
            r#fn,
            defer_stack: Vec::new(),
            chunk,
            code,
            cache,
            code_len,
            captures,
            stack_index,
            return_address,
        }
    }

    pub fn main(r#fn: Handle<Function>) -> Self {
        Self::new(r#fn, std::ptr::null_mut(), 0, 0)
    }

    #[inline]
    pub fn code(&self) -> &[Opcode] {
        unsafe { std::slice::from_raw_parts(self.code.as_ptr(), self.code_len) }
    }

    #[inline]
    pub fn code_mut(&mut self) -> &mut [Opcode] {
        unsafe { std::slice::from_raw_parts_mut(self.code.as_ptr(), self.code_len) }
    }

    pub fn file_id(&self) -> FileId {
        unsafe { self.chunk.as_ref().file_id }
    }

    pub fn span(&self, idx: usize) -> Span {
        unsafe { self.chunk.as_ref().spans.get(idx).unwrap().clone() }
    }

    pub fn func(&self) -> &Function {
        self.r#fn.get()
    }

    pub fn captures(&self) -> &Vec<NanBox> {
        if cfg!(debug_assertions) && self.captures.is_null() {
            panic!("Current CallFrame has no captures");
        }
        unsafe { &*self.captures }
    }

    pub fn captures_mut(&mut self) -> &mut Vec<NanBox> {
        if cfg!(debug_assertions) && self.captures.is_null() {
            panic!("Current CallFrame has no captures");
        }
        unsafe { &mut *self.captures }
    }

    #[cfg(not(feature = "fast"))]
    pub fn constants(&self) -> &[Value] {
        &self.func().chunk.constants[..]
    }

    #[cfg(feature = "fast")]
    #[inline]
    pub fn constants(&self) -> &[Value] {
        unsafe { &self.chunk.as_ref().constants }
    }

    #[inline]
    pub fn cache_mut(&mut self) -> &mut InlineCache {
        unsafe { self.cache.as_mut() }
    }

    #[inline]
    pub fn cache(&self) -> &InlineCache {
        unsafe { self.cache.as_ref() }
    }

    #[inline]
    pub fn code_len(&self) -> usize {
        self.code_len
    }

    #[cfg(feature = "fast")]
    #[inline]
    pub fn inst(&self, idx: usize) -> Opcode {
        unsafe { *self.bytecode.add(idx) }
    }

    #[cfg(not(feature = "fast"))]
    #[inline]
    pub fn inst(&self, idx: usize) -> Opcode {
        self.code()[idx]
    }
}

unsafe impl Trace for CallFrame {
    fn trace(&mut self, tracer: &mut dyn Tracer) {
        Trace::trace(&mut self.r#fn, tracer);
        for func in &mut self.defer_stack {
            Trace::trace(func, tracer);
        }
        for value in self.captures_mut() {
            value.trace(tracer);
        }
    }

    fn after_forwarding(&mut self) {
        self.r#fn.after_forwarding();
        for func in &mut self.defer_stack {
            func.after_forwarding();
        }
    }
}
