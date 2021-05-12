use std::ptr::NonNull;

use ves_error::{FileId, Span};

use crate::{
    emitter::{builder::Chunk, opcode::Opcode},
    gc::{GcObj, Trace},
    objects::ves_fn::VesFn,
    Value,
};

use super::inline_cache::InlineCache;

pub struct CallFrame {
    r#fn: GcObj,
    chunk: NonNull<Chunk>,
    code: NonNull<Opcode>,
    code_len: usize,
    cache: NonNull<InlineCache>,
    defer_stack: Vec<GcObj>,

    pub(crate) stack_index: usize,
    pub(crate) return_address: usize,
}

impl CallFrame {
    pub fn new(mut r#fn: GcObj, stack_index: usize, return_address: usize) -> Self {
        let obj = r#fn.as_fn_mut_unwrapped();
        let chunk = unsafe { NonNull::new_unchecked(&mut obj.chunk) };
        let code = unsafe { NonNull::new_unchecked(obj.chunk.code.as_mut_ptr()) };
        let code_len = obj.chunk.code.len();
        let cache = unsafe { NonNull::new_unchecked(&mut obj.chunk.cache) };

        Self {
            r#fn,
            defer_stack: Vec::new(),
            chunk,
            code,
            cache,
            code_len,
            stack_index,
            return_address,
        }
    }

    pub fn main(r#fn: GcObj) -> Self {
        Self::new(r#fn, 0, 0)
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

    pub fn func(&self) -> &VesFn {
        self.r#fn.as_fn().unwrap()
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
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        Trace::trace(&mut self.r#fn, tracer);
        for func in &mut self.defer_stack {
            Trace::trace(func, tracer);
        }
    }

    fn after_forwarding(&mut self) {
        self.r#fn.after_forwarding();
        for func in &mut self.defer_stack {
            func.after_forwarding();
        }
    }
}
