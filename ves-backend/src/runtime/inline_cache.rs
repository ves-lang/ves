//! Inspired by https://github.com/Laythe-lang/Laythe/blob/master/laythe_vm/src/cache.rs.

use crate::gc::{GcObj, Trace};

/// The cache entry for a field index ("slot") of a property on a struct.
#[derive(Debug, Clone)]
struct CacheEntry {
    /// The type of the struct.
    ty: GcObj,
    /// The index of the cached field.
    slot: usize,
}

#[derive(Debug, Clone)]
pub struct InlineCache {
    /// TODO: consider making this more memory efficient
    cache: Vec<Option<CacheEntry>>,
}

impl InlineCache {
    pub fn new(cache_size: usize) -> Self {
        Self {
            cache: vec![None; cache_size],
        }
    }

    /// Attempts to retrieve the cached field slot corresponding to the given instruction.
    /// Returns `None` if the cache slot is empty.
    pub fn get_property_cache(&self, instruction: usize, ty: &GcObj) -> Option<usize> {
        debug_assert!(instruction < self.cache.len());
        match unsafe { self.cache.get_unchecked(instruction) } {
            Some(prop) => {
                // NOTE: this is a pointer comparison. VesStruct isn't clone, so it should always hold true for the same struct.
                if prop.ty.ptr_eq(ty) {
                    Some(prop.slot)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub fn update_property_cache(&mut self, instruction: usize, property_slot: usize, ty: GcObj) {
        debug_assert!(instruction < self.cache.len());
        unsafe {
            *self.cache.get_unchecked_mut(instruction) = Some(CacheEntry {
                slot: property_slot,
                ty,
            })
        }
    }
}

// XXX: should this be traced? Hypothetically, if we never dereference any pointer in the cache
// before comparing it with the given pointer, it is safe to have invalid pointers in the cache.
unsafe impl Trace for InlineCache {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        self.cache.iter_mut().for_each(|entry| match entry {
            Some(prop) => tracer(&mut prop.ty),
            None => (),
        })
    }
}
