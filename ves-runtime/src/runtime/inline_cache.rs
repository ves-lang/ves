//! Inspired by https://github.com/Laythe-lang/Laythe/blob/master/laythe_vm/src/cache.rs.

use std::ptr::NonNull;

use crate::{
    gc::GcObj,
    objects::ves_struct::{Function, VesStruct},
};

/// The cache entry for a field index ("slot") of a property on a struct.
#[derive(Debug, Clone)]
struct PropertyEntry {
    /// The type of the struct.
    ty: GcObj,
    /// The index of the cached field.
    slot: usize,
}

/// The cache entry for a method of a struct. The returned methods
/// are intended to be immediately called by the Vm and therefore are unbound.
#[derive(Debug, Clone)]
struct MethodEntry {
    /// The type of the struct.
    ty: GcObj,
    /// The cached method (unbound).
    method: NonNull<Function>,
}

#[derive(Debug, Clone)]
enum CacheEntry {
    Property(PropertyEntry),
    #[allow(unused)] // TODO: method caching
    Method(MethodEntry),
    Empty,
}

#[derive(Debug, Clone)]
pub struct InlineCache {
    /// TODO: consider making this more memory efficient
    cache: Vec<CacheEntry>,
}

impl InlineCache {
    pub fn new(cache_size: usize) -> Self {
        Self {
            cache: vec![CacheEntry::Empty; cache_size],
        }
    }

    /// Attempts to retrieve the cached field slot corresponding to the given instruction.
    /// Returns `None` if the cache slot is empty, stores a method, or has a different struct type.
    pub fn get_property_cache(&self, instruction: usize, ty: &NonNull<VesStruct>) -> Option<usize> {
        debug_assert!(instruction < self.cache.len());
        match unsafe { self.cache.get_unchecked(instruction) } {
            CacheEntry::Property(prop) => {
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
            *self.cache.get_unchecked_mut(instruction) = CacheEntry::Property(PropertyEntry {
                slot: property_slot,
                ty,
            })
        }
    }
}
