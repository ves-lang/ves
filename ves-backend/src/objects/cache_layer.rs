use std::alloc::Allocator;

use crate::gc::{Trace, Tracer};

use super::ves_str::view::VesStrView;

pub trait PropertyLookup: Clone {
    fn lookup_slot(&self, name: &VesStrView) -> Option<usize>;
}

pub struct CacheLayer<L: PropertyLookup, V, A: Allocator> {
    lookup: L,
    slots: Vec<V, A>,
}

impl<L: PropertyLookup + std::fmt::Debug, V: std::fmt::Debug, A: Allocator> std::fmt::Debug
    for CacheLayer<L, V, A>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CacheLayer")
            .field("lookup", &self.lookup)
            .field("slots", &self.slots)
            .finish()
    }
}

impl<L: PropertyLookup, V, A: Allocator> CacheLayer<L, V, A> {
    pub fn new(lookup: L, slots: Vec<V, A>) -> CacheLayer<L, V, A> {
        Self { lookup, slots }
    }

    #[inline]
    pub fn slots(&self) -> &Vec<V, A> {
        &self.slots
    }

    #[inline]
    pub fn lookup(&self) -> &L {
        &self.lookup
    }

    #[inline]
    pub fn lookup_mut(&mut self) -> &mut L {
        &mut self.lookup
    }

    #[inline]
    pub fn get_slot_index(&self, name: &VesStrView) -> Option<usize> {
        self.lookup.lookup_slot(name)
    }

    #[inline]
    pub fn get_slot_value(&self, name: &VesStrView) -> Option<&V> {
        self.get_slot_index(name)
            .map(|slot| &self.slots[slot as usize])
    }

    #[inline]
    pub fn get_slot_value_mut(&mut self, name: &VesStrView) -> Option<&mut V> {
        let slot = self.get_slot_index(name);
        if let Some(slot) = slot {
            Some(self.slots.get_mut(slot as usize).unwrap())
        } else {
            None
        }
    }

    #[inline]
    pub fn get_by_slot_index(&self, slot: usize) -> Option<&V> {
        self.slots.get(slot)
    }

    #[inline]
    pub fn get_by_slot_index_mut(&mut self, slot: usize) -> Option<&mut V> {
        self.slots.get_mut(slot)
    }

    #[inline]
    pub fn get_by_slot_index_unchecked(&self, slot: usize) -> &V {
        debug_assert!(slot < self.slots.len());
        unsafe { self.slots.get_unchecked(slot) }
    }

    #[inline]
    pub fn get_by_slot_index_unchecked_mut(&mut self, slot: usize) -> &mut V {
        debug_assert!(slot < self.slots.len());
        unsafe { self.slots.get_unchecked_mut(slot) }
    }
}

unsafe impl<L: PropertyLookup + Trace, V: Trace, A: Allocator> Trace for CacheLayer<L, V, A> {
    fn trace(&mut self, tracer: &mut dyn Tracer) {
        Trace::trace(&mut self.lookup, tracer);
        for slot in &mut self.slots {
            Trace::trace(slot, tracer);
        }
    }

    fn after_forwarding(&mut self) {
        Trace::after_forwarding(&mut self.lookup);
        for slot in &mut self.slots {
            Trace::after_forwarding(slot);
        }
    }
}
