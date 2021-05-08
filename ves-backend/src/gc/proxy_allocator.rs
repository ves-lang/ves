use std::{
    alloc::{Allocator, Global},
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};

/// A proxy allocator returned by a [`VesGc`]. Allocating and deallocating memory with this allocator
/// will be visible to the gc, allowing it to perform more accurate garbage collection if the memory usage exceeds some threshold.
/// This allocator is thread-safe.
#[derive(Default, Debug, Clone)]
pub struct ProxyAllocator(Arc<AtomicUsize>);

impl ProxyAllocator {
    /// Creates a new proxy allocator initialized to 0.
    pub fn new() -> Self {
        Self(Arc::new(AtomicUsize::new(0)))
    }

    /// Creates a new proxy allocator using the given arc.
    pub fn with_arc(arc: Arc<AtomicUsize>) -> Self {
        Self(arc)
    }

    /// Manually bumps the number of bytes that are currently allocated.
    #[inline]
    pub fn bump(&self, n: usize) -> usize {
        self.0.fetch_add(n, Ordering::SeqCst) + n
    }

    /// Manually reduces the number of bytes that are currently allocated.
    /// The calls to this function must match the calls to `bump()`.
    ///
    /// # Panics
    /// Panics if compiled with debug assertions.
    #[cfg(not(debug_assertions))]
    #[inline]
    pub fn release(&self, n: usize) -> usize {
        self.0.fetch_sub(n, Ordering::SeqCst).saturating_sub(n)
    }

    /// Manually reduces the number of bytes that are currently allocated.
    /// The calls to this function must match the calls to `bump()`.
    ///
    /// # Panics
    /// Panics if compiled with debug assertions.
    #[cfg(debug_assertions)]
    #[inline]
    pub fn release(&self, n: usize) -> usize {
        self.0
            .fetch_sub(n, Ordering::SeqCst)
            .checked_sub(n)
            .expect("The calls to bump() do not match the calls to release(). Something is freeing extra memory.")
    }

    /// Returns the number of bytes currently used by all objects allocated with this allocator.
    #[inline]
    pub fn bytes_allocated(&self) -> usize {
        self.0.load(Ordering::SeqCst)
    }
}

unsafe impl Allocator for ProxyAllocator {
    fn allocate(
        &self,
        layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        let ret = Global.allocate(layout)?;
        self.bump(layout.size());
        Ok(ret)
    }

    unsafe fn deallocate(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) {
        Global.deallocate(ptr, layout);
        self.release(layout.size());
    }
}

#[cfg(test)]
mod tests {
    #[allow(unused)]
    use super::*;

    #[test]
    pub fn test_proxy_allocator() {
        let proxy = ProxyAllocator::new();
        assert_eq!(proxy.bytes_allocated(), 0);

        let mut v = Vec::new_in(proxy.clone());
        for i in 0..10 {
            v.push(i);
        }

        assert_eq!(proxy.bytes_allocated(), 64);

        std::mem::drop(v);

        assert_eq!(proxy.bytes_allocated(), 0);
    }
}
