use std::{collections::LinkedList, ptr::NonNull};

use crate::Value;

use super::{
    proxy_allocator::ProxyAllocator, GcBox, GcHeader, GcObj, GcRcObj, Roots, SharedPtr, Trace,
    VesGc,
};

pub const DEFAULT_INITIAL_THRESHOLD: usize = std::mem::size_of::<GcBox>() * 1000; // 1000 objects
pub const DEFAULT_HEAP_GROWTH_FACTOR: f64 = 1.4;

/// A naive mark-and-sweep linked-list based garbage collector.
#[derive(Debug)]
pub struct NaiveMarkAndSweep {
    bytes_allocated: ProxyAllocator,
    next_gc: usize,
    used_space_ratio: f64,
    objects: LinkedList<GcBox>,
    /// Permanent space isn't traced since the objects here aren't in the linked list.
    permanent_space: Vec<NonNull<GcBox>>,
    shared_space: Vec<GcRcObj>,
}

impl Drop for NaiveMarkAndSweep {
    fn drop(&mut self) {
        std::mem::take(&mut self.permanent_space)
            .into_iter()
            .for_each(|ptr| unsafe {
                std::mem::drop(Box::from_raw(ptr.as_ptr()));
            })
    }
}

impl Default for NaiveMarkAndSweep {
    fn default() -> Self {
        Self::new(DEFAULT_INITIAL_THRESHOLD, DEFAULT_HEAP_GROWTH_FACTOR)
    }
}

impl NaiveMarkAndSweep {
    pub fn new(initial_threshold: usize, heap_growth_factor: f64) -> Self {
        Self {
            bytes_allocated: ProxyAllocator::new(),
            next_gc: initial_threshold,
            used_space_ratio: 1.0 / heap_growth_factor,
            objects: LinkedList::new(),
            permanent_space: Vec::new(),
            shared_space: Vec::new(),
        }
    }

    fn collect(&mut self) {
        let mut cursor = self.objects.cursor_front_mut();
        while let Some(obj) = cursor.current() {
            if !obj.header.marked {
                self.bytes_allocated.release(std::mem::size_of::<GcBox>());
                // println!("[GC] dropping obj {:?}", obj);
                cursor.remove_current();
            } else {
                obj.header.marked = false;
                cursor.move_next();
            }
        }
    }

    fn trace<'s, 'data, I>(&mut self, roots: Roots<'s, 'data, I>)
    where
        I: Iterator<Item = &'data mut dyn Trace>,
    {
        // Since we don't do pointer forwarding here, we can work with GcBoxes directly.
        let mut worklist =
            Vec::with_capacity(self.bytes_allocated() / std::mem::size_of::<GcBox>());

        for root in roots.stack {
            if let Value::Ref(mut root) = root.unbox() {
                if !root.data().header.marked {
                    root.data().header.marked = true;
                    worklist.push(root.ptr);
                    self.trace_list(&mut worklist);
                }
            }
        }

        for data in roots.data {
            data.trace(&mut |obj| Self::tracer(&mut worklist, unsafe { obj.ptr.as_mut() }))
        }

        // QQQ: Should we trace the permanent space? If we don't, storing a non-permanent pointer in a permanent object would be fatal.
        self.permanent_space
            .iter_mut()
            .for_each(|ptr| Self::tracer(&mut worklist, unsafe { ptr.as_mut() }));

        // NOTE: this may segfault
        self.shared_space
            .iter_mut()
            .map(|rc| unsafe { (rc.obj.ptr.clone()).as_mut() })
            .for_each(|obj| Self::tracer(&mut worklist, obj));

        self.trace_list(&mut worklist);
        assert!(worklist.is_empty());
    }

    fn trace_list(&mut self, worklist: &mut Vec<NonNull<GcBox>>) {
        while !worklist.is_empty() {
            let obj = unsafe { worklist.pop().unwrap().as_mut() };
            obj.data
                .trace(&mut |child| Self::tracer(worklist, unsafe { child.ptr.as_mut() }));
        }
    }

    fn tracer(worklist: &mut Vec<NonNull<GcBox>>, obj: &mut GcBox) {
        if !obj.header.marked {
            obj.header.marked = true;
            worklist.push(unsafe { NonNull::new_unchecked(obj) })
        }
    }
}

impl VesGc for NaiveMarkAndSweep {
    fn alloc<'s, 'data, I>(
        &mut self,
        v: impl Into<crate::VesObject>,
        roots: super::Roots<'s, 'data, I>,
    ) -> Result<GcObj, std::alloc::AllocError>
    where
        I: Iterator<Item = &'data mut dyn Trace>,
    {
        // TODO: use log
        #[cfg(feature = "gc-debug")]
        {
            eprintln!("[GC] Preparing to allocate an object ...");
            eprintln!(
                "[GC] Allocated = {}, Next GC = {}",
                self.bytes_allocated(),
                self.next_gc
            );
        }

        if self.bytes_allocated() > self.next_gc {
            self.force_collect(roots);
            #[cfg(feature = "gc-debug")]
            eprintln!(
                "[GC] Performed a collection. New heap size: {}",
                self.bytes_allocated()
            );
        }

        if self.bytes_allocated() as f64 > self.next_gc as f64 * self.used_space_ratio {
            self.next_gc = (self.bytes_allocated() as f64 / self.used_space_ratio) as usize;
            #[cfg(feature = "gc-debug")]
            {
                eprintln!("[GC] Next GC has ben updated to {}", self.next_gc);
            }
        }

        let obj = v.into();
        self.bytes_allocated.bump(std::mem::size_of::<GcBox>());

        self.objects.push_back(GcBox {
            data: obj,
            header: GcHeader::default(),
        });

        let ptr = unsafe { NonNull::new_unchecked(self.objects.back_mut().unwrap()) };

        Ok(GcObj { ptr })
    }

    fn force_collect<'s, 'data, I>(&mut self, roots: super::Roots<'s, 'data, I>)
    where
        I: Iterator<Item = &'data mut dyn Trace>,
    {
        self.trace(roots);
        self.collect();
    }

    fn alloc_permanent(&mut self, v: impl Into<crate::VesObject>) -> GcObj {
        self.permanent_space.push(unsafe {
            NonNull::new_unchecked(Box::leak(Box::new(GcBox {
                data: v.into(),
                header: GcHeader::default(),
            })))
        });
        GcObj {
            ptr: *self.permanent_space.last().unwrap(),
        }
    }

    fn make_shared(&mut self, obj: GcObj) -> GcRcObj {
        let rc = GcRcObj {
            obj: SharedPtr::new(obj),
        };
        self.shared_space.push(rc.clone());
        rc
    }

    fn bytes_allocated(&self) -> usize {
        self.bytes_allocated.bytes_allocated()
    }

    fn proxy(&self) -> ProxyAllocator {
        self.bytes_allocated.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::NaiveMarkAndSweep;
    use crate::gc::GcHandle;

    #[test]
    fn generic_naive_mark_and_sweep_test() {
        let initial_threshold = 10;
        let factor = 1.2;
        let gc = NaiveMarkAndSweep::new(initial_threshold, factor);
        let handle = GcHandle::new(gc);

        crate::gc::tests::generic_gc_test(
            handle,
            crate::gc::tests::TestConfig {
                name: "naive-mark-sweep",
                seed: Some(1620272182),
                iterations: 10,
                stack_size: 1000,
                permanent_space_size: 300,
                drop_chance: 0.50,
            },
        )
    }
}
