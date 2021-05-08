use std::ptr::NonNull;

use ves_error::VesFileDatabase;
use ves_middle::registry::ModuleRegistry;

use crate::{
    gc::{GcHandle, GcObj, SharedPtr, Trace, VesGc},
    Value,
};

pub mod call_frame;
pub mod inline_cache;
pub mod vm;

#[derive(Clone)]
pub struct VmGlobals {
    actual_globals: SharedPtr<Vec<Option<Value>>>,
    ptr: NonNull<Vec<Option<Value>>>,
}

impl VmGlobals {
    pub fn new(n: usize) -> Self {
        let actual_globals = SharedPtr::new(vec![None; n]);
        let ptr = NonNull::new(SharedPtr::into_raw(actual_globals.clone()) as *mut _).unwrap();
        Self {
            actual_globals,
            ptr,
        }
    }

    #[inline]
    fn vec(&self) -> &Vec<Option<Value>> {
        unsafe { self.ptr.as_ref() }
    }

    #[inline]
    fn vec_mut(&mut self) -> &mut Vec<Option<Value>> {
        unsafe { self.ptr.as_mut() }
    }

    pub fn len(&self) -> usize {
        self.vec().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn get(&self, n: usize) -> Option<&Value> {
        self.vec().get(n).and_then(|x| x.as_ref())
    }

    #[inline]
    pub fn get_mut(&mut self, n: usize) -> Option<&mut Value> {
        self.vec_mut().get_mut(n).and_then(|x| x.as_mut())
    }

    #[inline]
    pub fn set(&mut self, n: usize, v: Value) -> Option<()> {
        self.vec_mut()[n] = Some(v);
        Some(())
    }

    /// # Safety
    /// The index must be within the length of the global array.
    #[inline]
    pub unsafe fn get_unchecked(&self, n: usize) -> Option<&Value> {
        self.vec().get_unchecked(n).as_ref()
    }

    /// # Safety
    /// The index must be within the length of the global array.
    #[inline]
    pub unsafe fn get_unchecked_mut(&mut self, n: usize) -> Option<&mut Value> {
        self.vec_mut().get_unchecked_mut(n).as_mut()
    }
}

unsafe impl Trace for VmGlobals {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        for global in self.vec_mut().iter_mut().filter_map(|g| g.as_mut()) {
            Trace::trace(global, tracer);
        }
    }
}

impl Drop for VmGlobals {
    fn drop(&mut self) {
        std::mem::drop(unsafe { SharedPtr::from_raw(self.ptr.as_ptr()) });
    }
}

// TODO: think through what exactly this needs to hold.
pub struct Context<T: VesGc> {
    gc: GcHandle<T>,
    db: VesFileDatabase<String, String>,
    registry: ModuleRegistry<()>,
    globals: VmGlobals,
}

#[cfg(tests)]
#[ves_testing::ves_test_suite]
pub mod suite {}
