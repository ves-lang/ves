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
    actual_globals: SharedPtr<(Vec<Option<Value>>, Vec<String>)>,
    ptr: NonNull<Vec<Option<Value>>>,
}

impl VmGlobals {
    pub fn new(names: Vec<String>) -> Self {
        let actual_globals = SharedPtr::new((vec![None; names.len()], names));
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

#[cfg(test)]
#[ves_testing::ves_test_suite]
pub mod suite {
    #[ves_tests = "tests/vm"]
    mod vm {
        #[ok_callback]
        use super::_impl::compile_and_run;
    }

    mod _impl {
        use std::collections::HashMap;

        use ves_error::ErrCtx;
        use ves_middle::{ves_path::VesPath, ImportConfig, VesMiddle};

        use crate::{
            emitter::{emit::Emitter, CompilationContext},
            gc::{DefaultGc, GcHandle},
            runtime::{vm::Vm, VmGlobals},
        };

        pub fn compile_and_run(src: String) -> String {
            let mut mid = VesMiddle::<()>::new(
                ImportConfig {
                    ves_path: VesPath::default().unwrap().unwrap(),
                    variables: std::collections::HashMap::new(),
                }
                .into(),
            );

            match mid.process_snippet(src) {
                Ok(_) => {}
                Err(_) => {
                    return mid.report_to_string();
                }
            }

            let gc = GcHandle::new(DefaultGc::default());

            let mut result = mid.map_modules(|ast| {
                Emitter::new(
                    ast,
                    CompilationContext {
                        gc: gc.clone(),
                        strings: &mut HashMap::new(),
                    },
                )
                .emit()
                .map_err(ErrCtx::with_error)
            });

            if result.had_error() {
                return result.report_to_string();
            }

            let mut globals = result
                .registry
                .globals()
                .iter()
                .map(|((_, name), idx)| (*idx, name.clone()))
                .collect::<Vec<_>>();

            globals.sort_by_key(|g| g.0);

            let globals = VmGlobals::new(globals.into_iter().map(|(_, name)| name).collect());

            let mut modules = result.get_output_unchecked();
            assert_eq!(modules.len(), 1); // TODO: multiple modules

            let entry = modules.pop().unwrap();

            let mut output = Vec::new();
            let mut vm = Vm::with_writer(gc, globals, &mut output);

            match vm.run(entry) {
                Ok(_) => String::from_utf8(output).unwrap(),
                Err(e) => result.db.report_one_to_string(&e).unwrap(),
            }
        }
    }
}
