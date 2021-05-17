use std::{
    cell::{Cell, RefCell},
    collections::HashMap,
    marker::PhantomData,
    rc::Rc,
};

use crate::objects::ves_struct::{VesHashMap, ViewKey};

use super::GcObj;

pub unsafe trait Trace {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj));

    fn after_forwarding(&mut self) {}
}

unsafe impl<T: Trace, A: std::alloc::Allocator> Trace for Vec<T, A> {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        self.iter_mut().for_each(|obj| obj.trace(tracer));
    }

    fn after_forwarding(&mut self) {
        self.iter_mut().for_each(|obj| obj.after_forwarding())
    }
}

unsafe impl<K, V: Trace> Trace for HashMap<K, V> {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        self.values_mut().for_each(|v| Trace::trace(v, tracer))
    }
}

unsafe impl<V: Trace> Trace for VesHashMap<ViewKey, V> {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        for (name, v) in self {
            Trace::trace(unsafe { &mut *name.raw_ptr() }, tracer);
            Trace::trace(v, tracer);
        }
    }
}

unsafe impl<A: Trace, B: Trace> Trace for (A, B) {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        Trace::trace(&mut self.0, tracer);
        Trace::trace(&mut self.1, tracer);
    }
}

unsafe impl<T: Trace> Trace for Box<T>
where
    T: ?Sized,
{
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        Trace::trace(&mut **self, tracer)
    }
}

unsafe impl<T: Trace> Trace for Rc<RefCell<T>> {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        Trace::trace(&mut *RefCell::borrow_mut(self), tracer)
    }
}

unsafe impl<T> Trace for PhantomData<T> {
    fn trace(&mut self, _tracer: &mut dyn FnMut(&mut GcObj)) {}
}

unsafe impl<T: Trace> Trace for Option<T> {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        if let Some(obj) = self {
            Trace::trace(obj, tracer);
        }
    }

    fn after_forwarding(&mut self) {
        if let Some(obj) = self {
            Trace::after_forwarding(obj);
        }
    }
}

macro_rules! impl_empty_trace {
    ($T:ty) => {
        unsafe impl Trace for $T {
            fn trace(&mut self, _tracer: &mut dyn FnMut(&mut GcObj)) {}
        }
    };
    ($($T:ty),*) => {
        $(impl_empty_trace!($T);)*
    };
}

impl_empty_trace!(i8, i16, i32, i64, i128, isize);
impl_empty_trace!(u8, u16, u32, u64, u128, usize);
impl_empty_trace!(f32, f64);
impl_empty_trace!(ibig::IBig, ibig::UBig);
impl_empty_trace!((), bool, &str, String, std::borrow::Cow<'static, str>);
impl_empty_trace!(
    Cell<i8>,
    Cell<i16>,
    Cell<i32>,
    Cell<i64>,
    Cell<i128>,
    Cell<isize>
);
impl_empty_trace!(
    Cell<u8>,
    Cell<u16>,
    Cell<u32>,
    Cell<u64>,
    Cell<u128>,
    Cell<usize>
);
impl_empty_trace!(Cell<Option<u64>>);
