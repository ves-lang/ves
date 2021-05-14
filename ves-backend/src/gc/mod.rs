use std::{
    cell::RefCell,
    fmt::{self, Display, Formatter},
    ops::{Deref, DerefMut},
    ptr::NonNull,
    rc::Rc,
};

use crate::{NanBox, VesObject};

use self::proxy_allocator::ProxyAllocator;

pub mod naive;
pub mod proxy_allocator;

pub type SharedPtr<T> = Rc<T>;

/// A managed pointer to a [`VesObject`].
pub type VesRef = GcObj;
/// A non-null raw pointer to a managed [`VesObject`].
pub type VesPtr = NonNull<GcBox>;
/// A raw pointer to a managed [`VesObject`] that _may_ but _shouldn't_ be null.
pub type VesRawPtr = *mut GcBox;

pub type DefaultGc = naive::NaiveMarkAndSweep;

#[derive(Debug)]
pub struct GcHandle<T: VesGc> {
    gc: SharedPtr<RefCell<T>>,
}

impl<T: VesGc> Clone for GcHandle<T> {
    fn clone(&self) -> Self {
        Self {
            gc: SharedPtr::clone(&self.gc),
        }
    }
}

impl<T: VesGc> GcHandle<T> {
    pub fn new(gc: T) -> Self {
        Self {
            gc: SharedPtr::new(RefCell::new(gc)),
        }
    }

    fn gc_mut(&mut self) -> std::cell::RefMut<'_, T> {
        (*self.gc).borrow_mut()
    }

    fn gc(&self) -> std::cell::Ref<'_, T> {
        (*self.gc).borrow()
    }
}

impl<T: VesGc> VesGc for GcHandle<T> {
    #[inline]
    fn alloc<'s, 'data, I>(
        &mut self,
        v: impl Into<VesObject>,
        roots: Roots<'s, 'data, I>,
    ) -> Result<GcObj, std::alloc::AllocError>
    where
        I: Iterator<Item = &'data mut dyn Trace>,
    {
        self.gc_mut().alloc(v, roots)
    }

    #[inline]
    fn alloc_permanent(&mut self, v: impl Into<VesObject>) -> GcObj {
        self.gc_mut().alloc_permanent(v)
    }

    #[inline]

    fn force_collect<'s, 'data, I>(&mut self, roots: Roots<'s, 'data, I>)
    where
        I: Iterator<Item = &'data mut dyn Trace>,
    {
        self.gc_mut().force_collect(roots)
    }

    #[inline]
    fn make_shared(&mut self, obj: GcObj) -> GcRcObj {
        self.gc_mut().make_shared(obj)
    }

    #[inline]
    fn bytes_allocated(&self) -> usize {
        self.gc().bytes_allocated()
    }

    #[inline]
    fn proxy(&self) -> ProxyAllocator {
        self.gc().proxy()
    }
}

pub struct Roots<'s, 'data, I>
where
    I: Iterator<Item = &'data mut dyn Trace>,
{
    pub stack: &'s mut Vec<NanBox>,
    pub data: I,
}

impl<'s, 'data> Roots<'s, 'data, std::iter::Empty<&'data mut dyn Trace>> {
    pub fn with_stack(stack: &'s mut Vec<NanBox>) -> Self {
        Self {
            stack,
            data: std::iter::empty(),
        }
    }

    pub fn and_data<I>(self, data: I) -> Roots<'s, 'data, I>
    where
        I: Iterator<Item = &'data mut dyn Trace>,
    {
        Roots {
            data,
            stack: self.stack,
        }
    }
}

pub trait VesGc {
    fn alloc<'s, 'cs, 'data, I>(
        &mut self,
        v: impl Into<VesObject>,
        roots: Roots<'s, 'data, I>,
    ) -> Result<GcObj, std::alloc::AllocError>
    where
        I: Iterator<Item = &'data mut dyn Trace>;

    fn force_collect<'s, 'data, I>(&mut self, roots: Roots<'s, 'data, I>)
    where
        I: Iterator<Item = &'data mut dyn Trace>;

    /// Allocate the given object in the permanent space.
    fn alloc_permanent(&mut self, v: impl Into<VesObject>) -> GcObj;

    fn make_shared(&mut self, obj: GcObj) -> GcRcObj;

    fn bytes_allocated(&self) -> usize;

    fn proxy(&self) -> ProxyAllocator;
}

pub unsafe trait Trace {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj));

    fn after_forwarding(&mut self) {}
}

#[derive(Debug, Default)]
pub struct GcHeader {
    marked: bool,
    // more metadata here
}

#[derive(Debug)]
pub struct GcBox {
    header: GcHeader,
    data: VesObject,
}

// TODO: figure out a way to make this safer using lifetimes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GcObj {
    ptr: NonNull<GcBox>,
}

impl Deref for GcObj {
    type Target = VesObject;

    fn deref(&self) -> &Self::Target {
        unsafe { &self.ptr.as_ref().data }
    }
}

impl DerefMut for GcObj {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data().data
    }
}

impl GcObj {
    pub fn new(ptr: VesPtr) -> Self {
        Self { ptr }
    }

    #[inline]
    pub fn ptr_eq(&self, other: &GcObj) -> bool {
        self.ptr.as_ptr() == other.ptr.as_ptr()
    }

    pub(super) fn data(&mut self) -> &mut GcBox {
        unsafe { self.ptr.as_mut() }
    }

    pub fn ptr(&self) -> VesPtr {
        self.ptr
    }
}

unsafe impl Trace for GcObj {
    #[inline]
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        tracer(self)
    }

    fn after_forwarding(&mut self) {
        let obj = &mut **self;
        obj.after_forwarding();
    }
}

unsafe impl<T: Trace> Trace for &mut Vec<T> {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        self.iter_mut().for_each(|obj| obj.trace(tracer));
    }

    fn after_forwarding(&mut self) {
        self.iter_mut().for_each(|obj| obj.after_forwarding())
    }
}

#[derive(Debug, Clone)]
pub struct GcRcObj {
    obj: Rc<GcObj>,
}

impl Deref for GcRcObj {
    type Target = GcObj;

    fn deref(&self) -> &Self::Target {
        &*self.obj
    }
}

impl Display for GcObj {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        (&**self).fmt(f)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use crate::{
        gc::{Roots, Trace},
        objects::{
            ves_str::view::VesStrView,
            ves_struct::{VesInstance, VesStruct},
        },
        NanBox, Value, VesObject,
    };

    use super::{GcHandle, GcObj, VesGc};

    use rand::prelude::*;
    use rand::rngs::StdRng;
    use rand::SeedableRng;
    #[derive(Debug, Clone)]
    pub struct TestConfig {
        pub name: &'static str,
        pub seed: Option<u64>,
        pub iterations: usize,
        pub stack_size: usize,
        pub permanent_space_size: usize,
        pub drop_chance: f64,
    }

    macro_rules! roots {
        ($stack:expr, $structs:expr) => {
            Roots::with_stack($stack).and_data($structs.iter_mut().map(|obj| obj as &mut dyn Trace))
        };
    }

    #[allow(unused)]
    pub fn generic_gc_test<T: VesGc>(mut handle: GcHandle<T>, config: TestConfig) {
        let seed = config.seed.unwrap_or_else(|| {
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs()
        });

        eprintln!("[GC TEST: `{}`] CONFIG: {:#?}", config.name, config);
        eprintln!("[GC TEST: `{}`] SEED: {}", config.name, seed);

        let mut stack = Vec::new();
        let mut structs = Vec::new();
        let mut rng = StdRng::seed_from_u64(seed);

        for _ in 0..config.permanent_space_size {
            // handle.alloc_permanent(gen_object(
            //     &mut rng,
            //     &mut stack,
            //     &mut structs,
            //     handle.clone(),
            // ));
            // handle.alloc_permanent(random_string(&mut rng, 15));
            handle.alloc_permanent(gen_struct(
                &mut rng,
                &mut stack,
                &mut structs,
                handle.clone(),
            ));
            assert!(stack.is_empty());
            assert!(structs.is_empty());
        }

        let permanent_bytes = handle.bytes_allocated();
        handle.force_collect(Roots::with_stack(&mut stack));
        eprintln!("{} -> {}", permanent_bytes, handle.bytes_allocated());
        assert_eq!(handle.bytes_allocated(), permanent_bytes);

        eprintln!(
            "[GC TEST: `{}`] PERM BYTES: {}",
            config.name, permanent_bytes
        );

        for i in 0..config.iterations {
            for j in 0..config.stack_size {
                let nanbox = match rng.gen_bool(0.3) {
                    true => match rng.gen_range(0..3) {
                        0 => NanBox::from(rng.gen::<f64>()),
                        1 => NanBox::from(rng.gen::<bool>()),
                        2 => NanBox::new(Value::None),
                        _ => unreachable!(),
                    },
                    false => {
                        let obj = gen_object(&mut rng, &mut stack, &mut structs, handle.clone());
                        let was_struct = matches!(obj, VesObject::Struct(_));
                        let ptr = handle.alloc(obj, roots!(&mut stack, structs)).unwrap();
                        if was_struct {
                            structs.push(ptr);
                        }
                        NanBox::from(ptr)
                    }
                };
                stack.push(nanbox);
            }

            if rng.gen_bool(config.drop_chance) {
                stack.clear();
            }
            if rng.gen_bool(config.drop_chance) {
                structs.clear();
            }
        }

        stack.clear();
        structs.clear();

        handle.force_collect(roots!(&mut stack, structs));

        assert_eq!(handle.bytes_allocated(), permanent_bytes);
    }

    fn gen_object<T: VesGc>(
        rng: &mut StdRng,
        stack: &mut Vec<NanBox>,
        structs: &mut Vec<GcObj>,
        handle: GcHandle<T>,
    ) -> VesObject {
        match rng.gen_range(0..3) {
            0 => random_string(rng, 50).into(),
            1 => gen_struct(rng, stack, structs, handle).into(),
            2 if structs.is_empty() => gen_struct(rng, stack, structs, handle).into(),
            2 => {
                let ty = *structs.choose(rng).unwrap();
                // println!("{:?} {:?}", ty, structs);
                // println!("{:?} {:#?}", ty, &*ty);
                VesInstance::new(ty, handle.proxy()).into()
            }
            _ => unreachable!(),
        }
    }

    fn random_string(rng: &mut StdRng, len: usize) -> String {
        std::iter::repeat(())
            .take(len)
            .map(|_| rng.gen::<char>())
            .collect::<String>()
    }

    fn gen_struct<T: VesGc>(
        rng: &mut StdRng,
        stack: &mut Vec<NanBox>,
        structs: &mut Vec<GcObj>,
        mut handle: GcHandle<T>,
    ) -> VesStruct {
        let mut fields = Vec::new_in(handle.proxy());

        for _ in 0..rng.gen_range(5..10) {
            let s = handle
                .alloc(random_string(rng, 15), roots!(stack, structs))
                .unwrap();
            stack.push(NanBox::from(s));
            fields.push(VesStrView::new(s));
        }

        let name = handle
            .alloc(random_string(rng, 10), roots!(stack, structs))
            .unwrap();

        for _ in 0..fields.len() {
            stack.pop();
        }

        VesStruct::new(
            crate::objects::ves_str::view::VesStrView::new(name),
            &fields,
            0,
        )
    }
}
