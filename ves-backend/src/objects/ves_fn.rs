use std::{
    borrow::Cow,
    convert::{TryFrom, TryInto},
};
use std::{
    fmt::{self, Display, Formatter},
    marker::PhantomData,
};

use ves_error::FileId;

use crate::{
    emitter::{builder::Chunk, emit::UpvalueInfo},
    gc::{GcObj, Trace},
    runtime::vm::VmInterface,
    value::{FromVes, IntoVes, RuntimeError},
    ves_object::FnNative,
    Value, VesObject,
};

use super::{peel::Peeled, ves_str::view::VesStrView};

#[derive(Debug)]
pub struct VesClosure {
    r#fn: Peeled<VesFn>,
    pub upvalues: Vec<Value>,
}
impl VesClosure {
    pub fn new(r#fn: GcObj) -> Self {
        Self {
            r#fn: Peeled::new(r#fn, VesObject::as_fn_mut_unwrapped),
            upvalues: vec![],
        }
    }

    pub fn r#fn(&self) -> &VesFn {
        self.r#fn.get()
    }

    pub fn fn_mut(&mut self) -> &mut VesFn {
        self.r#fn.get_mut()
    }
}

unsafe impl Trace for VesClosure {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        Trace::trace(&mut self.r#fn, tracer);
        for value in self.upvalues.iter_mut() {
            value.trace(tracer);
        }
    }
}

#[derive(Debug, Clone)]
pub struct ClosureDescriptor {
    pub fn_constant_index: u32,
    pub upvalues: Vec<UpvalueInfo>,
}

#[derive(Debug, Clone, Copy)]
pub struct Arity {
    /// The number of positional arguments this function accepts.
    pub positional: u32,
    /// The number of default arguments this function accepts.
    pub default: u32,
    /// Whether or not this function accepts rest arguments.
    pub rest: bool,
}

impl Arity {
    pub fn none() -> Self {
        Self {
            positional: 0,
            default: 0,
            rest: false,
        }
    }
}

impl std::fmt::Display for Arity {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[pos = {}, def = {}, rest =  {}]",
            self.positional, self.default, self.rest
        )
    }
}

#[derive(Debug)]
pub struct VesFn {
    pub name: VesStrView,
    /// The arity of the function
    pub arity: Arity,
    /// The function's code.
    pub chunk: Chunk,
    /// This function's source file ID
    pub file_id: FileId,
    /// Specifies whether the function is a magic method.
    pub is_magic_method: bool,
}

impl VesFn {
    pub fn name(&self) -> &str {
        self.name.str().as_ref()
    }
}

unsafe impl Trace for VesFn {
    fn trace(&mut self, tracer: &mut dyn FnMut(&mut GcObj)) {
        self.name.trace(tracer);
    }
}

impl Display for VesFn {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // TODO: better formatting
        write!(f, "<fn {}>", self.name.str())
    }
}

impl Display for VesClosure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.r#fn.get().fmt(f)
    }
}

impl Display for ClosureDescriptor {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Descriptor")
            .field(&self.fn_constant_index)
            .field(&self.upvalues.len())
            .finish()
    }
}

pub struct Args<'v>(pub(crate) &'v mut Vec<Value>);

macro_rules! impl_try_from_args_for_tuple {
    () => {
        impl<'v> TryFrom<Args<'v>> for () {
            type Error = RuntimeError;
            fn try_from(_: Args<'v>) -> Result<(), Self::Error> {
                Ok(())
            }
        }
        impl<'v> TryFrom<Args<'v>> for (&'v [Value],) {
            type Error = RuntimeError;
            fn try_from(args: Args<'v>) -> Result<(&'v [Value],), Self::Error> {
                let args = args.0;
                Ok((&args[0..args.len()],))
            }
        }
    };
    (1, $name:ident) => {
        #[allow(non_snake_case)]
        impl<'v, $name> TryFrom<Args<'v>> for ($name,)
        where
            $name: FromVes,
        {
            type Error = RuntimeError;
            fn try_from(args: Args<'v>) -> Result<($name,), Self::Error> {
                let args = args.0;
                if args.len() != 1 {
                    return Err(RuntimeError::new(format!("Arity mismatch: expected {}, got {}", 1, args.len())));
                }
                args.reverse();
                let $name = $name::from_ves(args.pop().unwrap())?;
                Ok(($name,))
            }
        }
        #[allow(non_snake_case)]
        impl<'v, $name> TryFrom<Args<'v>> for ($name, &'v [Value])
        where
            $name: FromVes
        {
            type Error = RuntimeError;
            fn try_from(args: Args<'v>) -> Result<($name, &'v [Value]), Self::Error> {
                let args = args.0;
                if args.len() < 1 {
                    return Err(RuntimeError::new(format!("Arity mismatch: expected at least {}, got {}", 1, args.len())));
                }
                args.reverse();
                let $name = $name::from_ves(args.pop().unwrap())?;
                args.reverse();
                Ok(($name, &args[0..args.len()]))
            }
        }
    };
    ($size:expr, $($name:ident),*) => {
        #[allow(non_snake_case)]
        impl<'v, $($name),*> TryFrom<Args<'v>> for ($($name),*)
        where
            $($name: FromVes,)*
        {
            type Error = RuntimeError;
            fn try_from(args: Args<'v>) -> Result<($($name),*,), Self::Error> {
                let arity = $size;
                let args = args.0;
                if args.len() != arity {
                    return Err(RuntimeError::new(format!("Arity mismatch: expected {}, got {}", arity, args.len())));
                }
                args.reverse();
                $(let $name = $name::from_ves(args.pop().unwrap())?;)*
                Ok(($($name),*))
            }
        }
        #[allow(non_snake_case)]
        impl<'v, $($name),*> TryFrom<Args<'v>> for ($($name),*, &'v [Value])
        where
            $($name: FromVes,)*
        {
            type Error = RuntimeError;
            fn try_from(args: Args<'v>) -> Result<($($name),*, &'v [Value]), Self::Error> {
                let arity = $size;
                let args = args.0;
                if args.len() < arity {
                    return Err(RuntimeError::new(format!("Arity mismatch: expected at least {}, got {}", arity, args.len())));
                }
                args.reverse();
                $(let $name = $name::from_ves(args.pop().unwrap())?;)*
                args.reverse();
                Ok(($($name),*, &args[0..args.len()]))
            }
        }
    };
}
impl_try_from_args_for_tuple!();
impl_try_from_args_for_tuple!(1, A);
impl_try_from_args_for_tuple!(2, A, B);
impl_try_from_args_for_tuple!(3, A, B, C);
impl_try_from_args_for_tuple!(4, A, B, C, D);
impl_try_from_args_for_tuple!(5, A, B, C, D, E);
impl_try_from_args_for_tuple!(6, A, B, C, D, E, F);
impl_try_from_args_for_tuple!(7, A, B, C, D, E, F, G);
impl_try_from_args_for_tuple!(8, A, B, C, D, E, F, G, H);
impl_try_from_args_for_tuple!(9, A, B, C, D, E, F, G, H, I);
impl_try_from_args_for_tuple!(10, A, B, C, D, E, F, G, H, I, J);
impl_try_from_args_for_tuple!(11, A, B, C, D, E, F, G, H, I, J, K);
impl_try_from_args_for_tuple!(12, A, B, C, D, E, F, G, H, I, J, K, L);

pub trait Callable<'v, A>
where
    A: TryFrom<Args<'v>>,
{
    // TODO: accept some kind of VmInterface here, for allocating objects and so on
    fn ves_call(&self, vm: &'v mut dyn VmInterface, args: Args<'v>) -> Result<Value, RuntimeError>;
}

impl<'v, A, R, F> Callable<'v, A> for F
where
    A: TryFrom<Args<'v>, Error = RuntimeError>,
    R: IntoVes,
    F: Fn(&'v mut dyn VmInterface, A) -> Result<R, RuntimeError>,
{
    fn ves_call(&self, vm: &'v mut dyn VmInterface, args: Args<'v>) -> Result<Value, RuntimeError> {
        let args: A = args.try_into()?;
        (*self)(vm, args).map(|v| v.into_ves())
    }
}

pub struct CallableWrapper<C, A> {
    func: C,
    name: Cow<'static, str>,
    is_magic: bool,
    _args: PhantomData<A>,
}

impl<C, A> CallableWrapper<C, A> {
    pub fn new(func: C) -> Self {
        Self {
            func,
            name: "<fn: native>".into(),
            is_magic: false,
            _args: PhantomData,
        }
    }

    pub fn with_name(func: C, name: impl Into<Cow<'static, str>>) -> Self {
        Self {
            func,
            name: name.into(),
            is_magic: false,
            _args: PhantomData,
        }
    }

    pub fn with_name_and_magic(
        func: C,
        name: impl Into<Cow<'static, str>>,
        is_magic: bool,
    ) -> Self {
        Self {
            func,
            name: name.into(),
            is_magic,
            _args: PhantomData,
        }
    }
}

pub fn wrap<A, R, F>(f: F, name: &'static str) -> CallableWrapper<F, A>
where
    F: for<'v> Callable<'v, A> + Fn(&mut dyn VmInterface, A) -> Result<R, RuntimeError>,
    A: for<'v> TryFrom<Args<'v>, Error = RuntimeError>,
    R: IntoVes,
{
    CallableWrapper::with_name(f, name)
}

pub fn wrap_with_magic<A, R, F>(f: F, name: &'static str, is_magic: bool) -> CallableWrapper<F, A>
where
    F: for<'v> Callable<'v, A> + Fn(&mut dyn VmInterface, A) -> Result<R, RuntimeError>,
    A: for<'v> TryFrom<Args<'v>, Error = RuntimeError>,
    R: IntoVes,
{
    CallableWrapper::with_name_and_magic(f, name, is_magic)
}

pub fn wrap_native<A, R, F>(f: F, name: &'static str, is_magic: bool) -> Box<dyn FnNative>
where
    F: for<'v> Callable<'v, A> + Fn(&mut dyn VmInterface, A) -> Result<R, RuntimeError> + 'static,
    A: for<'v> TryFrom<Args<'v>, Error = RuntimeError> + 'static,
    R: IntoVes,
{
    Box::new(wrap_with_magic(f, name, is_magic))
}

unsafe impl<'v, C, A> Trace for CallableWrapper<C, A>
where
    C: Callable<'v, A>,
    A: TryFrom<Args<'v>, Error = RuntimeError>,
{
    fn trace(&mut self, _tracer: &mut dyn FnMut(&mut GcObj)) {}
}

impl<A, C> crate::ves_object::FnNative for CallableWrapper<C, A>
where
    C: for<'v> Callable<'v, A>,
    A: for<'v> TryFrom<Args<'v>, Error = RuntimeError>,
{
    fn call<'a>(
        &mut self,
        vm: &'a mut dyn crate::runtime::vm::VmInterface,
        args: Args<'a>,
    ) -> Result<Value, ves_error::VesError> {
        self.func
            .ves_call(vm, args)
            .map_err(|e| vm.create_error(e.0.msg))
    }

    fn name(&self) -> &Cow<'static, str> {
        &self.name
    }

    fn is_magic(&self) -> bool {
        self.is_magic
    }
}

#[cfg(test)]
mod tests {
    use ves_middle::registry::ModuleRegistry;

    use crate::{
        gc::{DefaultGc, GcHandle, SharedPtr},
        runtime::{symbols::SymbolTable, vm::Vm, Context, VmGlobals},
        value::Result,
    };

    use super::*;

    #[test]
    fn calling_native() {
        fn something(
            _: &mut dyn VmInterface,
            (a, b, c, va): (i32, i32, Option<i32>, &[Value]),
        ) -> Result<i32> {
            let mut out = a + b * c.unwrap_or(0);
            for arg in va.iter() {
                out += i32::from_ves(*arg).unwrap();
            }
            Ok(out)
        }

        let handle = GcHandle::new(DefaultGc::default());
        let mut vm = Vm::<_, std::io::Stdout>::new(SharedPtr::new(Context::new(
            handle.clone(),
            ModuleRegistry::new(),
            VmGlobals::new(vec![]),
            SymbolTable::new(handle),
        )));
        let mut args = vec![Value::Int(2), Value::Int(5), Value::Int(3)];
        assert_eq!(
            something.ves_call(&mut vm, Args(&mut args)).unwrap(),
            Value::Int(17)
        );
        let mut args = vec![Value::Int(2), Value::Int(5), Value::None];
        assert_eq!(
            something.ves_call(&mut vm, Args(&mut args)).unwrap(),
            Value::Int(2)
        );
        let mut args = vec![
            Value::Int(2),
            Value::Int(2),
            Value::Int(2),
            Value::Int(2),
            Value::Int(2),
            Value::Int(2),
        ];
        assert_eq!(
            something.ves_call(&mut vm, Args(&mut args)).unwrap(),
            Value::Int(2 * 6)
        );

        fn fallible(_: &mut dyn VmInterface, _: ()) -> Result<()> {
            Err(RuntimeError::new("Something went wrong"))
        }
        assert_eq!(
            fallible.ves_call(&mut vm, Args(&mut vec![])).unwrap_err(),
            RuntimeError::new("Something went wrong")
        );

        let wrapper = wrap(fallible, "fallible");
        assert_eq!(wrapper.name(), "fallible");

        let wrapper = wrap_native(fallible, "fallible", false);
        assert_eq!(wrapper.name(), "fallible");
        assert!(!wrapper.is_magic());
    }
}
