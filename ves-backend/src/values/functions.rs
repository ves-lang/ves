use std::{
    borrow::Cow,
    convert::{TryFrom, TryInto},
};
use std::{
    fmt::{self, Display, Formatter},
    marker::PhantomData,
};

use ves_error::{FileId, VesError};

use crate::{
    emitter::{builder::Chunk, emit::CaptureInfo},
    gc::{GcObj, Trace, Tracer},
    value::{FromVes, IntoVes, RuntimeError, Stringify},
    vm::vm::VmInterface,
    NanBox, Object, Value,
};

use super::handle::Handle;
use super::strings::StrView;

use derive_trace::Trace;

pub trait FnNative: Trace {
    fn call<'a>(&mut self, vm: &'a mut dyn VmInterface, args: Args<'a>) -> Result<Value, VesError>;
    fn arity(&self) -> Arity;
    fn name(&self) -> &Cow<'static, str>;
    fn is_magic(&self) -> bool;
}

impl Stringify for &dyn FnNative {
    fn stringify(&self, _vm: &mut dyn VmInterface) -> std::result::Result<String, VesError> {
        Ok(format!("<fn native {} at {:p}", self.name(), self))
    }
}

#[derive(Debug, Trace)]
pub struct FnBound {
    r#fn: GcObj,
    receiver: NanBox,
}

impl FnBound {
    pub fn new(r#fn: GcObj, receiver: NanBox) -> Self {
        Self { r#fn, receiver }
    }

    #[inline]
    pub fn inner(&self) -> GcObj {
        self.r#fn
    }

    #[inline]
    pub fn receiver(&self) -> NanBox {
        self.receiver
    }
}

#[derive(Debug, Trace)]
pub struct FnClosure {
    r#fn: Handle<Function>,
    pub captures: Vec<NanBox>,
}
impl FnClosure {
    pub fn new(r#fn: GcObj) -> Self {
        Self {
            r#fn: Handle::new(r#fn, Object::as_fn_mut_unwrapped),
            captures: vec![],
        }
    }

    pub fn fn_ptr(&self) -> Handle<Function> {
        self.r#fn
    }

    pub fn r#fn(&self) -> &Function {
        self.r#fn.get()
    }

    pub fn fn_mut(&mut self) -> &mut Function {
        self.r#fn.get_mut()
    }
}

#[derive(Debug, Clone)]
pub struct ClosureDescriptor {
    pub fn_constant_index: u32,
    pub captures: Vec<CaptureInfo>,
}
unsafe impl crate::gc::Trace for ClosureDescriptor {
    fn trace(&mut self, _tracer: &mut dyn Tracer) {}
}

#[derive(Debug, Clone, Copy, Trace)]
pub struct Arity {
    /// The number of positional arguments this function accepts.
    pub positional: u32,
    /// The number of default arguments this function accepts.
    pub default: u32,
    /// Whether or not this function accepts rest arguments.
    pub rest: bool,
}

#[derive(Clone, Copy)]
pub enum ArgCountDiff {
    Equal,
    MissingPositional(usize),
    MissingDefaults(usize),
    Extra(usize),
}

impl Arity {
    pub fn new(positional: u32, default: u32, rest: bool) -> Self {
        Self {
            positional,
            default,
            rest,
        }
    }

    pub fn none() -> Self {
        Self {
            positional: 0,
            default: 0,
            rest: false,
        }
    }

    /// Returns the number of missing/extra args.
    pub fn diff(&self, n: usize) -> ArgCountDiff {
        if n < self.positional as usize {
            return ArgCountDiff::MissingPositional(self.positional as usize - n);
        }
        let diff = (self.positional + self.default) as isize - n as isize;
        match diff {
            n if n > 0 => ArgCountDiff::MissingDefaults(n as usize),
            n if n < 0 => ArgCountDiff::Extra((-n) as usize),
            _ => ArgCountDiff::Equal,
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
pub struct Function {
    pub name: StrView,
    /// The arity of the function
    pub arity: Arity,
    /// The function's code.
    pub chunk: Chunk,
    /// This function's source file ID
    pub file_id: FileId,
    /// Specifies whether the function is a magic method.
    pub is_magic_method: bool,
}

impl Function {
    pub fn name(&self) -> &str {
        self.name.str().as_ref()
    }
}

unsafe impl Trace for Function {
    fn trace(&mut self, tracer: &mut dyn Tracer) {
        self.name.trace(tracer);
    }
}

impl Stringify for Function {
    fn stringify(&self, _vm: &mut dyn VmInterface) -> std::result::Result<String, VesError> {
        Ok(self.to_string())
    }
}
impl Stringify for FnBound {
    fn stringify(&self, _vm: &mut dyn VmInterface) -> std::result::Result<String, VesError> {
        Ok(self.to_string())
    }
}
impl Stringify for FnClosure {
    fn stringify(&self, _vm: &mut dyn VmInterface) -> std::result::Result<String, VesError> {
        Ok(self.to_string())
    }
}

impl Display for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // TODO: better formatting
        write!(f, "<fn {}>", self.name.str())
    }
}

impl Display for FnBound {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "<fn {} -> {}>",
            match self
                .r#fn
                .as_closure()
                .map(|c| c.r#fn.get().name())
                .or_else(|| self.r#fn.as_fn().map(|f| f.name()))
            {
                Some(name) => {
                    name.to_string()
                }
                None => {
                    format!("{}", self.r#fn)
                }
            },
            self.receiver
                .as_ptr()
                .unwrap()
                .as_instance()
                .unwrap()
                .ty()
                .name(),
        )
    }
}

impl Display for FnClosure {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.r#fn.get().fmt(f)
    }
}

impl Display for ClosureDescriptor {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Descriptor")
            .field(&self.fn_constant_index)
            .field(&self.captures.len())
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

// ████████  ██████  ██████   ██████
//    ██    ██    ██ ██   ██ ██    ██
//    ██    ██    ██ ██   ██ ██    ██
//    ██    ██    ██ ██   ██ ██    ██
//    ██     ██████  ██████   ██████
//
// TODO: change native args deserialization to handle implicit receiver for non-instance functions
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
    arity: Arity,
    _args: PhantomData<A>,
}

impl<C, A> CallableWrapper<C, A> {
    pub fn new(func: C, arity: Arity) -> Self {
        Self {
            func,
            name: "<fn: native>".into(),
            is_magic: false,
            arity,
            _args: PhantomData,
        }
    }

    pub fn with_name(func: C, name: impl Into<Cow<'static, str>>, arity: Arity) -> Self {
        Self {
            func,
            name: name.into(),
            is_magic: false,
            arity,
            _args: PhantomData,
        }
    }

    pub fn with_name_and_magic(
        func: C,
        name: impl Into<Cow<'static, str>>,
        is_magic: bool,
        arity: Arity,
    ) -> Self {
        Self {
            func,
            name: name.into(),
            is_magic,
            arity,
            _args: PhantomData,
        }
    }
}

pub fn wrap<A, R, F>(f: F, name: &'static str, arity: Arity) -> CallableWrapper<F, A>
where
    F: for<'v> Callable<'v, A> + Fn(&mut dyn VmInterface, A) -> Result<R, RuntimeError>,
    A: for<'v> TryFrom<Args<'v>, Error = RuntimeError>,
    R: IntoVes,
{
    CallableWrapper::with_name(f, name, arity)
}

pub fn wrap_with_magic<A, R, F>(
    f: F,
    name: &'static str,
    is_magic: bool,
    arity: Arity,
) -> CallableWrapper<F, A>
where
    F: for<'v> Callable<'v, A> + Fn(&mut dyn VmInterface, A) -> Result<R, RuntimeError>,
    A: for<'v> TryFrom<Args<'v>, Error = RuntimeError>,
    R: IntoVes,
{
    CallableWrapper::with_name_and_magic(f, name, is_magic, arity)
}

pub fn wrap_native<A, R, F>(
    f: F,
    name: &'static str,
    is_magic: bool,
    arity: Arity,
) -> Box<dyn FnNative>
where
    F: for<'v> Callable<'v, A> + Fn(&mut dyn VmInterface, A) -> Result<R, RuntimeError> + 'static,
    A: for<'v> TryFrom<Args<'v>, Error = RuntimeError> + 'static,
    R: IntoVes,
{
    Box::new(wrap_with_magic(f, name, is_magic, arity))
}

unsafe impl<'v, C, A> Trace for CallableWrapper<C, A>
where
    C: Callable<'v, A>,
    A: TryFrom<Args<'v>, Error = RuntimeError>,
{
    fn trace(&mut self, _tracer: &mut dyn Tracer) {}
}

impl<A, C> FnNative for CallableWrapper<C, A>
where
    C: for<'v> Callable<'v, A>,
    A: for<'v> TryFrom<Args<'v>, Error = RuntimeError>,
{
    fn call<'a>(
        &mut self,
        vm: &'a mut dyn crate::vm::vm::VmInterface,
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

    fn arity(&self) -> Arity {
        self.arity
    }
}

#[cfg(test)]
mod tests {
    use ves_middle::registry::ModuleRegistry;

    use crate::{
        gc::{DefaultGc, GcHandle, SharedPtr},
        value::Result,
        vm::{symbols::SymbolTable, vm::Vm, Context, VmGlobals},
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

        let wrapper = wrap(fallible, "fallible", Arity::none());
        assert_eq!(wrapper.name(), "fallible");

        let wrapper = wrap_native(fallible, "fallible", false, Arity::none());
        assert_eq!(wrapper.name(), "fallible");
        assert!(!wrapper.is_magic());
    }
}
