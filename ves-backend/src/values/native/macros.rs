pub(super) trait __IsZero {
    fn __is_zero(self) -> bool;
}

impl<'a> __IsZero for &'a ibig::IBig {
    fn __is_zero(self) -> bool {
        self == &ibig::IBig::from(0u8)
    }
}

impl __IsZero for i32 {
    fn __is_zero(self) -> bool {
        self == 0
    }
}

macro_rules! __zero_division_check {
    (/ $right:expr) => {
        if $crate::values::native::macros::__IsZero::__is_zero($right) {
            return Err(RuntimeError::new("Division by zero"));
        }
    };
    (% $right:expr) => {};
    ($op:tt $right:expr) => {};
}

#[macro_export]
macro_rules! int_arithm_method {
    ($handle:ident, $lookup:ident, $proxy:ident, $name:tt, POW ?) => {{
        let lookup = $lookup.clone();
        let proxy = $proxy.clone();
        $handle.alloc_permanent(wrap_native(
            move |vm: &mut dyn VmInterface, (left, right): (GcObj, Value)| {
                let this = unsafe { left.as_int_unchecked() };

                let result = match right {
                    Value::Int(i) => {
                        if i < 0 {
                            return Err(RuntimeError::new(format!(
                                "The exponent must be a non-negative integer, but got `{}`",
                                i
                            )));
                        }
                        // TODO: resolve: this won't work on 32-bit platforms -- should we issue an error?
                        this.value.pow(i as usize)
                     },
                    Value::Ref(obj) if obj.as_int().is_some() => {
                        let right = unsafe { &obj.as_int_unchecked().value };
                        let right = if right <= &IBig::from(usize::MAX) && right > &IBig::from(0) {
                            // TODO: audit this
                            right.to_f64() as usize
                        } else {
                            return Err(RuntimeError::new(format!(
                                "The exponent is invalid or too big: `{}`",
                                right
                            )));
                        };
                        this.value.pow(right)
                    }
                    rest => {
                        return Err(RuntimeError::new(format!(
                            "Cannot raise a big integer to the power `{}`",
                            rest
                        )))
                    }
                };

                Ok(Value::Ref(vm.alloc(BigInt::new(result, lookup.clone(), proxy.clone()).into())))
            },
            $name,
            true,
            $crate::values::functions::Arity::new(1, 0, false)
        ))
    }};
    ($handle:ident, $lookup:ident, $proxy:ident, $name:tt, RPOW ?) => {{
        let lookup = $lookup.clone();
        let proxy = $proxy.clone();
        $handle.alloc_permanent(wrap_native(
            move |vm: &mut dyn VmInterface, (right, left): (GcObj, Value)| {
                let right = &unsafe { right.as_int_unchecked() }.value;
                let right = if right <= &IBig::from(usize::MAX) && right > &IBig::from(0) {
                    // TODO: audit this
                    right.to_f64() as usize
                } else {
                    return Err(RuntimeError::new(format!(
                        "The exponent is invalid or too big: `{}`",
                        right
                    )));
                };

                let result = match left {
                    Value::Int(i) => IBig::from(i).pow(right),
                    Value::Ref(obj) if obj.as_int().is_some() => {
                        unsafe { obj.as_int_unchecked().value.pow(right) }
                    }
                    rest => {
                        return Err(RuntimeError::new(format!(
                            "Cannot raise a big integer to the power `{}`",
                            rest
                        )))
                    }
                };

                Ok(Value::Ref(vm.alloc(BigInt::new(result, lookup.clone(), proxy.clone()).into())))
            },
            $name,
            true,
            $crate::values::functions::Arity::new(1, 0, false)
        ))
    }};
    ($handle:ident, $lookup:ident, $proxy:ident, $name:tt, CMP ?) => {{
        $handle.alloc_permanent(wrap_native(
            move |_vm: &mut dyn VmInterface, (this, other): (GcObj, Value)| {
                let this = unsafe { this.as_int_unchecked() };

                let result = match other {
                    Value::Int(i) => {
                        this.value.cmp(&IBig::from(i))
                     },
                    Value::Ref(obj) if obj.as_int().is_some() => {
                        this.value.cmp(unsafe { &obj.as_int_unchecked().value })
                    }
                    _ => {
                        return Ok(Value::None);
                    }
                };

                Ok(Value::Int(match result {
                    std::cmp::Ordering::Less => -1,
                    std::cmp::Ordering::Equal => 0,
                    std::cmp::Ordering::Greater => 1,
                }))
            },
            $name,
            true,
            $crate::values::functions::Arity::new(1, 0, false)
        ))
    }};
    ($handle:ident, $lookup:ident, $proxy:ident, $name:tt, LHS $op:tt) => {{
        let lookup = $lookup.clone();
        let proxy = $proxy.clone();
        $handle.alloc_permanent(wrap_native(
            move |vm: &mut dyn VmInterface, (left, right): (GcObj, Value)| {
                let left = unsafe { left.as_int_unchecked() };

                let result = match right {
                    Value::Int(i) => {
                        $crate::values::native::macros::__zero_division_check!($op i);
                        left.value.clone() $op IBig::from(i)
                     },
                    Value::Ref(obj) if obj.as_int().is_some() => {
                        unsafe {
                            $crate::values::native::macros::__zero_division_check!($op &obj.as_int_unchecked().value);
                            left.value.clone() $op &obj.as_int_unchecked().value
                        }
                    }
                    rest => {
                        return Err(RuntimeError::new(format!(
                            "Cannot {} a big integer and `{}`",
                            $name, rest
                        )))
                    }
                };

                Ok(vm.alloc(BigInt::new(result, lookup.clone(), proxy.clone()).into()))
            },
            $name,
            true,
            $crate::values::functions::Arity::new(1, 0, false)
        ))
    }};
    ($handle:ident, $lookup:ident, $proxy:ident, $name:tt, RHS $op:tt) => {{
        let lookup = $lookup.clone();
        let proxy = $proxy.clone();
        $handle.alloc_permanent(wrap_native(
            move |vm: &mut dyn VmInterface, (right, left): (GcObj, Value)| {
                let right = unsafe { right.as_int_unchecked() };
                $crate::values::native::macros::__zero_division_check!($op &right.value);

                let result = match left {
                    Value::Int(i) => IBig::from(i) $op right.value.clone(),
                    Value::Ref(obj) if obj.as_int().is_some() => {
                        unsafe { obj.as_int_unchecked().value.clone() $op &right.value }
                    }
                    rest => {
                        return Err(RuntimeError::new(format!(
                            "Cannot {} a big integer and `{}`",
                            $name, rest
                        )))
                    }
                };

                Ok(vm.alloc(BigInt::new(result, lookup.clone(), proxy.clone()).into()))
            },
            $name,
            true,
            $crate::values::functions::Arity::new(1, 0, false)
        ))
    }};
}

#[macro_export]
macro_rules! define_int_methods {
    ($handle:ident, $lookup:ident, $proxy:ident, $($name:literal => $side:ident $op:tt),*) => {{
        #[allow(unused_mut)]
        let mut methods = VesHashMap::new_in($handle.proxy());
        #[allow(unused)]

        let mut n = 0;

        $( $crate::values::native::macros::define_int_methods!(__internal n, methods, $handle, $lookup, $proxy, $name, $side $op); )*

        methods
    }};
    (__internal $n:ident, $methods:ident, $handle:ident, $lookup:ident, $proxy:ident, $name:tt, $side:ident $op:tt) => {{
        debug_assert!($methods.insert(
            ViewKey::from($handle.alloc_permanent($name)),
            (
                $n,
                $crate::values::native::macros::int_arithm_method!($handle, $lookup, $proxy, $name, $side $op),
            ),
        ).is_none(), "Attempted to redefine the method with the name {}", $name);

        #[allow(unused_assignments)]
        { $n += 1; }
    }};
}

pub(super) use __zero_division_check;
pub(super) use define_int_methods;
pub(super) use int_arithm_method;
