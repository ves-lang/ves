use std::usize;

use ves_error::VesError;

use crate::{
    emitter::emit::CaptureInfo,
    gc::{GcHandle, GcObj, Roots, SharedPtr, Trace, VesGc},
    objects::{
        peel::Peeled,
        ves_fn::{ArgCountDiff, Args, VesClosure},
        ves_str::view::VesStrView,
    },
    NanBox, Value, VesObject,
};

use super::{call_frame::CallFrame, symbols::SymbolTable, Context, VmGlobals};

pub const DEFAULT_STACK_SIZE: usize = 256;
pub const DEFAULT_MAX_CALL_STACK_SIZE: usize = 1024;
const DEBUG_STACK_PRINT_SIZE: usize = 5;

macro_rules! num_bin_op {
    ($self:ident, $left:ident, $right:ident, $int:expr, $float:expr, lhs => $lhs_method:ident, rhs => $rhs_method:ident) => {
        num_bin_op!($self, $left, $right, $int, $float);

        // TODO: bigint
        // outside of + - *, we also have to check if the values match certain criteria:
        // [ ] 1. in case of bigint.pow, the right side must be within usize::MIN..usize::MAX
        // [x] 2. in case of bigint.div, the right side must not be zero
        // [x] bigint + bigint -> bigint
        // [x] bigint + int -> bigint
        // [x] int + bigint -> bigint
        // [ ] bigint + float -> error
        // [ ] float + bigint -> error

        // Should this be in a method?
        let lhs_method = $self.symbols.$lhs_method;
        let rhs_method = $self.symbols.$rhs_method;
        match $self.call_magic_arithmetics_method(&lhs_method, &rhs_method, $left, $right)? {
            Some(result) => {
                $self.push(NanBox::new(result));
            }
            None => {
                unimplemented!("The result may be none only when making ves calls");
            }
        }
    };
    ($self:ident, $left:ident, $right:ident, $int:expr, $float:expr) => {
        // favor ints
        if $left.is_int() {
            if $right.is_int() {
                $self.pop_n(2);
                let v = $int($left.as_int_unchecked(), $right.as_int_unchecked())?;
                $self.push(NanBox::from(v));
                return Ok(());
            } else if $right.is_float() {
                $self.pop_n(2);
                let v = $float($left.as_int_unchecked() as f64, $right.as_float_unchecked());
                $self.push(NanBox::from(v));
                return Ok(());
            }
        } else if $left.is_float() {
            if $right.is_int() {
                $self.pop_n(2);
                let v = $float($left.as_float_unchecked(), $right.as_int_unchecked() as f64);
                $self.push(NanBox::from(v));
                return Ok(());
            } else if $right.is_float() {
                $self.pop_n(2);
                let v = $float($left.as_float_unchecked(), $right.as_float_unchecked());
                $self.push(NanBox::from(v));
                return Ok(());
            }
        }
    };
}

macro_rules! cmp_op {
    ($self:ident, $result:expr, $int:expr, $float:expr, $none:expr) => {
        let top = $result;
        #[allow(clippy::redundant_closure_call)]
        if top.is_int() {
            $self.push(($int)(top.as_int_unchecked()));
        } else if top.is_float() {
            $self.push(($float)(top.as_float_unchecked()));
        } else if top.is_none() {
            $none
        } else {
            return Err($self.error(format!(
                "@cmp must return a number, but produced {}",
                top.unbox()
            )));
        }
    };
}

pub trait VmInterface {
    fn alloc(&mut self, obj: VesObject) -> GcObj;
    fn execute(&mut self, callee: Value, args: Vec<Value>) -> Result<Value, VesError>;
    fn create_error(&mut self, msg: String) -> VesError;
}

pub struct Vm<T: VesGc, W = std::io::Stdout> {
    ctx: SharedPtr<Context<T>>,
    gc: GcHandle<T>,
    symbols: SymbolTable<T>,
    globals: VmGlobals,
    stack: Vec<NanBox>,
    call_stack: Vec<CallFrame>,
    max_cs_size: usize,
    ip: usize,
    // TODO: look at the asm for this vs Option<NonNull<CallFrame/>> + unwrap_unchecked()
    frame: *mut CallFrame,
    writer: W,
}

impl<T: VesGc, W: std::io::Write> VmInterface for Vm<T, W> {
    fn alloc(&mut self, obj: VesObject) -> GcObj {
        // TODO: don't panic on allocation failure
        // TODO: intern strings
        self.gc
            .alloc(
                obj,
                Roots {
                    stack: &mut self.stack,
                    data: self
                        .call_stack
                        .iter_mut()
                        .map(|frame| frame as &mut dyn Trace),
                },
            )
            .expect("Failed to allocate the object")
    }

    // TODO: currently the caller of this is responsible for setting up the stack for the call
    // it should be handled automatically
    fn execute(&mut self, callee: Value, args: Vec<Value>) -> Result<Value, VesError> {
        self.push(callee);
        let argc = args.len();
        self.stack.extend(args.into_iter().map(NanBox::from));
        if self.call(argc)? {
            return Ok(self.pop().unbox());
        }
        // TODO: tracebacks / backtraces
        self.run_dispatch_loop(true)?;
        Ok(self.pop().unbox())
    }

    fn create_error(&mut self, msg: String) -> VesError {
        self.error(msg)
    }
}

impl<T: VesGc, W: std::io::Write> Vm<T, W> {
    pub fn new(ctx: SharedPtr<Context<T>>) -> Vm<T, std::io::Stdout> {
        Vm::with_writer(ctx, std::io::stdout())
    }

    pub fn with_writer(ctx: SharedPtr<Context<T>>, writer: W) -> Vm<T, W> {
        Self {
            gc: ctx.gc.clone(),
            globals: ctx.globals.clone(),
            symbols: ctx.symbols.clone(),
            ctx,
            stack: Vec::with_capacity(DEFAULT_STACK_SIZE),
            call_stack: Vec::with_capacity(0),
            ip: 0,
            frame: std::ptr::null_mut(),
            max_cs_size: DEFAULT_MAX_CALL_STACK_SIZE,
            writer,
        }
    }

    // TODO: encapsulate modules and run one module at a time
    pub fn run(&mut self, r#fn: GcObj) -> Result<(), VesError> {
        self.push_frame(CallFrame::main(Peeled::new(
            r#fn,
            VesObject::as_fn_mut_unwrapped,
        )))
        .unwrap();

        // TODO: tracebacks / backtraces
        self.run_dispatch_loop(false)?;
        Ok(())
    }

    fn run_dispatch_loop(&mut self, early_return: bool) -> Result<(), VesError> {
        use crate::emitter::opcode::Opcode;

        let initial_call_stack_size = self.call_stack.len();
        // TODO: cache the code pointer here for speed
        // let len = self.frame_unchecked().code_len();
        // let code = self.frame_unchecked().code().as_ptr();

        while self.ip < self.frame_unchecked().code_len() {
            #[cfg(feature = "vm-debug")]
            {
                self.debug_inst();
            }
            self.ip += 1;
            match self.frame_unchecked().inst(self.ip - 1) {
                Opcode::GetConst(idx) => self.get_const(idx),
                Opcode::GetLocal(idx) => self.get_local(idx),
                Opcode::SetLocal(idx) => self.set_local(idx),
                Opcode::PushInt32(num) => self.push(NanBox::int(num as _)),
                Opcode::PushTrue => self.push(NanBox::bool(true)),
                Opcode::PushFalse => self.push(NanBox::bool(false)),
                Opcode::PushNone => self.push(NanBox::none()),
                Opcode::GetGlobal(idx) => self.get_global(idx)?,
                Opcode::GetCapture(idx) => self.get_capture(idx),
                Opcode::SetCapture(idx) => self.set_capture(idx),
                Opcode::SetGlobal(idx) => self.set_global(idx),
                Opcode::GetMagicProp(_) => unimplemented!(),
                Opcode::GetProp(_) => unimplemented!(),
                Opcode::TryGetProp(_) => unimplemented!(),
                Opcode::SetProp(_) => unimplemented!(),
                Opcode::GetItem => unimplemented!(),
                Opcode::SetItem => unimplemented!(),
                Opcode::Add => self.add()?,
                Opcode::Subtract => self.sub()?,
                Opcode::Multiply => self.mul()?,
                Opcode::Divide => self.div()?,
                Opcode::Remainder => self.rem()?,
                Opcode::Power => self.pow()?,
                Opcode::Negate => self.neg()?,
                Opcode::AddOne => self.add1()?,
                Opcode::SubtractOne => self.sub1()?,
                Opcode::Not => self.not()?,
                Opcode::Compare => self.compare()?,
                Opcode::IsCmpEqual => self.equal()?,
                Opcode::IsCmpNotEqual => self.not_equal()?,
                Opcode::IsCmpLessThan => self.less_than()?,
                Opcode::IsCmpLessEqual => self.less_equal()?,
                Opcode::IsCmpGreaterThan => self.greater_than()?,
                Opcode::IsCmpGreaterEqual => self.greater_equal()?,
                Opcode::CompareType => self.compare_type()?,
                Opcode::HasProperty => unimplemented!(),
                Opcode::Try => unimplemented!(),
                Opcode::WrapOk => unimplemented!(),
                Opcode::WrapErr => unimplemented!(),
                Opcode::UnwrapOk(_) => unimplemented!(),
                Opcode::UnwrapErr(_) => unimplemented!(),
                Opcode::Spread => unimplemented!(),
                Opcode::Call(args) => {
                    self.call(args as usize)?;
                }
                Opcode::Defer => unimplemented!(),
                Opcode::Interpolate(n) => self.interpolate(n)?,
                Opcode::CreateArray(_) => unimplemented!(),
                Opcode::CreateEmptyMap => unimplemented!(),
                Opcode::MapInsert => unimplemented!(),
                Opcode::MapExtend => unimplemented!(),
                Opcode::CreateClosure(d) => self.create_closure(d)?,
                Opcode::CreateStruct(_) => unimplemented!(),
                Opcode::AddMethod(_) => unimplemented!(),
                Opcode::AddMagicMethod(_) => unimplemented!(),
                Opcode::AddStaticMethod(_) => unimplemented!(),
                Opcode::AddStaticField(_) => unimplemented!(),
                Opcode::Print => self.print()?,
                Opcode::PrintN(n) => self.print_n(n)?,
                Opcode::Copy => self.copy()?,
                Opcode::CopyN(n) => self.copy_n(n)?,
                Opcode::Pop => {
                    self.pop();
                }
                Opcode::PopN(n) => {
                    self.pop_n(n as usize);
                }
                Opcode::Jump(to) => self.jump(to),
                Opcode::JumpIfFalse(to) => self.jump_if_false(to),
                Opcode::Return => {
                    let frame = self.pop_frame();
                    self.ip = frame.return_address;

                    let current_call_stack_size = self.call_stack.len();
                    let should_return = (early_return
                        && current_call_stack_size == initial_call_stack_size)
                        || current_call_stack_size == 0;
                    if should_return {
                        break;
                    }
                }
                Opcode::Data(_) => {
                    unreachable!("Data instructions aren't supposed to be executed")
                }
                Opcode::Label(_) => {
                    unreachable!(
                        "Label instructions are compile-time only, this should never happen"
                    )
                }
            }
        }

        Ok(())
    }

    fn get_magic_method(
        &mut self,
        obj: NanBox,
        name: &VesStrView,
        inst: usize,
    ) -> Result<GcObj, VesError> {
        match obj.unbox() {
            Value::Ref(mut obj) => {
                let slot = self
                    .frame_unchecked_mut()
                    .cache_mut()
                    .get_property_cache(inst, &obj);

                // TODO: this should probably be behind a trait
                match &mut *obj {
                    VesObject::Str(_) if name.str() == "str" => Err({
                        self.error("str doesn't have a magic method called `@str`".to_string())
                    }),
                    VesObject::Str(_) => todo!(),
                    // NOTE: this assumes that BigInt has only methods and no fields
                    VesObject::Int(i) => {
                        if let Some(slot) = slot {
                            let method = i.props().get_by_slot_index(slot).expect("Unexpected cache misconfiguration (expected to find a method according to the IC)");
                            Ok(method.as_ptr().unwrap())
                        } else {
                            let index = i.props().get_slot_index(&name);
                            if let Some(method) = index
                                .and_then(|index| i.props().get_by_slot_index(index))
                                .and_then(|obj| obj.as_ref())
                                .and_then(|obj| {
                                    if obj
                                        .as_fn_native()
                                        .map(|func| func.is_magic())
                                        .unwrap_or(false)
                                    {
                                        Some(*obj)
                                    } else {
                                        None
                                    }
                                })
                            {
                                self.frame_unchecked_mut()
                                    .cache_mut()
                                    .update_property_cache(inst, index.unwrap(), obj);
                                Ok(method)
                            } else {
                                Err({
                                    self.error(format!(
                                        "BigInt doesn't have a magic method called `@{}`",
                                        name.str()
                                    ))
                                })
                            }
                        }
                    }
                    VesObject::Instance(_) => {
                        unimplemented!()
                    }
                    rest => Err(self.error(format!(
                        "Cannot access a magic method `@{}` on an object of type {}",
                        name.str(),
                        rest,
                    ))),
                }
            }
            rest => Err(self.error(format!(
                "Cannot access properties on an object of type {}",
                rest
            ))),
        }
    }

    /// Calls the given LHS or RHS magic method on the left or right operand.
    /// NOTE: This method expects the operands to be present on the stack.
    fn call_magic_arithmetics_method(
        &mut self,
        lhs_method: &VesStrView,
        rhs_method: &VesStrView,
        left: NanBox,
        right: NanBox,
    ) -> Result<Option<Value>, VesError> {
        let inst = self.inst();
        if let Ok(method) = self.get_magic_method(left, &lhs_method, inst) {
            self.pop_n(2);
            self.push_many([NanBox::from(method), left, right]);
        } else {
            let method = self.get_magic_method(right, &rhs_method, inst)?;
            self.pop_n(2);
            self.push_many([NanBox::from(method), right, left]);
        }

        match self.call(2) {
            Ok(true) => {
                let result = self.pop().unbox();
                Ok(Some(result))
            }
            Ok(false) => Ok(None),
            Err(e) => Err(e),
        }
    }

    fn add(&mut self) -> Result<(), VesError> {
        let right = *self.peek();
        let left = *self.peek_at(1);

        num_bin_op!(
            self,
            left,
            right,
            |l, r| Ok(i32::wrapping_add(l, r)),
            std::ops::Add::<f64>::add,
            lhs => add,
            rhs => radd
        );

        Ok(())
    }

    fn sub(&mut self) -> Result<(), VesError> {
        let right = *self.peek();
        let left = *self.peek_at(1);

        num_bin_op!(
            self,
            left,
            right,
            |l, r| Ok(i32::wrapping_sub(l, r)),
            std::ops::Sub::<f64>::sub,
            lhs => sub,
            rhs => rsub
        );

        Ok(())
    }

    fn mul(&mut self) -> Result<(), VesError> {
        let right = *self.peek();
        let left = *self.peek_at(1);

        num_bin_op!(
            self,
            left,
            right,
            |l, r| Ok(i32::wrapping_mul(l, r)),
            std::ops::Mul::<f64>::mul,
            lhs => mul,
            rhs => rmul
        );

        Ok(())
    }

    fn div(&mut self) -> Result<(), VesError> {
        let right = *self.peek();
        let left = *self.peek_at(1);

        num_bin_op!(
            self,
            left,
            right,
            |l, r| i32::checked_div(l, r).ok_or_else(|| self.error("Division by zero")),
            std::ops::Div::<f64>::div,
            lhs => div,
            rhs => rdiv
        );

        Ok(())
    }

    fn rem(&mut self) -> Result<(), VesError> {
        let right = *self.peek();
        let left = *self.peek_at(1);

        num_bin_op!(
            self,
            left,
            right,
            |l, r| i32::checked_rem(l, r).ok_or_else(|| self.error("Division by zero")),
            std::ops::Rem::<f64>::rem,
            lhs => rem,
            rhs => rrem
        );

        Ok(())
    }

    fn pow(&mut self) -> Result<(), VesError> {
        let right = *self.peek();
        let left = *self.peek_at(1);

        num_bin_op!(
            self,
            left,
            right,
            |l, r| std::convert::TryInto::<u32>::try_into(r)
                .map(|r| i32::pow(l, r))
                .map_err(|_| self.error("Negative exponent")),
            f64::powf,
            lhs => pow,
            rhs => rpow
        );

        todo!()
    }

    fn neg(&mut self) -> Result<(), VesError> {
        let operand = *self.peek();

        if operand.is_int() {
            self.pop();
            self.push(NanBox::from(-operand.as_int_unchecked()));
            return Ok(());
        } else if operand.is_float() {
            self.pop();
            self.push(NanBox::from(-operand.as_float_unchecked()));
            return Ok(());
        } else if let Some(operand) = operand.unbox().as_bigint_mut() {
            operand.value = -&operand.value;
        }

        todo!()
    }

    fn add1(&mut self) -> Result<(), VesError> {
        self.push(NanBox::int(1));
        self.add()?;
        Ok(())
    }

    fn sub1(&mut self) -> Result<(), VesError> {
        self.push(NanBox::int(1));
        self.sub()?;
        Ok(())
    }

    fn not(&mut self) -> Result<(), VesError> {
        let operand = *self.peek();

        if operand.is_bool() {
            self.pop();
            self.push(NanBox::from(!operand.as_bool_unchecked()));
            return Ok(());
        }

        todo!()
    }

    fn compare(&mut self) -> Result<(), VesError> {
        let right = *self.peek();
        let left = *self.peek_at(1);

        // If two values have the same bit representation, they guaranteed to be equal, which implies:
        // - their types are the same
        // - their values are the same
        // Also, if neither of the values is a pointer, they are guaranteed to be different if their bit representations are different.
        if left == right {
            self.pop_n(2);
            self.push(0);
            // Skip the negate instruction
            self.ip += 1;
            return Ok(());
        } else if !(left.is_ptr() || right.is_ptr()) {
            self.pop_n(2);
            let result = match (left.unbox(), right.unbox()) {
                (Value::Int(l), Value::Int(r)) => (l - r).signum().into(),
                (Value::Int(l), Value::Float(r)) => (l as f64 - r).into(),
                (Value::Float(l), Value::Int(r)) => (l - r as f64).into(),
                (Value::Float(l), Value::Float(r)) => (l - r).into(),
                _ => Value::None,
            };
            self.push(result);
            // Skip the negate instruction
            self.ip += 1;
            return Ok(());
        }

        // Objects may override @cmp
        let method_name = self.symbols.cmp;
        let inst = self.inst();
        let jump_by = if let Ok(method) = self.get_magic_method(left, &method_name, inst) {
            self.pop_n(2);
            self.push_many([method.into(), left, right]);
            1 // have to jump by 1 to land on the mapping instruction
        } else if let Ok(method) = self.get_magic_method(right, &method_name, inst) {
            self.pop_n(2);
            // We have to reverse the order of the arguments since the receiver goes first
            self.push_many([method.into(), right, left]);
            0 // no need to jump, have to land onto the negate
        } else {
            self.push(NanBox::none());
            // Skip the negate instruction
            self.ip += 1;
            return Ok(());
        };

        // Adjust the ip before calling the @cmp so its return address can be set correctly.
        self.ip += jump_by;

        if self.call(2)? {
            let result = self.pop();
            if !result.is_int() && !result.is_float() {
                return Err(self.error(format!(
                    "The @cmp method must return a number, but produced {:?} instead",
                    result.unbox()
                )));
            }
            self.push(result);
            Ok(())
        } else {
            Ok(())
        }
    }

    fn equal(&mut self) -> Result<(), VesError> {
        cmp_op!(self, self.pop(), |x| x == 0, |x| x == 0.0, self.push(false));
        Ok(())
    }

    fn not_equal(&mut self) -> Result<(), VesError> {
        cmp_op!(self, self.pop(), |x| x != 0, |x| x != 0.0, self.push(true));
        Ok(())
    }

    fn less_than(&mut self) -> Result<(), VesError> {
        cmp_op!(
            self,
            self.pop(),
            |x| x < 0,
            |x| x < 0.0,
            return Err(self.error("The operands do not support ordering."))
        );
        Ok(())
    }

    fn less_equal(&mut self) -> Result<(), VesError> {
        cmp_op!(
            self,
            self.pop(),
            |x| x <= 0,
            |x| x <= 0.0,
            return Err(self.error("The operands do not support ordering."))
        );
        Ok(())
    }

    fn greater_than(&mut self) -> Result<(), VesError> {
        cmp_op!(
            self,
            self.pop(),
            |x| x > 0,
            |x| x > 0.0,
            return Err(self.error("The operands do not support ordering."))
        );
        Ok(())
    }

    fn greater_equal(&mut self) -> Result<(), VesError> {
        cmp_op!(
            self,
            self.pop(),
            |x| x >= 0,
            |x| x >= 0.0,
            return Err(self.error("The operands do not support ordering."))
        );
        Ok(())
    }

    fn interpolate(&mut self, n: u32) -> Result<(), VesError> {
        let mut interpolated = String::with_capacity(16); // 16 characters
        for v in self.pop_n(n as usize).collect::<Vec<_>>() {
            interpolated.extend(Some(self.stringify(&v.unbox())?.into_owned()));
        }
        // TODO: intern the string
        let obj = self.alloc(interpolated.into());
        self.push(obj);
        Ok(())
    }

    fn compare_type(&mut self) -> Result<(), VesError> {
        let right = *self.peek();
        let left = *self.peek_at(1);

        self.push(NanBox::bool(
            left.unbox().typeid() == right.unbox().typeid(),
        ));

        Ok(())
    }

    /// On success, returns `Ok(true)` if the callee was a native call
    fn call(&mut self, args: usize) -> Result<bool, VesError> {
        let obj = *self.peek_at(args);
        if let Some(obj) = obj.unbox().as_ref_mut() {
            // `args` implicitly includes the receiver (reserved 0th stack slot)
            let stack_index = self.stack.len() - (args + 1);

            // TODO: bound method
            // in case of bound methods, it should set the stack slot at which the callee resides to the receiver
            match &mut **obj {
                VesObject::Fn(_) => {
                    let r#fn = Peeled::new(*obj, VesObject::as_fn_mut_unwrapped);
                    let captures = std::ptr::null_mut();
                    let arity = r#fn.get().arity;
                    match arity.diff(args) {
                        // TODO: once Array is implemented, use it here
                        ArgCountDiff::Extra(n) => todo!("push into rest array"),
                        ArgCountDiff::MissingPositional(_) => {
                            return Err(self.error(format!(
                                "{} expected at least {} args, got {}",
                                obj, arity.positional, args
                            )))
                        }
                        ArgCountDiff::MissingDefaults(n) => {
                            for _ in 0..n {
                                self.push(NanBox::none());
                            }
                        }
                        _ => (),
                    }
                    self.push_frame(CallFrame::new(r#fn, captures, stack_index, self.ip))?;
                    self.ip = 0;
                    Ok(false)
                }
                VesObject::Closure(c) => {
                    let r#fn = c.fn_ptr();
                    let captures = &mut c.captures as _;
                    let arity = r#fn.get().arity;
                    match arity.diff(args) {
                        // TODO: once Array is implemented, use it here
                        ArgCountDiff::Extra(n) => todo!("push into rest array"),
                        ArgCountDiff::MissingPositional(_) => {
                            return Err(self.error(format!(
                                "{} expected at least {} args, got {}",
                                obj, arity.positional, args
                            )))
                        }
                        ArgCountDiff::MissingDefaults(n) => {
                            for _ in 0..n {
                                self.push(NanBox::none());
                            }
                        }
                        _ => (),
                    }
                    self.push_frame(CallFrame::new(r#fn, captures, stack_index, self.ip))?;
                    self.ip = 0;
                    Ok(false)
                }
                VesObject::FnNative(f) => {
                    let arity = f.arity();
                    let mut args = match f.arity().diff(args) {
                        ArgCountDiff::Extra(_) => {
                            if !arity.rest {
                                return Err(self.error(format!(
                                    "Function {} does not accept a variable number of arguments",
                                    obj
                                )));
                            }
                            self.pop_n(args).map(|v| v.unbox()).collect()
                        }
                        ArgCountDiff::MissingPositional(_) => {
                            return Err(self.error(format!(
                                "{} expected at least {} args, got {}",
                                obj, arity.positional, args
                            )))
                        }
                        ArgCountDiff::MissingDefaults(n) => self
                            .pop_n(args)
                            .map(|v| v.unbox())
                            .chain((0..n).map(|_| Value::None))
                            .collect(),
                        _ => self.pop_n(args).map(|v| v.unbox()).collect(),
                    };
                    let result = f.call(self, Args(&mut args))?;
                    self.pop(); // pop receiver
                    self.push(result);
                    Ok(true)
                }
                VesObject::Struct(_) => todo!(),
                _ => return Err(self.error(format!("{} is not callable", obj))),
            }
        } else {
            Err(self.error(format!(
                "Only objects may be called, attempted to call {}",
                obj.unbox()
            )))
        }
    }

    fn create_closure(&mut self, descriptor_index: u32) -> Result<(), VesError> {
        let descriptor = self.const_at(descriptor_index as usize);
        if let Some(descriptor) = descriptor.unbox().as_closure_descriptor() {
            let r#fn = self.const_at(descriptor.fn_constant_index as usize);
            let mut closure = self.alloc(VesClosure::new(*r#fn.unbox().as_ref_unchecked()).into());
            // because a closure may refer to itself as a capture,
            // it must be on the stack *before* we start adding captures
            self.push(closure);
            let closure = closure.as_closure_unchecked_mut();

            for capture in descriptor.captures.iter() {
                match *capture {
                    CaptureInfo::Local(index) => {
                        closure.captures.push(self.local_at(index as usize).unbox())
                    }
                    CaptureInfo::Capture(index) => {
                        closure.captures.push(*self.capture_at(index as usize))
                    }
                }
            }
            return Ok(());
        }
        println!("{:?}", self.peek().unbox());

        // The constant index inside CreateClosure always refers to a closure descriptor.
        // If this assert is triggered, it means there is a bug in the emit impl for functions.
        unreachable!()
    }

    /// TODO: there needs to be a mechanism (such as remembered pointers) to protect native objects from blowing up the rust stack when calling their stringify impls.
    /// Consider the following code:
    /// ```ignore
    /// let a = [];
    /// let b = [5];
    /// a.push(b);
    /// b[0] = a;
    ///
    /// print a;  // This line can will cause a stack overflow, but should instead print something like `[[[...]]]`.
    /// ```
    fn stringify(&mut self, value: &Value) -> Result<std::borrow::Cow<'static, str>, VesError> {
        let result = match value {
            Value::Ref(_) => {
                let method = self.symbols.str;
                let inst = self.inst();
                match self.get_magic_method(NanBox::from(*value), &method, inst) {
                    Ok(obj) => {
                        let stringified = self.execute(Value::Ref(obj), vec![*value])?;
                        match stringified.as_ref().and_then(|r| r.as_str()) {
                            Some(s) => s.clone_inner(),
                            None => {
                                return Err(
                                    self.error(format!("The @str method must return a string, but returned an object of type {:?}", stringified))
                                );
                            }
                        }
                    }
                    Err(_) => value.to_string().into(),
                }
            }
            _ => value.to_string().into(),
        };
        Ok(result)
    }

    fn get_const(&mut self, idx: u32) {
        self.push(self.const_at(idx as _));
    }

    fn get_local(&mut self, offset: u32) {
        self.push(*self.local_at(offset as usize));
    }

    fn set_local(&mut self, offset: u32) {
        let obj = self.pop();
        let obj = *self.set_local_at(offset as usize, obj);
        self.push(obj);
    }

    fn get_global(&mut self, offset: u32) -> Result<(), VesError> {
        match self.globals.get(offset as _) {
            Some(val) => {
                self.push(NanBox::new(val));
                Ok(())
            }
            None => Err(self.error("Attempted to access a not yet defined global")),
        }
    }

    fn set_global(&mut self, offset: u32) {
        let value = self.pop();
        self.globals.set(offset as _, value.unbox());
        self.push(value);
    }

    fn get_capture(&mut self, index: u32) {
        let value = *self.capture_at(index as usize);
        self.push(value);
    }

    fn set_capture(&mut self, index: u32) {
        let operand = *self.peek();
        self.set_capture_at(index as usize, operand.unbox());
    }

    #[cfg(not(feature = "fast"))]
    fn local_at(&self, offset: usize) -> &NanBox {
        let frame = self.frame_unchecked();
        let frame_start = frame.stack_index;
        match self.stack.get(frame_start + offset) {
            Some(v) => v,
            None => panic!(
                "INVALID LOCAL ADDRESS `{}` AT {} in `{}` (stack window = {}, stack = {:?})",
                offset,
                self.ip,
                frame.func().name(),
                frame_start,
                self.stack
            ),
        }
    }

    fn set_local_at(&mut self, offset: usize, obj: NanBox) -> &NanBox {
        let frame = self.frame_unchecked();
        let frame_start = frame.stack_index;
        let slot = frame_start + offset;
        #[cfg(not(feature = "fast"))]
        if slot >= self.stack.len() {
            panic!(
                "INVALID LOCAL ADDRESS `{}` AT {} in `{}` (stack window = {}, stack = {:?})",
                offset,
                self.ip,
                frame.func().name(),
                frame_start,
                self.stack
            );
        }
        self.stack[slot] = obj;
        self.local_at(offset)
    }

    fn capture_at(&self, offset: usize) -> &Value {
        let frame = self.frame_unchecked();
        let captures = frame.captures();
        #[cfg(not(feature = "fast"))]
        if offset >= captures.len() {
            panic!(
                "INVALID CAPTURE ADDRESS `{}` AT {} in `{}`",
                offset,
                self.ip,
                frame.func().name()
            );
        }
        &captures[offset]
    }

    fn set_capture_at(&mut self, offset: usize, value: Value) -> &Value {
        let frame = self.frame_unchecked();
        let captures = frame.captures();
        #[cfg(not(feature = "fast"))]
        if offset >= captures.len() {
            panic!(
                "INVALID CAPTURE ADDRESS `{}` AT {} in `{}`",
                offset,
                self.ip,
                frame.func().name()
            );
        }
        self.frame_unchecked_mut().captures_mut()[offset] = value;
        self.capture_at(offset)
    }

    fn print(&mut self) -> Result<(), VesError> {
        let v = self.pop();
        let output = self.stringify(&v.unbox())?;
        writeln!(self.writer, "{}", output).expect("Failed to write to STDOUT");
        Ok(())
    }

    fn print_n(&mut self, n: u32) -> Result<(), VesError> {
        let items = self.pop_n(n as usize).collect::<Vec<_>>();
        let mut output = Vec::with_capacity(items.len());
        for item in items {
            output.push(self.stringify(&item.unbox())?);
        }
        writeln!(self.writer, "{}", output.join(", ")).expect("Failed to write to STDOUT");
        Ok(())
    }

    fn copy(&mut self) -> Result<(), VesError> {
        self.push(*self.peek());
        Ok(())
    }

    fn copy_n(&mut self, mut n: u32) -> Result<(), VesError> {
        while n > 0 {
            self.push(*self.peek_at(n as usize));
            n -= 1;
        }
        Ok(())
    }

    #[inline]
    fn inst(&self) -> usize {
        self.ip - 1
    }

    #[cfg(feature = "fast")]
    #[inline]
    fn local_at(&self, offset: usize) -> &NanBox {
        let frame_start = self.frame_unchecked().stack_index;
        unsafe { self.stack.get_unchecked(frame_start + offset) }
    }

    #[inline]
    fn jump_if_false(&mut self, to: u32) {
        let operand = *self.peek();

        if !operand.unbox().is_truthy() {
            self.ip = to as usize;
        }
    }

    #[inline]
    fn jump(&mut self, to: u32) {
        self.ip = to as usize;
    }

    #[inline]
    fn push(&mut self, obj: impl Into<NanBox>) {
        self.stack.push(obj.into());
    }

    #[inline]
    fn push_many<const N: usize>(&mut self, objects: [NanBox; N]) {
        self.stack.extend_from_slice(&objects)
    }

    #[cfg(not(feature = "fast"))]
    #[inline]
    fn pop(&mut self) -> NanBox {
        match self.stack.pop() {
            Some(v) => v,
            None => panic!(
                "STACK UNDERFLOW AT ip={} in {}",
                self.ip,
                self.frame().func().name()
            ),
        }
    }

    #[cfg(feature = "fast")]
    #[inline]
    pub fn pop(&mut self) -> NanBox {
        let len = self.stack.len() - 1;
        unsafe {
            self.stack.set_len(len);
            std::ptr::read(self.stack.as_ptr().add(len))
        }
    }

    #[inline]
    fn pop_n(&mut self, n: usize) -> std::vec::Drain<'_, NanBox> {
        let len = self.stack.len();
        if n > len {
            panic!("STACK UNDERFLOW AT ip={}", self.ip)
        } else {
            self.stack.drain(len - n..len)
        }
    }

    #[cfg(not(feature = "fast"))]
    #[inline]
    pub fn peek(&self) -> &NanBox {
        match self.stack.last() {
            Some(v) => v,
            None => panic!(
                "STACK UNDERFLOW AT ip={} in {}",
                self.ip,
                self.frame().func().name()
            ),
        }
    }

    #[cfg(feature = "fast")]
    #[inline]
    pub fn peek(&self) -> &NanBox {
        let at = self.stack.len() - 1;
        unsafe { self.stack.get_unchecked(at) }
    }

    #[cfg(not(feature = "fast"))]
    #[inline]
    pub fn peek_at(&self, at: usize) -> &NanBox {
        let at = self.stack.len() - at - 1;
        match self.stack.get(at) {
            Some(v) => v,
            None => panic!(
                "STACK UNDERFLOW AT ip={} in {}",
                self.ip,
                self.frame().func().name()
            ),
        }
    }

    #[cfg(feature = "fast")]
    #[inline]
    pub fn peek_at(&self, at: usize) -> &NanBox {
        let at = self.stack.len() - at - 1;
        unsafe { self.stack.get_unchecked(at) }
    }

    #[inline(always)]
    fn frame_unchecked(&self) -> &CallFrame {
        unsafe { &*self.frame }
    }

    #[inline(always)]
    fn frame_unchecked_mut(&mut self) -> &mut CallFrame {
        unsafe { &mut *self.frame }
    }

    #[inline]
    fn frame(&self) -> &CallFrame {
        self.call_stack.last().unwrap()
    }

    #[cfg(not(feature = "fast"))]
    #[inline]
    fn const_at(&self, idx: usize) -> NanBox {
        match self.frame().constants().get(idx) {
            Some(v) => NanBox::new(*v),
            None => panic!("MISSING CONSTANT AT {}", idx),
        }
    }

    #[cfg(feature = "fast")]
    #[inline]
    fn const_at(&self, idx: usize) -> &Value {
        unsafe { self.frame_unchecked().constants().get_unchecked(idx) }
    }

    fn push_frame(&mut self, frame: CallFrame) -> Result<(), VesError> {
        if self.call_stack.len() >= self.max_cs_size {
            Err(self.error(format!(
                "Maximum recursion depth has been exceeded: {}.",
                self.call_stack.len()
            )))
        } else {
            self.call_stack.push(frame);
            let index = self.call_stack.len() - 1;
            self.frame = unsafe { self.call_stack.get_unchecked_mut(index) as *mut _ };
            Ok(())
        }
    }

    #[cfg(not(feature = "fast"))]
    #[inline]
    fn pop_frame(&mut self) -> CallFrame {
        let frame = self.call_stack.pop().expect("CALL STACK UNDERFLOW");
        if std::intrinsics::likely(!self.call_stack.is_empty()) {
            let index = self.call_stack.len() - 1;
            self.frame = unsafe { self.call_stack.get_unchecked_mut(index) as *mut _ };
        } else {
            self.frame = std::ptr::null_mut();
        }
        frame
    }

    #[cfg(feature = "fast")]
    #[inline]
    fn pop_frame(&mut self) -> CallFrame {
        let len = self.call_stack.len() - 1;
        let frame = unsafe {
            self.call_stack.set_len(len);
            self.frame = self.call_stack.get_unchecked_mut(len.saturating_sub(1)) as *mut _;
            std::ptr::read(self.call_stack.as_ptr().add(len))
        };
        frame
    }

    fn error(&mut self, msg: impl Into<String>) -> VesError {
        let id = self.frame().file_id();
        let span = self.frame().span(self.ip);
        VesError::runtime(msg, span, id).with_function(self.frame().func().name().to_string())
    }

    #[allow(unused)]
    fn debug_inst(&self) {
        let op = self.frame().inst(self.ip);
        println!(
            "[ip={:<03} in {:<08}] {:<016} [{}{}]",
            self.ip,
            self.frame().func().name(),
            format!("{:?}", op),
            if self.stack.len() >= DEBUG_STACK_PRINT_SIZE {
                format!("... x {}, ", self.stack.len())
            } else {
                String::new()
            },
            self.stack
                .iter()
                .rev()
                .take(DEBUG_STACK_PRINT_SIZE)
                .rev()
                .map(|v| format!("{:?}", v.unbox()))
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
}
