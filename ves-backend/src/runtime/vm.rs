use ves_error::VesError;

use crate::{
    gc::{GcHandle, GcObj, Roots, SharedPtr, Trace, VesGc},
    objects::{ves_fn::Args, ves_str::view::VesStrView},
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
        if let Some(result) =
            $self.call_magic_arithmetics_method(&lhs_method, &rhs_method, $left, $right)?
        {
            $self.pop_n(2);
            $self.push(NanBox::new(result));
        } else {
            unimplemented!("The result may be none only when making ves calls");
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

pub trait VmInterface {
    fn alloc(&mut self, obj: VesObject) -> GcObj;
    fn call_function(&mut self, obj: GcObj) -> Result<Value, VesError>;
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

    fn call_function(&mut self, obj: GcObj) -> Result<Value, VesError> {
        todo!("calling arbitrary functions isn't supported yet: {:?}", obj);
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
        self.push_frame(CallFrame::main(r#fn)).unwrap();

        // TODO: tracebacks / backtraces
        self.run_dispatch_loop()
    }

    fn run_dispatch_loop(&mut self) -> Result<(), VesError> {
        use crate::emitter::opcode::Opcode;

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
                Opcode::GetUpvalue(_) => unimplemented!(),
                Opcode::SetUpvalue(_) => unimplemented!(),
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
                Opcode::Equal => self.equal()?,
                Opcode::NotEqual => self.not_equal()?,
                Opcode::LessThan => self.less_than()?,
                Opcode::LessEqual => self.less_equal()?,
                Opcode::GreaterThan => self.greater_than()?,
                Opcode::GreaterEqual => self.greater_equal()?,
                Opcode::IsNum => unimplemented!(),
                Opcode::IsStr => unimplemented!(),
                Opcode::IsBool => unimplemented!(),
                Opcode::IsMap => unimplemented!(),
                Opcode::IsArray => unimplemented!(),
                Opcode::IsNone => unimplemented!(),
                Opcode::IsSome => unimplemented!(),
                Opcode::CompareType => unimplemented!(),
                Opcode::HasProperty => unimplemented!(),
                Opcode::Try => unimplemented!(),
                Opcode::WrapOk => unimplemented!(),
                Opcode::WrapErr => unimplemented!(),
                Opcode::UnwrapOk(_) => unimplemented!(),
                Opcode::UnwrapErr(_) => unimplemented!(),
                Opcode::Spread => unimplemented!(),
                Opcode::Call(_) => unimplemented!(),
                Opcode::Defer => unimplemented!(),
                Opcode::Interpolate(_) => unimplemented!(),
                Opcode::CreateArray(_) => unimplemented!(),
                Opcode::CreateEmptyMap => unimplemented!(),
                Opcode::MapInsert => unimplemented!(),
                Opcode::MapExtend => unimplemented!(),
                Opcode::CreateClosure(_) => unimplemented!(),
                Opcode::CreateStruct => unimplemented!(),
                Opcode::AddMethod(_) => unimplemented!(),
                Opcode::AddMagicMethod(_) => unimplemented!(),
                Opcode::AddStaticMethod(_) => unimplemented!(),
                Opcode::AddStaticField(_) => unimplemented!(),
                Opcode::Print => self.print()?,
                Opcode::PrintN(n) => self.print_n(n)?,
                Opcode::Pop => {
                    self.pop();
                }
                Opcode::PopN(n) => {
                    self.pop_n(n as usize);
                }
                Opcode::Jump(_) => unimplemented!(),
                Opcode::JumpIfFalse(_) => unimplemented!(),
                Opcode::Return => {
                    let cs_size = self.call_stack.len();

                    if cs_size == 1 {
                        self.pop_frame();
                        break; // todo: return result
                    }

                    todo!("function calls")
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

    fn call_magic_arithmetics_method(
        &mut self,
        lhs_method: &VesStrView,
        rhs_method: &VesStrView,
        left: NanBox,
        right: NanBox,
        // NOTE: has to return an option since ves calls wouldn't be able to return a value immediately
    ) -> Result<Option<Value>, VesError> {
        let inst = self.ip;
        let mut method = self
            .get_magic_method(left, &lhs_method, inst)
            .or_else(|_| self.get_magic_method(right, &rhs_method, inst))?;

        let result = match &mut *method {
            VesObject::FnNative(func) => {
                func.call(self, Args(&mut vec![left.unbox(), right.unbox()]))?
            }
            VesObject::Fn(_) | VesObject::Closure(_) => {
                unimplemented!("Functions calls aren't implemented yet")
            }
            _ => unreachable!("get_magic_method shouldn't return non-callable objects"),
        };

        Ok(Some(result))
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
        } else if operand.is_normal_ptr() {
            if let Some(operand) = operand.unbox().as_bigint_mut() {
                operand.value = -&operand.value;
            }
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
            self.push(NanBox::from(operand.as_bool_unchecked()));
            return Ok(());
        }

        todo!()
    }

    fn equal(&mut self) -> Result<(), VesError> {
        let right = *self.peek_at(1);
        let left = *self.peek();

        // two values are equal if their bit representations are equal, which implies:
        // - their types are the same
        // - their values are the same
        // for objects, we compare identity
        self.pop_n(2);
        self.push(NanBox::bool(left == right));
        Ok(())
    }

    fn not_equal(&mut self) -> Result<(), VesError> {
        let right = *self.peek_at(1);
        let left = *self.peek();
        self.pop_n(2);
        self.push(NanBox::bool(left != right));
        Ok(())
    }

    fn less_than(&mut self) -> Result<(), VesError> {
        let right = *self.peek_at(1);
        let left = *self.peek();

        num_bin_op!(self, left, right, |l, r| Ok(l < r), |l, r| l < r);

        Ok(())
    }

    fn less_equal(&mut self) -> Result<(), VesError> {
        let right = *self.peek_at(1);
        let left = *self.peek();

        num_bin_op!(self, left, right, |l, r| Ok(l <= r), |l, r| l <= r);

        Ok(())
    }

    fn greater_than(&mut self) -> Result<(), VesError> {
        let left = *self.peek();
        let right = *self.peek_at(1);

        num_bin_op!(self, left, right, |l, r| Ok(l > r), |l, r| l > r);

        Ok(())
    }

    fn greater_equal(&mut self) -> Result<(), VesError> {
        let right = *self.peek_at(1);
        let left = *self.peek();

        num_bin_op!(self, left, right, |l, r| Ok(l >= r), |l, r| l >= r);

        Ok(())
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
        if slot >= self.stack.len() {
            self.push(obj);
        } else {
            self.stack[slot] = obj;
        }
        self.local_at(offset)
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

    fn stringify(&mut self, value: &Value) -> Result<std::borrow::Cow<'static, str>, VesError> {
        // TODO: call the magic method here
        Ok(value.to_string().into())
    }

    #[cfg(feature = "fast")]
    #[inline]
    fn local_at(&self, offset: usize) -> &NanBox {
        let frame_start = self.frame_unchecked().stack_index;
        unsafe { self.stack.get_unchecked(frame_start + offset) }
    }

    #[inline]
    fn push(&mut self, obj: impl Into<NanBox>) {
        self.stack.push(obj.into());
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
