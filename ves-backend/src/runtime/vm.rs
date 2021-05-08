use ves_error::VesError;

use crate::{
    gc::{GcHandle, GcObj, VesGc},
    NanBox, Value,
};

use super::{call_frame::CallFrame, VmGlobals};

pub const DEFAULT_STACK_SIZE: usize = 256;
pub const DEFAULT_MAX_CALL_STACK_SIZE: usize = 1024;

pub struct Vm<T: VesGc, W> {
    gc: GcHandle<T>,
    globals: VmGlobals,
    stack: Vec<NanBox>,
    call_stack: Vec<CallFrame>,
    max_cs_size: usize,
    ip: usize,
    // TODO: look at the asm for this vs Option<NonNull<CallFrame/>> + unwrap_unchecked()
    frame: *mut CallFrame,
    writer: W,
}

impl<T: VesGc, W: std::io::Write> Vm<T, W> {
    pub fn new(gc: GcHandle<T>, globals: VmGlobals) -> Vm<T, std::io::Stdout> {
        Vm::with_writer(gc, globals, std::io::stdout())
    }

    pub fn with_writer(gc: GcHandle<T>, globals: VmGlobals, writer: W) -> Vm<T, W> {
        Self {
            gc,
            globals,
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
            self.ip += 1;
            match self.frame_unchecked().inst(self.ip - 1) {
                Opcode::GetConst(idx) => self.get_const(idx),
                Opcode::GetLocal(idx) => self.get_local(idx),
                Opcode::SetLocal(idx) => self.set_local(idx),
                Opcode::PushNum32(num) => self.push(NanBox::num(num as _)),
                Opcode::PushTrue => self.push(NanBox::r#true()),
                Opcode::PushFalse => self.push(NanBox::r#false()),
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
                Opcode::Add => unimplemented!(),
                Opcode::AddOne => unimplemented!(),
                Opcode::Subtract => unimplemented!(),
                Opcode::SubtractOne => unimplemented!(),
                Opcode::Multiply => unimplemented!(),
                Opcode::Divide => unimplemented!(),
                Opcode::Remainder => unimplemented!(),
                Opcode::Power => unimplemented!(),
                Opcode::Negate => unimplemented!(),
                Opcode::And => unimplemented!(),
                Opcode::Or => unimplemented!(),
                Opcode::Not => unimplemented!(),
                Opcode::Equal => unimplemented!(),
                Opcode::NotEqual => unimplemented!(),
                Opcode::LessThan => unimplemented!(),
                Opcode::LessEqual => unimplemented!(),
                Opcode::GreaterThan => unimplemented!(),
                Opcode::GreaterEqual => unimplemented!(),
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
                Opcode::Pop => unimplemented!(),
                Opcode::PopN(_) => unimplemented!(),
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
        match self.globals.get(offset as _).copied() {
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

    #[inline(always)]
    fn frame_unchecked(&self) -> &CallFrame {
        unsafe { &*self.frame }
    }

    #[inline]
    fn frame(&self) -> &CallFrame {
        self.call_stack.last().unwrap()
    }

    #[cfg(not(feature = "fast"))]
    #[inline]
    fn const_at(&self, idx: usize) -> NanBox {
        match self.frame_unchecked().constants().get(idx) {
            Some(v) => NanBox::new(*v),
            None => panic!("MISSING CONSTANT AT {}", idx),
        }
    }

    #[cfg(feature = "fast")]
    #[inline]
    fn const_at(&self, idx: usize) -> &Value {
        unsafe { self.frame_unchecked().chunk().constants.get_unchecked(idx) }
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
}
