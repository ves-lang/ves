use ves_backend::{
    gc::{GcHandle, GcObj, Roots, Trace, VesGc},
    nanbox::NanBox,
    objects::{
        ves_str::view::VesStrView,
        ves_struct::{VesHashMap, VesInstance, VesStruct, ViewKey},
    },
    Value, VesObject,
};

#[derive(Debug, Clone, Copy)]
pub enum Inst {
    Const(u8),
    Pop,
    Alloc,
    SetLocal(u8),
    GetLocal(u8),
    SetField(u8),
    GetField(u8),
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Neq,
    Jz(i16),
    Jmp(i16),
    Return,
}

#[derive(Debug, Clone)]
pub struct VmEnum<T: VesGc> {
    ip: usize,
    stack: Vec<NanBox>,
    constants: Vec<NanBox>,
    gc: GcHandle<T>,
    instructions: Vec<Inst>,
    /// The type used by the Alloc instruction
    ty: GcObj,
    err: Option<String>,
}

impl<T: VesGc> VmEnum<T> {
    pub fn new(mut gc: GcHandle<T>, constants: Vec<NanBox>, instructions: Vec<Inst>) -> Self {
        let mut fields = VesHashMap::new_in(gc.proxy());
        fields.insert(ViewKey::from(gc.alloc_permanent("n")), 0);
        fields.insert(ViewKey::from(gc.alloc_permanent("a")), 1);
        fields.insert(ViewKey::from(gc.alloc_permanent("b")), 2);
        let ty = VesStruct::new(fields, VesHashMap::new_in(gc.proxy()));
        let ty = gc.alloc_permanent(ty);

        Self {
            ip: 0,
            stack: Vec::with_capacity(256),
            gc,
            constants,
            instructions,
            ty,
            err: None,
        }
    }

    pub fn reset(&mut self) {
        self.stack.clear();
        self.ip = 0;
        self.err = None;
    }

    pub fn run(&mut self) -> Result<NanBox, String> {
        while self.ip < self.instructions.len() {
            self.ip += 1;
            let inst = self.instructions[self.ip - 1];
            // println!("ip={:03} {:#?} {:#?}", self.ip - 1, inst, self.stack);
            match inst {
                Inst::Const(c) => self.push(self.constants[c as usize]),
                Inst::Pop => {
                    self.pop();
                }
                Inst::SetLocal(s) => {
                    self.stack[s as usize] = self.pop();
                }
                Inst::GetLocal(s) => {
                    self.push(self.stack[s as usize]);
                }
                Inst::SetField(c) => self.set_field(self.constants[c as usize]),
                Inst::GetField(c) => self.get_field(self.constants[c as usize]),
                Inst::Add => self.add(),
                Inst::Sub => self.sub(),
                Inst::Mul => self.mul(),
                Inst::Div => self.div(),
                Inst::Eq => self.eq(),
                Inst::Neq => self.neq(),
                Inst::Alloc => self.alloc_instance(),
                Inst::Jz(offset) => self.jz(offset),
                Inst::Jmp(offset) => self.jmp(offset),
                Inst::Return => return Ok(self.pop()),
            }
        }

        Err(self.err.take().unwrap())
    }

    fn eq(&mut self) {
        let right = self.pop();
        let left = self.pop();
        self.push(NanBox::new(Value::Bool(
            right.raw_bits() == left.raw_bits(),
        )));
    }

    fn neq(&mut self) {
        let right = self.pop();
        let left = self.pop();
        self.push(NanBox::new(Value::Bool(
            left.raw_bits() != right.raw_bits(),
        )));
    }

    fn alloc_instance(&mut self) {
        let instance = VesInstance::new(self.ty, self.gc.proxy());

        let ptr = self.alloc(instance);

        self.push(NanBox::new(Value::from(ptr)));
    }

    fn alloc(&mut self, o: impl Into<VesObject>) -> GcObj {
        self.gc
            .alloc(
                o,
                Roots {
                    stack: &mut self.stack,
                    data: std::iter::once(&mut self.ty as &mut dyn Trace),
                },
            )
            .unwrap()
    }

    fn jz(&mut self, offset: i16) {
        let val = self.peek();
        if val.is_ptr() {
            return;
        }
        let jmp = match val.unbox() {
            Value::Num(n) => n != 0.0,
            Value::Bool(b) => b,
            Value::None => false,
            Value::Ref(_) => unreachable!(),
        };
        if !jmp {
            self.jmp(offset)
        }
    }

    fn jmp(&mut self, offset: i16) {
        self.ip = (self.ip as isize + offset as isize) as usize;
    }

    fn add(&mut self) {
        let right = self.pop();
        let left = self.pop();

        if right.is_num() && left.is_num() {
            self.push(NanBox::new(Value::Num(unsafe {
                left.into_num_unchecked() + right.into_num_unchecked()
            })));
            return;
        }

        match (left.unbox(), right.unbox()) {
            (Value::Ref(l), Value::Ref(r)) => match (&*l, &*r) {
                (VesObject::Str(l), VesObject::Str(r)) => {
                    let ptr = self.alloc(l.clone_inner().into_owned() + r);
                    self.push(NanBox::new(Value::from(ptr)));
                }
                _ => self.error(format!("Cannot add objects `{:?}` and `{:?}`", left, right)),
            },
            (left, right) => {
                self.error(format!("Cannot add objects `{:?}` and `{:?}`", left, right))
            }
        }
    }

    fn sub(&mut self) {
        let right = self.pop();
        let left = self.pop();

        if right.is_num() && left.is_num() {
            self.push(NanBox::new(Value::Num(unsafe {
                left.into_num_unchecked() - right.into_num_unchecked()
            })));
            return;
        }

        self.error(format!(
            "Cannot subtract objects `{:?}` and `{:?}`",
            left.unbox(),
            right.unbox()
        ))
    }

    fn mul(&mut self) {
        let right = self.pop();
        let left = self.pop();

        if right.is_num() && left.is_num() {
            self.push(NanBox::new(Value::Num(unsafe {
                left.into_num_unchecked() * right.into_num_unchecked()
            })));
            return;
        }

        self.error(format!(
            "Cannot multiply objects `{:?}` and `{:?}`",
            left.unbox(),
            right.unbox()
        ))
    }

    fn div(&mut self) {
        let right = self.pop();
        let left = self.pop();

        if right.is_num() && left.is_num() {
            if left.as_num_unchecked() == 0.0 {
                self.error("Attempted to divide by zero".to_string());
                return;
            }
            self.push(NanBox::new(Value::Num(unsafe {
                left.into_num_unchecked() / right.into_num_unchecked()
            })));
            return;
        }

        self.error(format!(
            "Cannot divide objects `{:?}` and `{:?}`",
            left.unbox(),
            right.unbox()
        ))
    }

    fn set_field(&mut self, n: NanBox) {
        let obj = self.pop();
        if !obj.is_ptr() {
            self.error(format!("{:?} is not an object", obj.unbox()));
            return;
        }
        let name = n.unbox().as_ptr().unwrap();
        let name = VesStrView::new(name);
        let mut obj = unsafe { obj.unbox_pointer() }.0;
        match &mut *obj {
            VesObject::Instance(obj) => {
                *obj.get_slot_value_mut(&name).unwrap() = self.pop().unbox()
            }
            _ => {
                self.error("Only struct instances support field assignment".to_string());
            }
        }
    }

    fn get_field(&mut self, n: NanBox) {
        let obj = self.pop();
        if !obj.is_ptr() {
            self.error(format!("{:?} is not an object", obj.unbox()));
            return;
        }
        let name = n.unbox().as_ptr().unwrap();
        let name = match *name {
            VesObject::Str(_) => VesStrView::new(name),
            _ => unreachable!(),
        };
        let obj = unsafe { obj.unbox_pointer() }.0;
        match &*obj {
            VesObject::Instance(instance) => match instance.get_slot_value(&name) {
                Some(r#ref) => self.push(NanBox::new(*r#ref)),
                None => self.error(format!("Object is missing the field `{}`.", name.str())),
            },
            _ => self.error("Only struct instances support field access".to_string()),
        }
    }

    fn error(&mut self, e: String) {
        self.err = Some(format!("[ip={:03}] {}", self.ip, e));
        self.ip = std::usize::MAX;
    }

    #[inline]
    fn push(&mut self, v: NanBox) {
        self.stack.push(v);
    }

    #[inline]
    #[cfg(feature = "unsafe")]
    fn pop(&mut self) -> NanBox {
        let len = self.stack.len() - 1;
        unsafe {
            self.stack.set_len(len);
            std::ptr::read(self.stack.as_ptr().add(len))
        }
    }

    #[inline]
    #[cfg(not(feature = "unsafe"))]
    fn pop(&mut self) -> NanBox {
        self.stack.pop().unwrap()
    }

    #[cfg(feature = "unsafe")]
    #[inline]
    fn peek(&self) -> &NanBox {
        let at = self.stack.len() - 1;
        unsafe { self.stack.get_unchecked(at) }
    }

    #[inline]
    #[cfg(not(feature = "unsafe"))]
    fn peek(&self) -> &NanBox {
        self.stack.last().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vm_enum_opcodes() {
        let gc = ves_backend::gc::DefaultGc::default();
        let mut handle = GcHandle::new(gc);
        let mut vm = VmEnum::new(
            handle.clone(),
            vec![
                NanBox::num(100.0),
                NanBox::num(0.0),
                NanBox::num(1.0),
                NanBox::new(ves_backend::Value::from(handle.alloc_permanent("a"))),
                NanBox::new(ves_backend::Value::from(handle.alloc_permanent("b"))),
                NanBox::new(ves_backend::Value::from(handle.alloc_permanent("n"))),
            ],
            vec![
                Inst::Alloc, // 0 = obj
                Inst::Const(0),
                Inst::GetLocal(0),
                Inst::SetField(5), // n = 100
                Inst::Const(1),
                Inst::GetLocal(0),
                Inst::SetField(3), // a = 0
                Inst::Const(2),
                Inst::GetLocal(0),
                Inst::SetField(4), // b = 1
                Inst::GetLocal(0),
                Inst::GetField(5),
                Inst::Const(1),
                Inst::Neq,
                Inst::Jz(19),
                Inst::Pop,
                Inst::GetLocal(0),
                Inst::GetField(4), // tmp = b
                Inst::GetLocal(0),
                Inst::GetField(4),
                Inst::GetLocal(0),
                Inst::GetField(3),
                Inst::Add,
                Inst::GetLocal(0),
                Inst::SetField(4), // b = a + b
                Inst::GetLocal(0),
                Inst::SetField(3), // a = tmp
                Inst::GetLocal(0),
                Inst::GetField(5), // n - 1
                Inst::Const(2),
                Inst::Sub,
                Inst::GetLocal(0),
                Inst::SetField(5),
                Inst::Jmp(-24),
                Inst::Pop,
                Inst::GetLocal(0),
                Inst::GetField(3),
                Inst::Return,
            ],
        );

        let res = vm.run().unwrap().unbox();
        assert_eq!(res, Value::Num(354224848179262000000.0));
    }
}
