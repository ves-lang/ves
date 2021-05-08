use ves_backend::{
    gc::{GcHandle, GcObj, Roots, Trace, VesGc},
    nanbox::NanBox,
    objects::{
        ves_str::view::VesStrView,
        ves_struct::{VesHashMap, VesInstance, VesStruct, ViewKey},
    },
    ves_object::VesObject,
    Value,
};

#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum Inst {
    Const = 0x0, // u16
    Pop = 0x01,
    Alloc = 0x02,
    SetLocal = 0x03, // u8
    GetLocal = 0x04, // u8
    SetField = 0x05, // u8
    GetField = 0x06, // u8
    Add = 0x07,
    Sub = 0x08,
    Mul = 0x09,
    Div = 0x0A,
    Eq = 0x0B,
    Neq = 0x0C,
    Jz = 0x0D,  // i16
    Jmp = 0x0E, // i16
    Return = 0x0F,
}

#[derive(Debug, Clone)]
pub struct VmBytes<T: VesGc> {
    ip: usize,
    stack: Vec<NanBox>,
    constants: Vec<NanBox>,
    gc: GcHandle<T>,
    instructions: Vec<u8>,
    /// The type used by the Alloc instruction
    ty: GcObj,
    err: Option<String>,
}

impl<T: VesGc> VmBytes<T> {
    pub fn new(mut gc: GcHandle<T>, constants: Vec<NanBox>, instructions: Vec<u8>) -> Self {
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

            // #[cfg(debug_assertions)]
            // {
            //     let symbol = unsafe { std::mem::transmute::<u8, Inst>(inst) };
            //     debug_assert!(inst <= Inst::Return as u8);
            //     println!("ip={:03} {:#?} {:#?}", self.ip - 1, symbol, self.stack);
            // }

            match inst {
                0x00 /* Inst::Const(u8) */ => {
                    let c = self.read_u8();
                    self.push(self.constants[c as usize]);
                }
                0x01 /* Inst::Pop*/ => {
                    self.pop();
                }
                0x02 /* Inst::Alloc */ => self.alloc_instance(),
                0x03 /* Inst::SetLocal(u8) */ => {
                    let s = self.read_u8();
                    self.stack[s as usize] = self.pop();
                }
                0x04 /*Inst::GetLocal(u8)*/ => {
                    let s = self.read_u8();
                    self.push(self.stack[s as usize]);
                }
                0x05 /* Inst::SetField(u8) */ => self.set_field(),
                0x06 /* Inst::GetField(u8) */ => self.get_field(),
                0x07 /* Inst::Add */ => self.add(),
                0x08 /* Inst::Sub */ => self.sub(),
                0x09 /* Inst::Mul */ => self.mul(),
                0x0A /* Inst::Div */ => self.div(),
                0x0B /* Inst::Eq */ => self.eq(),
                0x0C /* Inst::Neq */ => self.neq(),
                0x0D /* Inst::Jz(i16) */ => self.jz(),
                0x0E /* Inst::Jmp(i16) */ => self.jmp(),
                0x0F /* Inst::Return */ => return Ok(self.pop()),
                _ /* ??? */ => unreachable!()
            }
        }

        Err(self.err.take().unwrap())
    }

    #[inline]
    #[cfg(feature = "unsafe")]
    fn read_u8(&mut self) -> u8 {
        self.ip += 1;
        unsafe { *self.instructions.get_unchecked(self.ip - 1) }
    }

    #[inline]
    #[cfg(not(feature = "unsafe"))]
    fn read_u8(&mut self) -> u8 {
        self.ip += 1;
        self.instructions[self.ip - 1]
    }

    #[inline]
    #[cfg(feature = "unsafe")]
    fn read_i16(&mut self) -> i16 {
        self.ip += 2;
        let hi =
            unsafe { std::mem::transmute::<u8, i8>(*self.instructions.get_unchecked(self.ip - 2)) };
        let lo =
            unsafe { std::mem::transmute::<u8, i8>(*self.instructions.get_unchecked(self.ip - 1)) };
        ((hi as i16) << 8) | lo as i16
    }

    #[inline]
    #[cfg(not(feature = "unsafe"))]
    fn read_i16(&mut self) -> i16 {
        self.ip += 2;
        let hi = unsafe { std::mem::transmute::<u8, i8>(self.instructions[self.ip - 2]) };
        let lo = unsafe { std::mem::transmute::<u8, i8>(self.instructions[self.ip - 1]) };
        ((hi as i16) << 8) | lo as i16
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

    fn jz(&mut self) {
        let val = self.peek();
        if val.is_ptr() {
            self.read_i16();
            return;
        }
        let condition = match val.unbox() {
            Value::Num(n) => n != 0.0,
            Value::Bool(b) => b,
            Value::None => false,
            Value::Ref(_) => unreachable!(),
        };
        if !condition {
            self.jmp();
        } else {
            self.read_i16();
        }
    }

    fn jmp(&mut self) {
        let ip = self.ip;
        let offset = self.read_i16();
        self.ip = (ip as isize + offset as isize) as usize;
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

    fn set_field(&mut self) {
        let obj = self.pop();
        if !obj.is_ptr() {
            self.error(format!("{:?} is not an object", obj.unbox()));
            return;
        }
        let id = self.read_u8() as usize;
        let name = self.constants[id].unbox().as_ptr().unwrap();
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

    fn get_field(&mut self) {
        let obj = self.pop();
        if !obj.is_ptr() {
            self.error(format!("{:?} is not an object", obj.unbox()));
            return;
        }
        let id = self.read_u8() as usize;
        let name = self.constants[id].unbox().as_ptr().unwrap();
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
    fn test_vm_byte_opcodes_simple_jump() {
        let gc = ves_backend::gc::DefaultGc::default();
        let handle = GcHandle::new(gc);
        let mut vm = VmBytes::new(
            handle,
            vec![NanBox::num(std::f64::consts::PI)],
            vec![
                Inst::Jmp as u8,
                0,
                2,
                Inst::Const as u8,
                0,
                Inst::Return as u8,
            ],
        );
        let res = vm.run().unwrap();
        assert_eq!(res.raw_bits(), std::f64::consts::PI.to_bits());
    }

    #[test]
    fn test_vm_byte_opcodes_fib() {
        let gc = ves_backend::gc::DefaultGc::default();
        let mut handle = GcHandle::new(gc);
        let mut vm = VmBytes::new(
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
                Inst::Alloc as _,
                Inst::Const as _,
                0, // load 100.0
                Inst::GetLocal as _,
                0, // load obj
                Inst::SetField as _,
                5, // set obj.n = 100
                Inst::Const as _,
                1, // load 0.0
                Inst::GetLocal as _,
                0, // load obj
                Inst::SetField as _,
                3, // set obj.a = 0
                Inst::Const as _,
                2, // load 1.0
                Inst::GetLocal as _,
                0, // load obj
                Inst::SetField as _,
                4, // set obj.b = 1
                Inst::GetLocal as _,
                0, // load obj
                Inst::GetField as _,
                5, // get obj.n
                Inst::Const as _,
                1,              // load 0
                Inst::Neq as _, // obj.n != 0
                Inst::Jz as _,  // jz (obj.n == 0)
                (39i16 << 8) as u8,
                39 & 0xFF,
                Inst::Pop as _,
                Inst::GetLocal as _,
                0, // load obj
                Inst::GetField as _,
                4, // tmp = obj.b
                Inst::GetLocal as _,
                0, // load obj
                Inst::GetField as _,
                4, // get obj.b
                Inst::GetLocal as _,
                0, // load obj
                Inst::GetField as _,
                3,              // get obj.a
                Inst::Add as _, // a + b
                Inst::GetLocal as _,
                0, // load obj
                Inst::SetField as _,
                4, // set obj.b = a + b
                Inst::GetLocal as _,
                0, // load obj
                Inst::SetField as _,
                3, // set obj.a = tmp
                Inst::GetLocal as _,
                0, // load obj
                Inst::GetField as _,
                5, // get obj.n
                Inst::Const as _,
                2,              // load 1.0
                Inst::Sub as _, // n - 1
                Inst::GetLocal as _,
                0, // load obj
                Inst::SetField as _,
                5, // set obj.n = obj.n - 1
                Inst::Jmp as _,
                unsafe { std::mem::transmute((-44i16 << 8) as i8) },
                unsafe { std::mem::transmute((-44i16 & 0xFF) as i8) },
                Inst::Pop as _,
                Inst::GetLocal as _,
                0, // load obj
                Inst::GetField as _,
                3, // get obj.a
                Inst::Return as _,
            ],
        );
        let res = vm.run().unwrap().unbox();
        assert_eq!(res, Value::Num(354224848179262000000.0));
    }
}
