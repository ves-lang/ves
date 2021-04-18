use ves_cc::CcContext;
use ves_runtime::{nanbox::NanBox, value::HeapObject, Value};

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
pub struct VmBytes {
    ip: usize,
    stack: Vec<NanBox>,
    constants: Vec<NanBox>,
    heap: CcContext,
    instructions: Vec<u8>,
    err: Option<String>,
}

impl VmBytes {
    pub fn new(heap: CcContext, constants: Vec<NanBox>, instructions: Vec<u8>) -> Self {
        Self {
            ip: 0,
            stack: Vec::with_capacity(256),
            heap,
            constants,
            instructions,
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
            //     println!("ip={:03} {:#?} {:#?}", self.ip, symbol, self.stack);
            // }

            match inst {
                0x00 /* Inst::Const(u8) */ => {
                    let c = self.read_u8();
                    self.push(self.constants[c as usize].clone());
                }
                0x01 /* Inst::Pop*/ => {
                    self.pop();
                }
                0x02 /* Inst::Alloc */ => self.alloc(),
                0x03 /* Inst::SetLocal(u8) */ => {
                    let s = self.read_u8();
                    self.stack[s as usize] = self.pop();
                }
                0x04 /*Inst::GetLocal(u8)*/ => {
                    let s = self.read_u8();
                    self.push(self.stack[s as usize].clone());
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

    fn alloc(&mut self) {
        self.push(NanBox::new(Value::from(self.heap.cc(HeapObject::Obj(
            std::collections::HashMap::with_capacity(3),
        )))));
    }

    fn jz(&mut self) {
        let val = self.peek();
        if val.is_ptr() {
            self.read_i16();
            return;
        }
        let condition = match val.clone().unbox() {
            Value::Num(n) => n != 0.0,
            Value::Bool(b) => b,
            Value::None => false,
            Value::Ptr(_) => unreachable!(),
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
            (Value::Ptr(l), Value::Ptr(r)) => l.with(|left| {
                r.with(|right| match (&**left, &**right) {
                    (HeapObject::Str(l), HeapObject::Str(r)) => self.push(NanBox::new(
                        Value::from(self.heap.cc(HeapObject::Str(l.to_owned() + &r[..]))),
                    )),
                    _ => self.error(format!("Cannot add objects `{:?}` and `{:?}`", left, right)),
                })
            }),
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
            "Cannot add objects `{:?}` and `{:?}`",
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
            "Cannot add objects `{:?}` and `{:?}`",
            left.unbox(),
            right.unbox()
        ))
    }

    fn div(&mut self) {
        let right = self.pop();
        let left = self.pop();

        if right.is_num() && left.is_num() {
            if unsafe { left.as_num_unchecked() == 0.0 } {
                self.error("Attempted to divide by zero".to_string());
                return;
            }
            self.push(NanBox::new(Value::Num(unsafe {
                left.into_num_unchecked() / right.into_num_unchecked()
            })));
            return;
        }

        self.error(format!(
            "Cannot add objects `{:?}` and `{:?}`",
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
        let name = self.constants[id].clone().unbox().as_ptr().unwrap();
        let name = match *name {
            HeapObject::Str(ref s) => std::borrow::Cow::Owned(s.clone()),
            HeapObject::Obj(_) => unreachable!(),
        };
        let mut obj = unsafe { obj.unbox_pointer() }.0.get();
        match unsafe { obj.deref_mut() } {
            HeapObject::Obj(obj) => {
                obj.insert(name, self.pop().unbox());
            }
            HeapObject::Str(_) => {
                self.error("Strings do not support field assignment".to_string());
                return;
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
        let name = self.constants[id].clone().unbox().as_ptr().unwrap();
        let name = match *name {
            HeapObject::Str(ref s) => std::borrow::Cow::Borrowed(&s[..]),
            HeapObject::Obj(_) => unreachable!(),
        };
        let obj = unsafe { obj.unbox_pointer() }.0.get();
        match &*obj {
            HeapObject::Obj(obj) => match obj.get(&*name) {
                Some(r#ref) => self.push(NanBox::new(r#ref.clone())),
                None => self.error(format!("Object is missing the field `{}`.", name)),
            },
            HeapObject::Str(_) => {
                self.error("Strings do not support field access".to_string());
                return;
            }
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
        let mut vm = VmBytes::new(
            CcContext::new(),
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
    fn test_vm_bytes_opcodes() {
        let ctx = CcContext::new();
        let mut vm = VmBytes::new(
            ctx.clone(),
            vec![
                NanBox::none(),
                NanBox::num(0.0),
                NanBox::num(1.0),
                NanBox::num(100.0),
                NanBox::new(ves_runtime::Value::from(
                    ctx.cc(ves_runtime::value::HeapObject::Str("fib".to_string())),
                )),
            ],
            vec![
                Inst::Const as _,
                0, // 0 = obj
                Inst::Const as _,
                1, // 1 = a
                Inst::Const as _,
                2, // 2 = b
                Inst::Const as _,
                3, // 3 = n
                Inst::Alloc as _,
                Inst::SetLocal as _,
                0,
                Inst::GetLocal as _,
                3,
                Inst::Const as _,
                1,
                Inst::Neq as _,
                Inst::Jz as _,
                (24i16 << 8) as u8,
                24 & 0xFF,
                Inst::Pop as _,
                Inst::GetLocal as _,
                2, // 4 = tmp
                Inst::GetLocal as _,
                2,
                Inst::GetLocal as _,
                1,
                Inst::Add as _,
                Inst::SetLocal as _,
                2,
                Inst::SetLocal as _,
                1, // a = tmp
                Inst::GetLocal as _,
                3,
                Inst::Const as _,
                2,
                Inst::Sub as _,
                Inst::SetLocal as _,
                3, // n -= 1
                Inst::Jmp as _,
                unsafe { std::mem::transmute((-28i16 << 8) as i8) },
                unsafe { std::mem::transmute((-28i16 & 0xFF) as i8) },
                Inst::Pop as _,
                Inst::GetLocal as _,
                1,
                Inst::GetLocal as _,
                0,
                Inst::SetField as _,
                4,
                Inst::GetLocal as _,
                0,
                Inst::Return as _,
            ],
        );
        let res = vm.run().unwrap().unbox();
        let obj = res.as_ptr().unwrap();
        match &*obj {
            HeapObject::Obj(obj) => {
                assert_eq!(obj.get("fib"), Some(&Value::Num(354224848179262000000.0)));
            }
            _ => unreachable!(),
        }
    }
}
