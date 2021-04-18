use ves_cc::CcContext;
use ves_runtime::{nanbox::NanBox, value::HeapObject, Value};

#[derive(Debug, Clone, Copy)]
pub enum Inst<'a> {
    Const(u16),
    Pop,
    Alloc,
    SetLocal(u8),
    GetLocal(u8),
    SetField(&'a str),
    GetField(&'a str),
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
pub struct VmEnum<'a> {
    ip: usize,
    stack: Vec<NanBox>,
    constants: Vec<NanBox>,
    heap: CcContext,
    instructions: Vec<Inst<'a>>,
    err: Option<String>,
}

impl VmEnum<'static> {
    pub fn new(heap: CcContext, constants: Vec<NanBox>, instructions: Vec<Inst<'static>>) -> Self {
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
            let inst = self.instructions[self.ip - 1].clone();
            // println!("ip={:03} {:#?} {:#?}", self.ip - 1, inst, self.stack);
            match inst {
                Inst::Const(c) => {
                    self.push(self.constants[c as usize].clone());
                }
                Inst::Pop => {
                    self.pop();
                }
                Inst::SetLocal(s) => {
                    self.stack[s as usize] = self.pop();
                }
                Inst::GetLocal(s) => {
                    self.push(self.stack[s as usize].clone());
                }
                Inst::SetField(n) => {
                    self.set_field(n);
                }
                Inst::GetField(n) => {
                    self.get_field(n);
                }
                Inst::Add => self.add(),
                Inst::Sub => self.sub(),
                Inst::Mul => self.mul(),
                Inst::Div => self.div(),
                Inst::Eq => self.eq(),
                Inst::Neq => self.neq(),
                Inst::Alloc => self.alloc(),
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

    fn alloc(&mut self) {
        self.push(NanBox::new(Value::from(self.heap.cc(HeapObject::Obj(
            std::collections::HashMap::with_capacity(3),
        )))));
    }

    fn jz(&mut self, offset: i16) {
        let val = self.peek();
        if val.is_ptr() {
            return;
        }
        let jmp = match val.clone().unbox() {
            Value::Num(n) => n != 0.0,
            Value::Bool(b) => b,
            Value::None => false,
            Value::Ptr(_) => unreachable!(),
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

    fn set_field(&mut self, n: &'static str) {
        let obj = self.pop();
        if !obj.is_ptr() {
            self.error(format!("{:?} is not an object", obj.unbox()));
            return;
        }
        let mut obj = unsafe { obj.unbox_pointer() }.0.get();
        match unsafe { obj.deref_mut() } {
            HeapObject::Obj(obj) => {
                obj.insert(std::borrow::Cow::Borrowed(n), self.pop().unbox());
            }
            HeapObject::Str(_) => {
                self.error("Strings do not support field assignment".to_string());
                return;
            }
        }
    }

    fn get_field(&mut self, n: &'static str) {
        let obj = self.pop();
        if !obj.is_ptr() {
            self.error(format!("{:?} is not an object", obj.unbox()));
            return;
        }
        let obj = unsafe { obj.unbox_pointer() }.0.get();
        match &*obj {
            HeapObject::Obj(obj) => match obj.get(n) {
                Some(r#ref) => self.push(NanBox::new(r#ref.clone())),
                None => self.error(format!("Object is missing the field `{}`.", n)),
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
    fn test_vm_enum_opcodes() {
        let mut vm = VmEnum::new(
            CcContext::new(),
            vec![
                NanBox::none(),
                NanBox::num(0.0),
                NanBox::num(1.0),
                NanBox::num(100.0),
            ],
            vec![
                Inst::Const(0), // 0 = obj
                Inst::Const(1), // 1 = a
                Inst::Const(2), // 2 = b
                Inst::Const(3), // 3 = n
                Inst::Alloc,
                Inst::SetLocal(0),
                Inst::GetLocal(3),
                Inst::Const(1),
                Inst::Neq,
                Inst::Jz(12),
                Inst::Pop,
                Inst::GetLocal(2), // 4 = tmp
                Inst::GetLocal(2),
                Inst::GetLocal(1),
                Inst::Add,
                Inst::SetLocal(2),
                Inst::SetLocal(1), // a = tmp
                Inst::GetLocal(3),
                Inst::Const(2),
                Inst::Sub,
                Inst::SetLocal(3), // n -= 1
                Inst::Jmp(-16),
                Inst::Pop,
                Inst::GetLocal(1),
                Inst::GetLocal(0),
                Inst::SetField("fib"),
                Inst::GetLocal(0),
                Inst::Return,
            ],
        );

        let value: Value = vm.run().unwrap().unbox();
        value.as_ptr_guard().unwrap().with(|cc| match &**cc {
            HeapObject::Obj(obj) => {
                assert_eq!(obj.get("fib"), Some(&Value::Num(354224848179262000000.0)));
            }
            HeapObject::Str(_) => unreachable!(),
        });
    }
}
