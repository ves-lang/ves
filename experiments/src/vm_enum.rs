use ves_cc::{Cc, CcContext};
use ves_runtime::{
    nanbox::NanBox,
    objects::{
        ves_str::{StrCcExt, VesStr},
        ves_struct::{VesHashMap, VesInstance, VesStruct},
    },
    Value, VesObject,
};

#[derive(Debug, Clone)]
pub enum Inst {
    Const(u8),
    Pop,
    Alloc,
    SetLocal(u8),
    GetLocal(u8),
    SetField(Value),
    GetField(Value),
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
pub struct VmEnum {
    ip: usize,
    stack: Vec<NanBox>,
    constants: Vec<NanBox>,
    heap: CcContext,
    instructions: Vec<Inst>,
    /// The type used by the Alloc instruction
    ty: Cc<VesStruct>,
    err: Option<String>,
}

impl VmEnum {
    pub fn new(heap: CcContext, constants: Vec<NanBox>, instructions: Vec<Inst>) -> Self {
        let mut fields = VesHashMap::new_in(heap.proxy_allocator());
        fields.insert(VesStr::on_heap(&heap, "fib").view(), 0);
        let ty = heap.cc(VesStruct::new(
            fields,
            VesHashMap::new_in(heap.proxy_allocator()),
        ));
        Self {
            ip: 0,
            stack: Vec::with_capacity(256),
            heap,
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
        self.push(NanBox::new(Value::from(self.heap.cc(VesObject::Instance(
            self.heap.cc(VesInstance::new(self.ty.clone())),
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
                    (VesObject::Str(l), VesObject::Str(r)) => self.push(NanBox::new(Value::from(
                        self.heap.cc(VesObject::Str(
                            VesStr::on_heap(&self.heap, l.clone_inner().into_owned() + &r[..])
                                .view(),
                        )),
                    ))),
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
            "Cannot divide objects `{:?}` and `{:?}`",
            left.unbox(),
            right.unbox()
        ))
    }

    fn set_field(&mut self, n: Value) {
        let obj = self.pop();
        if !obj.is_ptr() {
            self.error(format!("{:?} is not an object", obj.unbox()));
            return;
        }
        let name = n.as_ptr().unwrap();
        let name = match *name {
            VesObject::Str(ref s) => s,
            VesObject::Instance(_) => unreachable!(),
            VesObject::Struct(_) => unreachable!(),
        };
        let mut obj = unsafe { obj.unbox_pointer() }.0.get();
        match unsafe { obj.deref_mut() } {
            VesObject::Instance(obj) => unsafe {
                *obj.deref_mut().get_property_mut(name).unwrap() = self.pop().unbox();
            },
            VesObject::Struct(_) => {
                self.error("Structs do not support field assignment".to_string());
            }
            VesObject::Str(_) => {
                self.error("Strings do not support field assignment".to_string());
            }
        }
    }

    fn get_field(&mut self, n: Value) {
        let obj = self.pop();
        if !obj.is_ptr() {
            self.error(format!("{:?} is not an object", obj.unbox()));
            return;
        }
        let name = n.as_ptr().unwrap();
        let name = match *name {
            VesObject::Str(ref s) => s,
            VesObject::Instance(_) => unreachable!(),
            VesObject::Struct(_) => unreachable!(),
        };
        let obj = unsafe { obj.unbox_pointer() }.0.get();
        match &*obj {
            VesObject::Instance(instance) => match instance.get_property(name) {
                Some(r#ref) => self.push(NanBox::new(r#ref.clone())),
                None => self.error(format!("Object is missing the field `{}`.", name.str())),
            },
            VesObject::Struct(_) => {
                self.error("Structs do not support field access (?)".to_string());
            }
            VesObject::Str(_) => {
                self.error("Strings do not support field access".to_string());
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
        let heap = CcContext::new();
        let mut vm = VmEnum::new(
            heap.clone(),
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
                Inst::SetField(Value::from(
                    heap.cc(VesObject::Str(VesStr::on_heap(&heap, "fib").view())),
                )),
                Inst::GetLocal(0),
                Inst::Return,
            ],
        );

        let res = vm.run().unwrap().unbox();
        let obj = res.as_ptr().unwrap();
        match &*obj {
            VesObject::Instance(instance) => {
                assert_eq!(
                    instance.get_by_slot_index(0),
                    Some(&Value::Num(354224848179262000000.0))
                );
            }
            _ => unreachable!(),
        }

        std::mem::drop(obj);
        std::mem::drop(res);
        std::mem::drop(vm);
        heap.collect_cycles();
    }
}
