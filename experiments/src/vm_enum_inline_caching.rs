use ves_cc::{Cc, CcContext};
use ves_runtime::{
    nanbox::NanBox,
    objects::{
        ves_str::{StrCcExt, VesStr},
        ves_struct::{VesHashMap, VesInstance, VesStruct},
    },
    runtime::inline_cache::InlineCache,
    Value, VesObject,
};

#[derive(Debug, Clone)]
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
pub struct VmEnum {
    ip: usize,
    stack: Vec<NanBox>,
    constants: Vec<NanBox>,
    heap: CcContext,
    instructions: Vec<Inst>,
    ic: InlineCache,
    /// The type used by the Alloc instruction
    ty: Cc<VesStruct>,
    err: Option<String>,
}

impl VmEnum {
    pub fn new(heap: CcContext, constants: Vec<NanBox>, instructions: Vec<Inst>) -> Self {
        let mut fields = VesHashMap::new_in(heap.proxy_allocator());
        fields.insert(VesStr::on_heap(&heap, "n").view(), 0);
        fields.insert(VesStr::on_heap(&heap, "a").view(), 1);
        fields.insert(VesStr::on_heap(&heap, "b").view(), 2);
        let ty = heap.cc(VesStruct::new(
            fields,
            VesHashMap::new_in(heap.proxy_allocator()),
        ));
        let ic = InlineCache::new(instructions.len());
        Self {
            ip: 0,
            stack: Vec::with_capacity(256),
            heap,
            constants,
            instructions,
            ic,
            ty,
            err: None,
        }
    }

    pub fn reset(&mut self) {
        let cap = self.stack.capacity();
        self.stack = std::mem::replace(&mut self.stack, Vec::with_capacity(cap));

        self.ip = 0;
        self.err = None;
        self.ic = InlineCache::new(self.instructions.len());
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
                Inst::SetField(c) => self.set_field(self.constants[c as usize].clone()),
                Inst::GetField(c) => self.get_field(self.constants[c as usize].clone()),
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

    fn set_field(&mut self, n: NanBox) {
        let obj = self.pop();
        if !obj.is_ptr() {
            self.error(format!("{:?} is not an object", obj.unbox()));
            return;
        }
        let mut obj = unsafe { obj.unbox_pointer() }.0.get();
        if let VesObject::Instance(instance) = unsafe { obj.deref_mut() } {
            // Fast path
            if let Some(slot) = self.ic.get_property_cache(self.ip - 1, instance.ty()) {
                unsafe {
                    *instance.deref_mut().get_by_slot_index_unchecked_mut(slot) =
                        self.pop().unbox();
                }
                return;
            }

            let name = n.unbox().as_ptr().unwrap();
            let name = match *name {
                VesObject::Str(ref s) => s,
                VesObject::Instance(_) => unreachable!(),
                VesObject::Struct(_) => unreachable!(),
            };
            let slot = match instance.get_property_slot(name) {
                Some(slot) => slot,
                None => {
                    return self.error(format!("Object is missing the field `{}`.", name.str()))
                }
            } as usize;

            unsafe {
                *instance.deref_mut().get_by_slot_index_unchecked_mut(slot) = self.pop().unbox();
            }
            self.ic
                .update_property_cache(self.ip - 1, slot, instance.ty().clone());
            return;
        }
        self.error(format!(
            "Object `{:?}` does not support field assignment",
            obj
        ));
    }

    fn get_field(&mut self, n: NanBox) {
        let obj = self.pop();
        if !obj.is_ptr() {
            self.error(format!("{:?} is not an object", obj.unbox()));
            return;
        }
        let obj = unsafe { obj.unbox_pointer() }.0.get();
        if let VesObject::Instance(instance) = &*obj {
            // Fast path
            if let Some(slot) = self.ic.get_property_cache(self.ip - 1, instance.ty()) {
                self.push(NanBox::new(
                    instance.get_by_slot_index_unchecked(slot).clone(),
                ));
                return;
            }

            let name = n.unbox().as_ptr().unwrap();
            let name = match *name {
                VesObject::Str(ref s) => s,
                VesObject::Instance(_) => unreachable!(),
                VesObject::Struct(_) => unreachable!(),
            };
            let slot = match instance.get_property_slot(name) {
                Some(slot) => slot,
                None => {
                    return self.error(format!("Object is missing the field `{}`.", name.str()))
                }
            } as usize;

            let value = NanBox::new(instance.get_by_slot_index_unchecked(slot).clone());
            self.ic
                .update_property_cache(self.ip - 1, slot, instance.ty().clone());
            self.push(value);
            return;
        }

        self.error(format!(
            "Object `{:?}` does not support field accesses",
            obj
        ));
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
    fn test_vm_enum_opcodes_inline_caching() {
        let heap = CcContext::new();
        let mut vm = VmEnum::new(
            heap.clone(),
            vec![
                NanBox::num(100.0),
                NanBox::num(0.0),
                NanBox::num(1.0),
                NanBox::new(ves_runtime::Value::from(
                    heap.cc(VesObject::Str(VesStr::on_heap(&heap, "a").view())),
                )),
                NanBox::new(ves_runtime::Value::from(
                    heap.cc(VesObject::Str(VesStr::on_heap(&heap, "b").view())),
                )),
                NanBox::new(ves_runtime::Value::from(
                    heap.cc(VesObject::Str(VesStr::on_heap(&heap, "n").view())),
                )),
            ],
            {
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
                ]
            },
        );

        vm.reset();
        let res = vm.run().unwrap().unbox();
        assert_eq!(res, Value::Num(354224848179262000000.0));
        std::mem::drop(vm);
        heap.collect_cycles();
    }
}
