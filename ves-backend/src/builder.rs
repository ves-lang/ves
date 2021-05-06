use std::{borrow::Cow, collections::HashMap};

use crate::emit::UpvalueInfo;
use crate::opcode::Opcode;
use crate::Result;
use crate::Span;
use ves_error::{FileId, VesError};
/* use ves_runtime::{NanBox, Value}; */

#[derive(Debug, Clone)]
pub struct Chunk {
    pub code: Vec<Opcode>,
    pub spans: Vec<Span>,
    pub constants: Vec<Value>,
    pub file_id: FileId,
}

// TEMP
#[derive(Debug, Clone)]
pub struct Function {
    pub name: String,
    /// How many positional arguments this function accepts
    pub positionals: u32,
    /// How many default arguments this function accepts
    pub defaults: u32,
    /// Whether or not this function accepts an arbitrary amount of arguments
    pub rest: bool,
    pub chunk: Chunk,
}

// TEMP
#[derive(Debug, Clone)]
pub struct Closure {
    pub function: Function,
    pub upvalues: Vec<UpvalueInfo>,
}

// TEMP
#[derive(Debug, Clone)]
pub struct ClosureDescriptor {
    pub fn_constant_index: u32,
    pub upvalues: Vec<UpvalueInfo>,
}

// TEMP: replace the usage of this with the actual ves_runtime Value once GC is implemented
#[derive(Debug, Clone)]
pub enum Value {
    Number(f64),
    String(String),
    Function(Function),
    Closure(Closure),
    ClosureDescriptor(ClosureDescriptor),
    /* Struct(Struct), */
}
impl Value {
    pub fn function<S: Into<String>>(
        name: S,
        positionals: u32,
        defaults: u32,
        rest: bool,
        chunk: Chunk,
    ) -> Self {
        Value::Function(Function {
            name: name.into(),
            positionals,
            defaults,
            rest,
            chunk,
        })
    }

    pub fn closure_desc(fn_constant_index: u32, upvalues: Vec<UpvalueInfo>) -> Self {
        Self::ClosureDescriptor(ClosureDescriptor {
            fn_constant_index,
            upvalues,
        })
    }
}

impl From<f64> for Value {
    fn from(value: f64) -> Self {
        Value::Number(value)
    }
}
impl<'a> From<Cow<'a, str>> for Value {
    fn from(value: Cow<'a, str>) -> Self {
        Value::String(value.to_string())
    }
}

#[derive(Clone, Debug)]
pub struct BytecodeBuilder {
    code: Vec<Opcode>,
    spans: Vec<Span>,
    constants: Vec<Value>,
    file_id: FileId,
}

impl BytecodeBuilder {
    pub fn new(fid: FileId) -> BytecodeBuilder {
        Self {
            code: vec![],
            spans: vec![],
            constants: vec![],
            file_id: fid,
        }
    }

    #[inline]
    pub fn file_id(&self) -> FileId {
        self.file_id
    }

    /// Get the current offset
    #[inline]
    pub fn offset(&self) -> u32 {
        self.code.len() as u32
    }

    pub fn patch<F>(&mut self, index: u32, callback: F, span: Span) -> Result<()>
    where
        F: Fn(&mut Opcode),
    {
        let end = self.code.len() - 1;
        let fid = self.file_id;
        callback(self.code.get_mut(index as usize).ok_or_else(|| {
            VesError::emit(
                format!(
                    "Attempted to patch opcode at index out of bounds ({}/{})",
                    index, end
                ),
                span,
                fid,
            )
        })?);
        Ok(())
    }

    pub fn op(&mut self, op: Opcode, span: Span) -> u32 {
        self.code.push(op);
        self.spans.push(span);
        (self.code.len() - 1) as u32
    }

    // Labels are compile-time only so they don't need spans
    pub fn label(&mut self, label: u32) {
        self.code.push(Opcode::Label(label));
    }

    pub fn constant(&mut self, value: Value, span: Span) -> Result<u32> {
        let index = self.constants.len() as u32;
        if index == u32::MAX {
            Err(VesError::emit(
                "Exceeded maximum number of constants in one bytecode chunk",
                span,
                self.file_id,
            ))
        } else {
            self.constants.push(value);
            Ok(index)
        }
    }

    /// Removes all labels in the chunk and patches virtual jumps.
    ///
    /// A virtual jump stores a *label id*, which is replaced with the label's address
    /// once the address is guaranteed to not change anymore.
    fn patch_jumps(&mut self, labels: Vec<u32>) {
        let mut labels = labels
            .into_iter()
            .map(|label| (label, -1i64))
            .collect::<HashMap<_, _>>();
        // There should be at least as many jumps as there are labels
        let mut jumps = Vec::with_capacity(labels.len());
        let mut patched_code = Vec::with_capacity(self.code.len());

        // TODO: copy opcodes in slices rather than 1-by-1
        for op in self.code.drain(..) {
            let inst = patched_code.len();
            match op {
                // Map the label at this location to the next instruction
                Opcode::Label(label) => {
                    assert!(
                        matches!(labels.insert(label, inst as _), Some(-1)),
                        "Encountered a non-unique label: {} at {}",
                        label,
                        inst
                    );
                    continue;
                }
                // Remember the jumps and its target label
                Opcode::Jump(label) => jumps.push((inst, label)),
                Opcode::JumpIfFalse(label) => jumps.push((inst, label)),
                _ => (),
            }

            patched_code.push(op);
        }

        for (jump_op_addr, label) in jumps {
            let label_addr = *labels
                .get(&label)
                .ok_or_else(|| format!("Attempted to patch a nonexistent label -- {}", label))
                .unwrap();
            assert!(
                label_addr >= 0,
                "Attempted to patch a label that isn't present in the chunk: {}",
                label
            );
            match &mut patched_code[jump_op_addr] {
                // Up until this point, jump stored the label ID,
                // replace it with the address of the associated label
                Opcode::Jump(ref mut addr) => *addr = label_addr as u32,
                Opcode::JumpIfFalse(ref mut addr) => *addr = label_addr as u32,
                _ => panic!("Attempted to patch a non-jump instruction"),
            }
        }

        self.code = patched_code;
    }

    pub fn finish(&mut self, labels: Vec<u32>) -> Chunk {
        use std::mem::take;

        self.patch_jumps(labels);
        Chunk {
            code: take(&mut self.code),
            spans: take(&mut self.spans),
            constants: take(&mut self.constants),
            file_id: self.file_id,
        }
    }
}
