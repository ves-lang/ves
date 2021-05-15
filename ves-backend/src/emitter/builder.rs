use std::collections::HashMap;

use super::opcode::Opcode;
use super::Result;
use crate::{runtime::inline_cache::InlineCache, Span, Value};
use ves_error::{FileId, VesError};
/* use ves_backend::{NanBox, Value}; */

#[derive(Debug, Clone)]
pub struct Chunk {
    // SHould the these vecs be allocated using the proxy allocator?
    pub code: Vec<Opcode>,
    pub spans: Vec<Span>,
    pub constants: Vec<Value>,
    pub cache: InlineCache,
    pub file_id: FileId,
}

#[derive(Clone, Debug)]
pub struct BytecodeBuilder {
    code: Vec<Opcode>,
    spans: Vec<Span>,
    constants: HashMap<Value, u32>,
    file_id: FileId,
}

impl BytecodeBuilder {
    pub fn new(fid: FileId) -> BytecodeBuilder {
        Self {
            code: vec![],
            spans: vec![],
            constants: HashMap::new(),
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

    pub fn get_prop(&mut self, idx: u32, span: Span) {
        self.with_ic(Opcode::GetProp, idx, span);
    }

    pub fn set_prop(&mut self, idx: u32, span: Span) {
        self.with_ic(Opcode::SetProp, idx, span);
    }

    pub fn get_magic(&mut self, idx: u32, span: Span) {
        self.with_ic(Opcode::InvokeMagicMethod, idx, span);
    }

    pub fn with_ic(&mut self, constructor: impl Fn(u32) -> Opcode, idx: u32, span: Span) {
        self.op(constructor(idx), span.clone());
        for _ in 0..3 {
            self.op(Opcode::Data(0), span.clone());
        }
    }

    // Labels are compile-time only so they don't need spans
    pub fn label(&mut self, label: u32) {
        self.code.push(Opcode::Label(label));
    }

    pub fn constant(&mut self, value: Value, span: Span) -> Result<u32> {
        let index = if let Some(index) = self.constants.get(&value) {
            *index
        } else {
            let index = self.constants.len() as _;
            self.constants.insert(value, index);
            index
        };
        if index == u32::MAX {
            Err(VesError::emit(
                format!(
                    "Exceeded maximum number of constants in one bytecode chunk ({})",
                    u32::MAX
                ),
                span,
                self.file_id,
            ))
        } else {
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

        let cache_size = self.code.len();
        Chunk {
            code: take(&mut self.code),
            spans: take(&mut self.spans),
            constants: {
                let mut constants = take(&mut self.constants).into_iter().collect::<Vec<_>>();
                constants.sort_by_key(|(_, idx)| *idx);
                constants.into_iter().map(|(v, _)| v).collect()
            },
            cache: InlineCache::new(cache_size),
            file_id: self.file_id,
        }
    }
}
