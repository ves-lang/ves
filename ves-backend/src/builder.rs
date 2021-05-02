use crate::opcode::Opcode;
use crate::Result;
use crate::Span;
use ves_error::{FileId, VesError};
use ves_runtime::{NanBox, Value};

pub struct Chunk {
    pub code: Vec<Opcode>,
    pub spans: Vec<Span>,
    pub constants: Vec<NanBox>,
    pub file_id: FileId,
}

#[derive(Clone, Debug)]
pub struct BytecodeBuilder {
    code: Vec<Opcode>,
    spans: Vec<Span>,
    constants: Vec<NanBox>,
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

    /// Get the current offset
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

    pub fn constant(&mut self, value: Value, span: Span) -> Result<u32> {
        let index = self.constants.len() as u32;
        if index == u32::MAX {
            Err(VesError::emit(
                "Exceeded maximum number of constants in one bytecode chunk",
                span,
                self.file_id,
            ))
        } else {
            self.constants.push(NanBox::new(value));
            Ok(index)
        }
    }

    pub fn finish(&mut self) -> Chunk {
        use std::mem::take;
        Chunk {
            code: take(&mut self.code),
            spans: take(&mut self.spans),
            constants: take(&mut self.constants),
            file_id: self.file_id,
        }
    }
}
