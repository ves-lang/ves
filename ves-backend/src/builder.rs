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

    pub fn op(&mut self, op: Opcode, span: Span) -> &mut Self {
        self.code.push(op);
        self.spans.push(span);
        self
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

    pub fn finish(self) -> Chunk {
        Chunk {
            code: self.code,
            spans: self.spans,
            constants: self.constants,
            file_id: self.file_id,
        }
    }
}
