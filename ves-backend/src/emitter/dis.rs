use ves_error::VesFileDatabase;

use crate::{emitter::opcode::Opcode, objects::ves_fn::VesFn};

use super::builder::Chunk;

const DEFAULT_INDENT: usize = 0;

pub fn dis_func<N, S>(
    func: &VesFn,
    db: Option<&VesFileDatabase<N, S>>,
    indent: Option<usize>,
) -> String
where
    N: AsRef<str> + std::fmt::Display + Clone,
    S: AsRef<str>,
{
    let dis = dis_chunk(&func.chunk, db, indent.unwrap_or(DEFAULT_INDENT));
    let header = format!(
        "== VesFn `{}` [pos={} / def={} / rest={}; is_magic = {}] ==",
        &*func.name,
        func.arity.positional,
        func.arity.default,
        func.arity.rest as usize,
        func.is_magic_method
    );
    format!("{}\n{}", header, dis)
}

fn line_fmt<N, S>(ip: usize, chunk: &Chunk, db: Option<&VesFileDatabase<N, S>>) -> String
where
    N: AsRef<str> + std::fmt::Display + Clone,
    S: AsRef<str>,
{
    let span = chunk.spans.get(ip).cloned();
    let line = span
        .map(|span| {
            if let Some(db) = db {
                let (line, col) = db.location(chunk.file_id, &span);
                format!("{:<03}:{:<02}", line, col)
            } else {
                format!("{:?}", span)
            }
        })
        .unwrap_or_else(|| format!("<MISSING SPAN FOR IP={}>", ip));
    format!("{}|ip={:<03}", line, ip)
}

fn const_at(at: usize, chunk: &Chunk) -> String {
    format!(
        "'{}'",
        chunk
            .constants
            .get(at)
            .map(|v| format!("{}", v))
            .unwrap_or_else(|| format!("ERR: INVALID CONST INDEX `{}`", at))
    )
}

fn const_at_value(at: usize, chunk: &Chunk) -> Option<&crate::Value> {
    chunk.constants.get(at)
}

pub fn dis_chunk<N, S>(chunk: &Chunk, db: Option<&VesFileDatabase<N, S>>, indent: usize) -> String
where
    N: AsRef<str> + std::fmt::Display + Clone,
    S: AsRef<str>,
{
    let mut out = String::from("<chunk>\n");

    for (ip, op) in chunk.code.iter().enumerate() {
        let value = match op {
            // 0-byte operands
            Opcode::PushNone
            | Opcode::PushTrue
            | Opcode::PushFalse
            | Opcode::Pop
            | Opcode::Print
            | Opcode::Copy
            | Opcode::Negate
            | Opcode::Not
            | Opcode::Add
            | Opcode::Subtract
            | Opcode::Multiply
            | Opcode::Divide
            | Opcode::Power
            | Opcode::Remainder
            | Opcode::Compare
            | Opcode::IsCmpEqual
            | Opcode::CompareType
            | Opcode::IsCmpNotEqual
            | Opcode::IsCmpLessThan
            | Opcode::IsCmpLessEqual
            | Opcode::IsCmpGreaterThan
            | Opcode::IsCmpGreaterEqual
            | Opcode::Return
            | Opcode::GetItem
            | Opcode::SetItem
            | Opcode::AddOne
            | Opcode::SubtractOne
            | Opcode::MapExtend
            | Opcode::MapInsert
            | Opcode::CreateEmptyMap
            | Opcode::Defer
            | Opcode::Spread
            | Opcode::WrapOk
            | Opcode::WrapErr
            | Opcode::Try
            | Opcode::HasProperty => {
                format!(
                    "{}| {:<indent$}",
                    line_fmt(ip, chunk, db),
                    format!("{:?}", op),
                    indent = indent
                )
            }

            Opcode::GetConst(operand)
            | Opcode::CreateClosure(operand)
            | Opcode::SetProp(operand)
            | Opcode::GetProp(operand)
            | Opcode::TryGetProp(operand)
            | Opcode::GetMagicProp(operand) => {
                format!(
                    "{}| {:<indent$} %const = {}",
                    line_fmt(ip, chunk, db),
                    format!("{:?}", op),
                    const_at(*operand as usize, chunk),
                    indent = indent
                )
            }

            Opcode::CreateStruct(operand) => {
                let line = line_fmt(ip, chunk, db);
                let line_len = line.len() + 2 + (indent > 0) as usize;
                let mut out = format!(
                    "{}| {:<indent$} %const = {}",
                    line,
                    format!("{:?}", op),
                    const_at(*operand as usize, chunk),
                    indent = indent
                );

                if let Some(descriptor) =
                    const_at_value(*operand as _, chunk).and_then(|v| v.as_struct_descriptor())
                {
                    if descriptor.fields.is_empty() && descriptor.methods.is_empty() {
                        out.push_str(&format!(
                            "\n{: >pad$} <empty descriptor>",
                            "",
                            pad = line_len
                        ));
                    }

                    for (i, field) in descriptor.fields.iter().enumerate() {
                        out.push_str(&format!(
                            "\n{: >pad$} {:<indent$}%field @{} = {}",
                            "",
                            "",
                            i,
                            field.str(),
                            pad = line_len,
                            indent = indent,
                        ));
                    }

                    for (name, method) in &descriptor.methods {
                        out.push_str(&format!(
                            "\n{: >pad$} {:<indent$}%method @[{:02},{:02}] = {{ name: {}, fn: {} }}",
                            "",
                            "",
                            name,
                            method,
                            const_at(*name as _, chunk),
                            const_at(*method as _, chunk),
                            pad = line_len,
                            indent = indent
                        ));
                    }
                } else {
                    out.push_str(&format!(
                        "\n{: >pad$} <ERROR: FAILED TO RETRIEVE THE DESCRIPTOR>",
                        "",
                        pad = line_len
                    ));
                }
                out
            }

            Opcode::GetLocal(operand)
            | Opcode::SetLocal(operand)
            | Opcode::GetGlobal(operand)
            | Opcode::SetGlobal(operand)
            | Opcode::UnwrapOk(operand)
            | Opcode::UnwrapErr(operand)
            | Opcode::GetCapture(operand)
            | Opcode::SetCapture(operand) => {
                format!(
                    "{}| {:<indent$} @slot{}= {:>04}",
                    line_fmt(ip, chunk, db),
                    format!("{:?}", op),
                    if indent > 0 { "  " } else { " " },
                    operand,
                    indent = indent
                )
            }
            Opcode::CreateArray(operand)
            | Opcode::Interpolate(operand)
            | Opcode::PrintN(operand)
            | Opcode::CopyN(operand)
            | Opcode::PopN(operand)
            | Opcode::Call(operand) => {
                format!(
                    "{}| {:<indent$} #count = {:>04}",
                    line_fmt(ip, chunk, db),
                    format!("{:?}", op),
                    operand,
                    indent = indent
                )
            }

            Opcode::Jump(operand) | Opcode::JumpIfFalse(operand) => {
                format!(
                    "{}| {:<indent$} [{} -> {}]",
                    line_fmt(ip, chunk, db),
                    format!("{:?}", op),
                    ip,
                    operand,
                    indent = indent
                )
            }
            Opcode::PushInt32(_) => {
                format!(
                    "{}| {:<indent$}",
                    line_fmt(ip, chunk, db),
                    format!("{:?}", op),
                    indent = indent
                )
            }
            Opcode::Data(_) => {
                format!(
                    "{}| {:<indent$}",
                    line_fmt(ip, chunk, db),
                    format!("{:?}", op),
                    indent = indent
                )
            }
            Opcode::Label(lbl) => {
                format!(
                    "{}| <ERROR: UNPATCHED JUMP LABEL = {}> ",
                    line_fmt(ip, chunk, db),
                    lbl
                )
            }
        };
        out.push_str(&format!("|{}\n", value));
    }

    let mut n_funcs = 0;
    let nested = chunk
        .constants
        .iter()
        .flat_map(|ptr| ptr.as_ptr())
        .filter(|ptr| ptr.as_fn().is_some())
        .flat_map(|func| {
            let func = func.as_fn().unwrap();
            n_funcs += 1;
            let s = dis_func(func, db, Some(indent));
            s.split('\n')
                .map(|line| format!("\t{}", line))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>()
        .join("\n");

    format!(
        "{}<nested fn objects: {}>{}",
        out,
        n_funcs,
        if nested.is_empty() {
            "".to_string()
        } else {
            format!("\n{}", nested)
        },
    )
}

#[allow(dead_code)]
#[cfg(test)]
mod tests {
    use std::{collections::HashMap, path::PathBuf};

    use ves_middle::Resolver;
    use ves_parser::{Lexer, Parser};

    use crate::{
        emitter::{emit::Emitter, CompilationContext, VTables},
        gc::{DefaultGc, GcHandle},
    };

    use super::*;

    //#[test]
    fn test_dis_no_indent() {
        let expected = r#"
== VesFn `<main>` [pos=0 / def=0 / rest=0; is_magic = false] ==
<chunk>
|001:01|ip=000| CreateStruct
|001:01|ip=001| SetGlobal(0) @slot = 0000
|008:01|ip=002| Pop
|002:01|ip=003| CreateStruct
|002:01|ip=004| SetGlobal(1) @slot = 0001
|001:10|ip=005| Pop
|003:01|ip=006| CreateStruct
|003:01|ip=007| GetConst(1) %const = '<fn T2.init>'
|003:01|ip=008| AddMethod(0) %const = 'init'
|003:01|ip=009| SetGlobal(2) @slot = 0002
|002:13|ip=010| Pop
|004:01|ip=011| CreateStruct
|004:01|ip=012| GetConst(2) %const = '<fn T3.init>'
|004:01|ip=013| AddMethod(0) %const = 'init'
|004:01|ip=014| SetGlobal(3) @slot = 0003
|003:17|ip=015| Pop
|001:01|ip=016| Return
<nested fn objects: 2>
       == VesFn `T2.init` [pos=0 / def=0 / rest=0; is_magic = false] ==
       <chunk>
       |003:11|ip=000| PushNone
       |003:11|ip=001| GetLocal(0) @slot = 0000
       |003:11|ip=002| GetProp(0) %const = 'a'
       |003:11|ip=003| Data(0)
       |003:11|ip=004| Data(0)
       |003:11|ip=005| Data(0)
       |003:11|ip=006| PushNone
       |003:11|ip=007| Equal
       |003:11|ip=008| JumpIfFalse(18) [8 -> 18]
       |003:11|ip=009| Pop
       |003:11|ip=010| GetLocal(0) @slot = 0000
       |003:15|ip=011| PushInt32(0)
       |003:11|ip=012| SetProp(0) %const = 'a'
       |003:11|ip=013| Data(0)
       |003:11|ip=014| Data(0)
       |003:11|ip=015| Data(0)
       |003:11|ip=016| Pop
       |003:11|ip=017| Jump(19) [17 -> 19]
       |003:11|ip=018| Pop
       |003:11|ip=019| Pop
       |003:01|ip=020| Return
       <nested fn objects: 0>
       == VesFn `T3.init` [pos=0 / def=0 / rest=0; is_magic = false] ==
       <chunk>
       |004:11|ip=000| PushNone
       |004:11|ip=001| GetLocal(0) @slot = 0000
       |004:11|ip=002| GetProp(0) %const = 'a'
       |004:11|ip=003| Data(0)
       |004:11|ip=004| Data(0)
       |004:11|ip=005| Data(0)
       |004:11|ip=006| PushNone
       |004:11|ip=007| Equal
       |004:11|ip=008| JumpIfFalse(18) [8 -> 18]
       |004:11|ip=009| Pop
       |004:11|ip=010| GetLocal(0) @slot = 0000
       |004:15|ip=011| PushInt32(0)
       |004:11|ip=012| SetProp(0) %const = 'a'
       |004:11|ip=013| Data(0)
       |004:11|ip=014| Data(0)
       |004:11|ip=015| Data(0)
       |004:11|ip=016| Pop
       |004:11|ip=017| Jump(19) [17 -> 19]
       |004:11|ip=018| Pop
       |004:11|ip=019| Pop
       |006:15|ip=020| GetLocal(0) @slot = 0000
       |006:15|ip=021| GetProp(0) %const = 'a'
       |006:15|ip=022| Data(0)
       |006:15|ip=023| Data(0)
       |006:15|ip=024| Data(0)
       |006:15|ip=025| Print
       |004:01|ip=026| Return
       <nested fn objects: 0>"#
            .trim_start();
        assert_dis(None, expected)
    }

    fn assert_dis(indent: Option<usize>, expected: &str) {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join("codegen");
        let test = "t59_struct_expr_init";

        let source = ves_testing::load_test_file(&path, test).0;

        ves_testing::test_eq(test, source, expected.into(), |src| compile(src, indent));
    }

    pub fn compile(src: String, indent: Option<usize>) -> String {
        let mut fdb = VesFileDatabase::default();
        let fid = fdb.add_snippet(&src);
        let mut ast = Parser::new(Lexer::new(&src), fid, &fdb).parse().unwrap();
        Resolver::new().resolve(&mut ast).unwrap();
        let gc = GcHandle::new(DefaultGc::default());
        let mut vtables = VTables::init(gc.clone());
        let ptr = Emitter::new(
            &ast,
            CompilationContext {
                gc: gc.clone(),
                strings: &mut HashMap::new(),
                vtables: &mut vtables,
            },
        )
        .emit()
        .unwrap();
        let out = dis_func(ptr.as_fn().unwrap(), Some(&fdb), indent);
        std::mem::drop(gc);
        out
    }
}
