use criterion::{black_box, criterion_group, criterion_main, Criterion};

use experiments::{vm_bytes, vm_enum};
use ves_cc::CcContext;
use ves_runtime::{nanbox::NanBox, ves_str::VesStr};

fn get_enum_vm() -> vm_enum::VmEnum<'static> {
    use vm_enum::Inst;
    return vm_enum::VmEnum::new(
        CcContext::new(),
        vec![
            NanBox::none(),
            NanBox::num(0.0),
            NanBox::num(1.0),
            NanBox::num(200.0),
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
}

fn get_byte_vm() -> vm_bytes::VmBytes {
    use vm_bytes::Inst;
    let ctx = CcContext::new();
    vm_bytes::VmBytes::new(
        ctx.clone(),
        vec![
            NanBox::none(),
            NanBox::num(0.0),
            NanBox::num(1.0),
            NanBox::num(200.0),
            NanBox::new(ves_runtime::Value::from(ctx.cc(
                ves_runtime::value::HeapObject::Str(VesStr::on_heap(&ctx, "fib")),
            ))),
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
    )
}

fn bench_fibonacci(c: &mut Criterion) {
    let mut group = c.benchmark_group("fibonacci");
    group.bench_with_input(
        "<enum opcodes: fib-iterative(200)>",
        &get_enum_vm(),
        move |b, vm| {
            let mut vm = vm.clone();
            b.iter(|| {
                vm.reset();
                black_box(vm.run().unwrap())
            })
        },
    );
    group.bench_with_input(
        "<byte opcodes: fib-iterative(200)>",
        &get_byte_vm(),
        move |b, vm| {
            let mut vm = vm.clone();
            b.iter(|| {
                vm.reset();
                black_box(vm.run().unwrap())
            })
        },
    );
}

criterion_group!(benches, bench_fibonacci);
criterion_main!(benches);
