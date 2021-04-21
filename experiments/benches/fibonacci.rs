use criterion::{black_box, criterion_group, criterion_main, Criterion};

use experiments::{vm_bytes, vm_enum, vm_enum_inline_caching};
use ves_cc::CcContext;
use ves_runtime::{
    nanbox::NanBox,
    objects::ves_str::{StrCcExt, VesStr},
    VesObject,
};

fn get_enum_vm() -> vm_enum::VmEnum {
    use vm_enum::Inst;
    let heap = CcContext::new();
    vm_enum::VmEnum::new(
        heap.clone(),
        vec![
            NanBox::num(200.0),
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
    )
}

fn get_enum_ic_vm() -> vm_enum_inline_caching::VmEnum {
    use vm_enum_inline_caching::Inst;
    let heap = CcContext::new();
    vm_enum_inline_caching::VmEnum::new(
        heap.clone(),
        vec![
            NanBox::num(200.0),
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
    )
}

fn get_byte_vm() -> vm_bytes::VmBytes {
    use vm_bytes::Inst;
    let ctx = CcContext::new();
    vm_bytes::VmBytes::new(
        ctx.clone(),
        vec![
            NanBox::num(200.0),
            NanBox::num(0.0),
            NanBox::num(1.0),
            NanBox::new(ves_runtime::Value::from(
                ctx.cc(VesObject::Str(VesStr::on_heap(&ctx, "a").view())),
            )),
            NanBox::new(ves_runtime::Value::from(
                ctx.cc(VesObject::Str(VesStr::on_heap(&ctx, "b").view())),
            )),
            NanBox::new(ves_runtime::Value::from(
                ctx.cc(VesObject::Str(VesStr::on_heap(&ctx, "n").view())),
            )),
        ],
        vec![
            Inst::Alloc as _,
            Inst::Const as _,
            0, // load 100.0
            Inst::GetLocal as _,
            0, // load obj
            Inst::SetField as _,
            5, // set obj.n = 100
            Inst::Const as _,
            1, // load 0.0
            Inst::GetLocal as _,
            0, // load obj
            Inst::SetField as _,
            3, // set obj.a = 0
            Inst::Const as _,
            2, // load 1.0
            Inst::GetLocal as _,
            0, // load obj
            Inst::SetField as _,
            4, // set obj.b = 1
            Inst::GetLocal as _,
            0, // load obj
            Inst::GetField as _,
            5, // get obj.n
            Inst::Const as _,
            1,              // load 0
            Inst::Neq as _, // obj.n != 0
            Inst::Jz as _,  // jz (obj.n == 0)
            (39i16 << 8) as u8,
            39 & 0xFF,
            Inst::Pop as _,
            Inst::GetLocal as _,
            0, // load obj
            Inst::GetField as _,
            4, // tmp = obj.b
            Inst::GetLocal as _,
            0, // load obj
            Inst::GetField as _,
            4, // get obj.b
            Inst::GetLocal as _,
            0, // load obj
            Inst::GetField as _,
            3,              // get obj.a
            Inst::Add as _, // a + b
            Inst::GetLocal as _,
            0, // load obj
            Inst::SetField as _,
            4, // set obj.b = a + b
            Inst::GetLocal as _,
            0, // load obj
            Inst::SetField as _,
            3, // set obj.a = tmp
            Inst::GetLocal as _,
            0, // load obj
            Inst::GetField as _,
            5, // get obj.n
            Inst::Const as _,
            2,              // load 1.0
            Inst::Sub as _, // n - 1
            Inst::GetLocal as _,
            0, // load obj
            Inst::SetField as _,
            5, // set obj.n = obj.n - 1
            Inst::Jmp as _,
            unsafe { std::mem::transmute((-44i16 << 8) as i8) },
            unsafe { std::mem::transmute((-44i16 & 0xFF) as i8) },
            Inst::Pop as _,
            Inst::GetLocal as _,
            0, // load obj
            Inst::GetField as _,
            3, // get obj.a
            Inst::Return as _,
        ],
    )
}

fn bench_fibonacci(c: &mut Criterion) {
    let mut group = c.benchmark_group("fibonacci");
    group.bench_function("<byte opcodes: fib-iterative(200)>", move |b| {
        let mut vm = get_byte_vm();
        b.iter(|| {
            vm.reset();
            black_box(vm.run().unwrap())
        })
    });
    group.bench_function("<enum opcodes: fib-iterative(200)>", move |b| {
        let mut vm = get_enum_vm();
        b.iter(|| {
            vm.reset();
            black_box(vm.run().unwrap())
        })
    });
    group.bench_function("<enum opcodes + IC: fib-iterative(200)>", move |b| {
        let mut vm = get_enum_ic_vm();
        b.iter(|| {
            vm.reset();
            black_box(vm.run().unwrap())
        })
    });
}

criterion_group!(benches, bench_fibonacci);
criterion_main!(benches);
