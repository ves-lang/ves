#![feature(
    box_syntax,
    box_patterns,
    allocator_api,
    linked_list_cursors,
    core_intrinsics,
    test
)]
#![allow(
    clippy::new_without_default,
    clippy::comparison_chain,
    clippy::needless_range_loop,
    clippy::wrong_self_convention,
    clippy::single_component_path_imports
)]
extern crate static_assertions as sa;

pub type Span = core::ops::Range<usize>;

mod macros;

pub mod emitter;
pub mod gc;
pub mod values;
pub mod vm;

use std::marker::PhantomData;

pub use self::values::nanbox;
pub use self::values::object;
pub use self::values::value;
pub use nanbox::NanBox;
pub use object::Object;
pub use value::Value;

pub struct Tagged<'a, T> {
    data: T,
    tag: PhantomData<&'a ()>,
}

impl<'a, T> std::ops::Deref for Tagged<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

sa::assert_eq_size!(Value, u128);
