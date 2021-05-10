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
    clippy::needless_range_loop
)]
extern crate static_assertions as sa;

pub type Span = core::ops::Range<usize>;

pub mod emitter;
pub mod gc;
pub mod objects;
pub mod runtime;

use std::marker::PhantomData;

pub use self::objects::nanbox;
pub use self::objects::value;
pub use self::objects::ves_object;
pub use nanbox::NanBox;
pub use value::Value;
pub use ves_object::VesObject;

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
