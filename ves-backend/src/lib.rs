#![feature(box_syntax, box_patterns, allocator_api, linked_list_cursors)]
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

pub use self::objects::nanbox;
pub use self::objects::value;
pub use self::objects::ves_object;

pub use nanbox::NanBox;
pub use value::Value;
pub use ves_object::VesObject;

sa::assert_eq_size!(Value, u128);
