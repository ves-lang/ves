#![feature(allocator_api)]
extern crate static_assertions as sa;

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
