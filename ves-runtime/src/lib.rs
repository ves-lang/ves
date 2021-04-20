#![feature(allocator_api)]
extern crate static_assertions as sa;
extern crate ves_cc;

pub mod objects;

pub use self::objects::nanbox;
pub use self::objects::value;
pub use self::objects::ves_object;

pub use value::Value;

sa::assert_eq_size!(Value, u128);
