#![feature(allocator_api)]
extern crate static_assertions as sa;
extern crate ves_cc;

pub mod nanbox;
pub mod value;
pub mod ves_str;
pub mod ves_struct;

pub use value::Value;

sa::assert_eq_size!(Value, u128);
