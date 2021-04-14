extern crate static_assertions as sa;
extern crate ves_cc;

pub mod nanbox;
pub mod value;

pub use value::Value;

sa::assert_eq_size!(Value, u128);

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
