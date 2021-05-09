// TODO: update this to reflect changes
//! A NanBox implementation inspired by <https://github.com/Marwes/nanbox> and <http://craftinginterpreters.com/optimization.html>. See the last link for more info.
//!
//! # Overview
//! Ves have four primitive values whose sizes allow us to take advantage of NaN Boxing, enabling efficient storage and type checking:
//! 1) Floats  -- double precision floating point number (63 bits)
//! 2) Booleans -- true/false (1 bit)
//! 3) None     -- none ( bits, only needs a type tag)
//! 4) Pointers -- reference-counted pointers to heap-allocated Ves objects (48 bits).
//!
//! We can store all of these values inside a NaN in the manner outlined in the diagram below.
//! The first bit of the NaN can be arbitrary, same as the 2 bits that follow the pointer payload, giving
//! us 3 bits of free spaces or 2^3 = 8 possible states in the worst case (numbers and pointers).
//!
//!```text,ignore
//!              Quiet Bit
//!  Free Bit        │  2 Free Bits
//!     │            │ ┌┬───────────
//!     │            │ ││
//!    ┌▼────────────▼─▼▼───────────────────────────────────────────────────────┐
//!    │01111111_11111100_00000000_00000000_00000000_00000000_00000000_000000000│
//!    └─▲──────────▲─▲───▲────────────────────────────────────────────────────▲┘
//!      │          │ │   └────────────────────────────────────────────────────┘
//!      │          │ │                      48 Pointer Bits
//!      │ Exponent │ └──────┐
//!      └──────────┘        │
//!        11  bits   Intel FP Indef.
//! ```
//!
//! We need at least 4 values to encode the 4 primitives types, and we would also like to encode whether a value
//! is a variant of a result (ok, err). One possible encoding layout for this is the following:
//!
//! 1. 000 - num (a normal f64 number)
//! 2. 001 - none
//! 3. 010 - bool ~if the 3rd and 4th pointer bits are 0, one of (ok, err) otherwise.~
//! 4. 011 - ptr
//! 5. 100 - ptr (ok)
//! 6. 101 - ptr (err)
//!
//! ## Not a QNaN - num
//! A regular 63-bit floating point number.
//!
//! ```text,ignore
//!   Tag = Not a QNAN
//!   ┌────────────┐
//!   │            │
//! ┌─▼────────────▼────────────────────────────────────────────────────────┐
//! │........_........_........_........_........_........_........_........│
//! └───────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## 001 - none
//! Encodes a none value.
//!
//! ```text,ignore
//!     Tag = 001           Pointer bits are all 0 = none
//!  ┌───────────────┐ ┌───────────────────────────────────────────────────┐
//! ┌▼──────────────▼▼─▼───────────────────────────────────────────────────▼┐
//! │01111111_11111101_00000000_00000000_00000000_00000000_00000000_00000000│
//! └───────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## 010 - bool
//! Encodes a bool that is possibly wrapped by an ok or err.
//!
//! ```text,ignore
//!     Tag = 010
//!  ┌──────────────┬┐                                              Value of the bool
//!  │              ││                                                     │
//! ┌▼──────────────▼▼─────────────────────────────────────────────────────▼┐
//! │01111111_11111110_........_........_........_........_........_.....YYX│
//! └────────────────────────────────────────────────────────────────────▲▲─┘
//!                                                                      └┘
//!                                                                      00 Variant Bits are 00 = normal bool
//!                                                                      ~01 Variant Bits are 01 = ok~
//!                                                                      ~10 Variant Bits are 10 = err~
//! ```
//!
//! ## 101, 110, 111 - ptr
//! Encodes a pointer: either a normal a pointer (011), a pointer behind an Ok (100), or a pointer behind an Err (101).
//!
//! ```text,ignore
//!      Tag = 101      A regular pointer
//!  ┌───────────────┐ ┌───────────────────────────────────────────────────┐
//! ┌▼──────────────▼▼─▼───────────────────────────────────────────────────▼┐
//! │11111111_11111101_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX│
//! └───────────────────────────────────────────────────────────────────────┘
//!      Tag = 110      A pointer wrapped in an ok
//!  ┌───────────────┐ ┌───────────────────────────────────────────────────┐
//! ┌▼──────────────▼▼─▼───────────────────────────────────────────────────▼┐
//! │11111111_11111110_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX│
//! └───────────────────────────────────────────────────────────────────────┘
//!      Tag = 111      A pointer wrapped in an err
//!  ┌───────────────┐ ┌───────────────────────────────────────────────────┐
//! ┌▼──────────────▼▼─▼───────────────────────────────────────────────────▼┐
//! │11111111_11111111_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX_XXXXXXXX│
//! └───────────────────────────────────────────────────────────────────────┘
//! ```
#![allow(clippy::unusual_byte_groupings)]

use std::ptr::NonNull;

use crate::gc::{VesPtr, VesRawPtr, VesRef};

use super::value::Value;

pub const QNAN: u64 = 0b01111111_11111100_00000000_00000000_00000000_00000000_00000000_00000000;

#[rustfmt::skip]
pub mod mask {
    pub const TAG: u64 =        0b10000000_00000011_00000000_00000000_00000000_00000000_00000000_00000000;
    pub const QNAN: u64 =       0b11111111_11111111_00000000_00000000_00000000_00000000_00000000_00000000;
    pub const PTR: u64 =        0b00000000_00000000_11111111_11111111_11111111_11111111_11111111_11111111;
}
#[rustfmt::skip]
pub mod tag {
    //                        HIGH BIT         LOW BITS
    //                            v               vv
    pub const FLOAT: u64 =      0b0_0000000000000_00_000000000000000000000000000000000000000000000000;
    pub const NONE: u64 =       0b0_1111111111111_01_000000000000000000000000000000000000000000000000;
    pub const BOOL: u64 =       0b0_1111111111111_10_000000000000000000000000000000000000000000000000;
    pub const PTR: u64 =        0b1_1111111111111_01_000000000000000000000000000000000000000000000000;
    pub const OK: u64 =         0b1_1111111111111_10_000000000000000000000000000000000000000000000000;
    pub const ERR: u64 =        0b1_1111111111111_11_000000000000000000000000000000000000000000000000;
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NanBoxVariant {
    Value,
    Ok,
    Err,
}

#[derive(Clone, Copy, PartialEq)]
pub struct NanBox(u64);

impl NanBox {
    pub fn new(value: Value) -> NanBox {
        match value {
            // Safety: Floats are stored as themselves so the transmute is perfectly safe
            Value::Num(n) => NanBox(n.to_bits()),
            Value::Bool(b) => NanBox(b as u64 | tag::BOOL),
            Value::None => Self::none(),
            // Safety: The nanbox's drop makes sure to decrement the refcount.
            Value::Ref(obj) => Self::box_ptr(obj.ptr()),
        }
    }

    pub fn with_variant(ptr: Value, variant: NanBoxVariant) -> Self {
        match ptr {
            Value::Ref(ptr) => {
                let raw = ptr.ptr().as_ptr() as u64;
                let masked = raw & mask::PTR;
                let tag = match variant {
                    NanBoxVariant::Value => tag::PTR,
                    NanBoxVariant::Ok => tag::OK,
                    NanBoxVariant::Err => tag::ERR,
                };
                NanBox(tag | masked)
            }
            // NOTE: We could consider eliminating this branch entirely with std::hint::unreachable() in release builds,
            //       although actually hitting it would then be UB.
            _ => panic!("Only pointers support variants"),
        }
    }

    #[inline]
    fn box_ptr(ptr: VesPtr) -> Self {
        let raw = ptr.as_ptr() as u64;
        let masked = raw & mask::PTR;
        NanBox(tag::PTR | masked)
    }

    #[inline]
    fn masked(&self) -> u64 {
        self.0 & mask::QNAN
    }

    #[inline]
    pub fn raw_bits(&self) -> u64 {
        self.0
    }

    #[inline]
    pub fn none() -> Self {
        Self(tag::NONE)
    }

    #[inline]
    pub fn num(n: f64) -> Self {
        Self(n.to_bits())
    }

    pub fn int(n: i32) -> Self {
        todo!()
    }

    pub fn int_48(n: i64) -> Option<Self> {
        todo!()
    }

    #[inline]
    pub fn r#true() -> Self {
        Self(tag::BOOL | 1)
    }

    #[inline]
    pub fn r#false() -> Self {
        Self(tag::BOOL)
    }

    #[inline]
    pub fn is_num(&self) -> bool {
        (self.0 & QNAN) != QNAN
    }

    #[inline]
    pub fn is_none(&self) -> bool {
        self.0 == tag::NONE
    }

    #[inline]
    pub fn is_bool(&self) -> bool {
        self.masked() == tag::BOOL
    }

    #[inline]
    pub fn is_ptr(&self) -> bool {
        self.masked() >= tag::PTR
    }

    #[inline]
    pub fn is_normal_ptr(&self) -> bool {
        self.masked() == tag::PTR
    }

    #[inline]
    pub fn is_ok(&self) -> bool {
        self.masked() == tag::OK
    }

    #[inline]
    pub fn is_err(&self) -> bool {
        self.masked() == tag::ERR
    }

    #[inline]
    pub fn is_result_variant(&self) -> bool {
        let masked = self.masked();
        masked == tag::OK || masked == tag::ERR
    }

    /// Unboxes the boxed value into a raw f64.
    ///
    /// # Safety
    /// The caller must ensure that the boxed value is an f64. Failure to do so will result in a NaN
    /// being returned.
    #[inline(always)]
    pub fn as_num_unchecked(&self) -> f64 {
        f64::from_bits(self.0)
    }

    /// Unboxes the boxed value into a raw f64, consuming the nanbox.
    ///
    /// # Safety
    /// The caller must ensure that the boxed value is an f64. Failure to do so may result in a memory leak
    /// and a NaN being returned.
    #[inline(always)]
    pub unsafe fn into_num_unchecked(self) -> f64 {
        let this = std::mem::ManuallyDrop::new(self);
        f64::from_bits(this.0)
    }

    /// Unboxes the nanbox into a Value, without cloning and re-recreating the wrapper valued.
    /// This means that if the object is a pointer, its ref count will not be changed.
    /// Also see [`Self::unbox_with_variant`].
    #[inline]
    pub fn unbox(self) -> Value {
        self.unbox_with_variant().0
    }

    /// Unboxes the nanbox into a tuple `(Value, NanBoxVariant)`, without cloning or re-creating the wrapped value.
    /// The variant is guaranteed to be `NanBoxVariant::Value` for all primitive types, but may additionally be
    /// `Ok` or `Err` if the value is a pointer.
    #[inline]
    pub fn unbox_with_variant(self) -> (Value, NanBoxVariant) {
        if self.is_num() {
            (
                Value::Num(unsafe { self.into_num_unchecked() }),
                NanBoxVariant::Value,
            )
        } else if self.is_none() {
            (Value::None, NanBoxVariant::Value)
        } else if self.is_bool() {
            debug_assert!(self.is_bool());
            (Value::Bool(self.0 & 1 == 1), NanBoxVariant::Value)
        } else {
            let res = unsafe { self.unbox_pointer() };
            (Value::Ref(res.0), res.1)
        }
    }

    /// Unboxes the nanbox into a tuple (Value::Ptr, NanBoxVariant), without cloning or re-rcreating the wrapped value.
    /// This function doesn't perform any safety or type checks in release mode, and therefore, is unsafe.
    ///
    /// # Safety
    /// The caller must ensure that the nanbox contains a pointer. Failure to do so will result into executing
    /// operations such on completely random memory.
    #[allow(unused_unsafe)]
    pub unsafe fn unbox_pointer(self) -> (VesRef, NanBoxVariant) {
        debug_assert!(self.is_ptr());

        let masked = self.masked();
        let ptr = (self.0 & mask::PTR) as VesRawPtr;
        debug_assert!(!ptr.is_null());

        let ptr = unsafe { VesRef::new(NonNull::new_unchecked(ptr)) };
        let variant = match masked {
            tag::PTR => NanBoxVariant::Value,
            tag::OK => NanBoxVariant::Ok,
            _ => {
                debug_assert_eq!(masked, tag::ERR);
                NanBoxVariant::Err
            }
        };
        (ptr, variant)
    }
}

impl<V: Into<Value>> From<V> for NanBox {
    fn from(value: V) -> Self {
        NanBox::new(value.into())
    }
}

impl std::fmt::Debug for NanBox {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !f.alternate() {
            write!(f, "NanBox({:064b})", self.0)
        } else {
            writeln!(f, "NanBox {{")?;
            writeln!(f, "    boxed   = {:064b},", self.0)?;
            writeln!(
                f,
                "    tag     = {:064b} ({}),",
                if self.is_num() {
                    0
                } else {
                    (self.0 & mask::QNAN) & (!QNAN)
                },
                if self.is_num() {
                    "num"
                } else if self.is_none() {
                    "none"
                } else if self.is_ptr() {
                    "ptr"
                } else if self.is_bool() {
                    "bool"
                } else {
                    unimplemented!()
                }
            )?;
            writeln!(
                f,
                "    variant = {}",
                if self.is_ok() {
                    "OK"
                } else if self.is_err() {
                    "ERR"
                } else {
                    "N/A"
                }
            )?;
            writeln!(
                f,
                "    value   = {}",
                if self.is_ptr() {
                    format!("{:#?}", self.unbox())
                } else {
                    format!("{:?}", self.unbox())
                }
            )?;
            write!(f, "}}")
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::gc::{Roots, VesGc};

    use super::*;

    #[test]
    fn test_mask_ptr() {
        let ptr = 0x944fc8669b86u64 as *const i32;
        let raw = ptr as u64;
        let masked = raw & mask::PTR;
        let tagged = tag::PTR | masked;
        let unmasked = tagged & mask::PTR;
        assert_eq!(raw, unmasked);
    }

    #[test]
    fn test_nanbox_predicates() {
        let none = NanBox::none();
        assert!(none.is_none());
        assert!(!none.is_num());
        assert_eq!(none.0, tag::NONE);
        println!("{:#?}", none);

        let num = NanBox::new(Value::Num(std::f64::consts::PI));
        assert!(num.is_num());
        assert!(!num.is_none());
        assert_eq!(num.0, std::f64::consts::PI.to_bits());
        println!("{:#?}", num);

        for value in &[false, true] {
            let boolean = NanBox::new(Value::Bool(*value));
            assert!(boolean.is_bool());
            assert!(!boolean.is_num());
            assert!(!boolean.is_none());
            assert!(!boolean.is_ptr());
            println!("{:#?}", boolean);
            assert_eq!(boolean.unbox(), Value::Bool(*value));
        }

        macro_rules! alloc {
            ($gc:ident, $obj:expr) => {
                $gc.alloc(
                    $obj,
                    Roots {
                        stack: &mut vec![],
                        data: std::iter::empty(),
                    },
                )
                .unwrap()
            };
        }

        let mut gc = crate::gc::naive::NaiveMarkAndSweep::default();
        let ptr = alloc!(gc, "a string");

        let val = Value::from(ptr);
        let val = NanBox::new(val);
        assert!(!val.is_num());
        assert!(!val.is_none());
        assert!(!val.is_bool());
        assert!(val.is_ptr());
        assert!(!val.is_ok());
        assert!(!val.is_err());

        assert!(matches!(
            &**val.unbox().as_ptr().unwrap().as_str().unwrap().inner(),
            "a string"
        ));

        let clone = val;
        assert_eq!(val.0, clone.0);

        let unboxed = clone.unbox();
        let ok = NanBox::with_variant(unboxed, NanBoxVariant::Ok);
        assert!(ok.is_ptr());
        assert!(ok.is_ok());
        assert!(!ok.is_err());
        println!("{:#?}", ok);

        let (unboxed, _) = ok.unbox_with_variant();
        let err = NanBox::with_variant(unboxed, NanBoxVariant::Err);
        assert!(err.is_ptr());
        assert!(!err.is_ok());
        assert!(err.is_err());
    }
}
