//! A NanBox implementation inspired by <https://github.com/Marwes/nanbox> and <http://craftinginterpreters.com/optimization.html>. See the last link for more info.
//!
//! # Overview
//! Ves have four primitive values whose sizes allow us to take advantage of NaN Boxing, enabling efficient storage and type checking:
//! 1) Numbers  -- double precision floating point number (63 bits)
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

use std::ptr::NonNull;

use crate::value::{PtrGuard, VesPtr, VesRawPtr, VesRef};

use super::value::Value;

// The size of a pointer on 64-bit systems.
const TAG_SHIFT: u64 = 48;
const HIGH_BIT: u64 = 1 << 63;
const QNAN: u64 = 0x7ffc000000000000;
const TAG_MASK: u64 = HIGH_BIT | (0b11 << TAG_SHIFT);
const QNAN_TAG_MASK: u64 = QNAN | TAG_MASK;
const PTR_MASK: u64 = (1 << TAG_SHIFT) - 1;

pub const NUM_TAG: u64 = 0;
pub const NONE_TAG: u64 = QNAN ^ (0b01 << TAG_SHIFT);
pub const BOOL_TAG: u64 = QNAN ^ (0b10 << TAG_SHIFT);
pub const PTR_TAG: u64 = HIGH_BIT | QNAN ^ (0b01 << TAG_SHIFT);
pub const PTR_OK_TAG: u64 = HIGH_BIT | QNAN ^ (0b10 << TAG_SHIFT);
pub const PTR_ERR_TAG: u64 = HIGH_BIT | QNAN ^ (0b11 << TAG_SHIFT);

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NanBoxVariant {
    Value,
    Ok,
    Err,
}

#[derive(PartialEq)]
pub struct NanBox(u64);

impl NanBox {
    pub fn new(value: Value) -> NanBox {
        match value {
            // Safety: Floats are stored as themselves so the transmute is perfectly safe
            Value::Num(n) => NanBox(n.to_bits()),
            Value::Bool(b) => NanBox(b as u64 | BOOL_TAG),
            Value::None => Self::none(),
            // Safety: The nanbox's drop makes sure to decrement the refcount.
            Value::Ptr(ptr) => Self::box_ptr(unsafe { ptr.get_unchecked() }),
        }
    }

    pub fn with_variant(ptr: Value, variant: NanBoxVariant) -> Self {
        match ptr {
            Value::Ptr(ptr) => {
                let raw = unsafe { ptr.get_unchecked() }.as_ptr() as u64;
                let masked = raw & PTR_MASK;
                let tag = match variant {
                    NanBoxVariant::Value => PTR_TAG,
                    NanBoxVariant::Ok => PTR_OK_TAG,
                    NanBoxVariant::Err => PTR_ERR_TAG,
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
        let masked = raw & PTR_MASK;
        NanBox(PTR_TAG | masked)
    }

    #[inline]
    fn masked(&self) -> u64 {
        self.0 & QNAN_TAG_MASK
    }

    #[inline]
    pub fn none() -> Self {
        Self(NONE_TAG)
    }

    #[inline]
    pub fn is_num(&self) -> bool {
        (self.0 & QNAN) != QNAN
    }

    #[inline]
    pub fn is_none(&self) -> bool {
        self.0 == NONE_TAG
    }

    #[inline]
    pub fn is_bool(&self) -> bool {
        self.masked() == BOOL_TAG
    }

    #[inline]
    pub fn is_ptr(&self) -> bool {
        self.masked() >= PTR_TAG
    }

    #[inline]
    pub fn is_normal_ptr(&self) -> bool {
        self.masked() == PTR_TAG
    }

    #[inline]
    pub fn is_ok(&self) -> bool {
        self.masked() == PTR_OK_TAG
    }

    #[inline]
    pub fn is_err(&self) -> bool {
        self.masked() == PTR_ERR_TAG
    }

    #[inline]
    pub fn is_result_variant(&self) -> bool {
        let masked = self.masked();
        masked == PTR_OK_TAG || masked == PTR_ERR_TAG
    }

    pub fn try_access_pointer<T, F>(&self, f: F) -> Option<T>
    where
        F: Fn(&VesRef) -> T,
    {
        if !self.is_ptr() {
            return None;
        }
        let ptr = (self.0 & PTR_MASK) as VesRawPtr;
        debug_assert!(!ptr.is_null());

        // Safety: We make sure to construct and leak the pointer without incrementing or decrementing the ref count.
        //         Additionally, no Ves reference can be null, so the unchecked call is safe.
        let cc = unsafe { VesRef::from_raw(NonNull::new_unchecked(ptr)) };
        let result = f(&cc);
        let _ = unsafe { VesRef::leak(cc) };

        Some(result)
    }

    /// Unboxes the boxed value into a raw f64.
    ///
    /// # Safety
    /// The caller must ensure that the boxed value is an f64. Failure to do so will result in a NaN
    /// being returned.
    #[inline(always)]
    pub unsafe fn as_num_unchecked(&self) -> f64 {
        f64::from_bits(self.0)
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
                Value::Num(unsafe { self.as_num_unchecked() }),
                NanBoxVariant::Value,
            )
        } else if self.is_none() {
            (Value::None, NanBoxVariant::Value)
        } else if self.is_bool() {
            debug_assert!(self.is_bool());
            (Value::Bool(self.0 & 1 == 1), NanBoxVariant::Value)
        } else {
            unsafe { self.unbox_pointer() }
        }
    }

    /// Unboxes the nanbox into a tuple (Value::Ptr, NanBoxVariant), without cloning or re-rcreating the wrapped value.
    /// This function doesn't perform any safety or type checks in release mode, and therefore, is unsafe.
    ///
    /// # Safety
    /// The caller must ensure that the nanbox contains a pointer. Failure to do so will result into executing
    /// operations such on completely random memory.
    #[allow(unused_unsafe)]
    pub unsafe fn unbox_pointer(self) -> (Value, NanBoxVariant) {
        debug_assert!(self.is_ptr());

        let masked = self.masked();
        let this = std::mem::ManuallyDrop::new(self);
        let ptr = (this.0 & PTR_MASK) as VesRawPtr;
        debug_assert!(!ptr.is_null());
        // Safety: We make sure to avoid calling the drop impl for this nanbox, thus avoiding decrementing the refcount,
        //         while transferring the ownership of the CC to the guard (which correctly handles the refcount semantics).
        let ptr = Value::Ptr(unsafe { PtrGuard::new_unchecked(NonNull::new_unchecked(ptr)) });
        let variant = match masked {
            PTR_TAG => NanBoxVariant::Value,
            PTR_OK_TAG => NanBoxVariant::Ok,
            _ => {
                debug_assert_eq!(masked, PTR_ERR_TAG);
                NanBoxVariant::Err
            }
        };
        (ptr, variant)
    }
}

impl Clone for NanBox {
    fn clone(&self) -> Self {
        self.try_access_pointer(|cc| Self::box_ptr(unsafe { VesRef::clone(&cc).leak() }))
            .unwrap_or_else(|| Self(self.0))
    }
}

impl Drop for NanBox {
    fn drop(&mut self) {
        if self.is_ptr() {
            let ptr = (self.0 & PTR_MASK) as VesRawPtr;
            debug_assert!(!ptr.is_null());
            // Safety: Ves references cannot be null, and PtrGuard correctly handles refcounts for us.
            unsafe {
                std::mem::drop(PtrGuard::new_unchecked(NonNull::new_unchecked(ptr)));
            }
        }
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
                    (self.0 & QNAN_TAG_MASK) & (!QNAN)
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
                    format!("{:#?}", self.clone().unbox())
                } else {
                    format!("{:?}", self.clone().unbox())
                }
            )?;
            write!(f, "}}")
        }
    }
}

#[cfg(test)]
mod tests {
    use ves_cc::CcContext;

    use super::*;

    #[test]
    fn test_nanbox_tags() {
        println!("{:064b}", QNAN);
        println!("{:064b}", TAG_MASK);
        println!("{:064b}", QNAN_TAG_MASK);
        println!("{:064b}", NUM_TAG);
        println!("{:064b}", NONE_TAG);
        println!("{:064b}", BOOL_TAG);
        println!("{:064b}", PTR_TAG);

        assert_eq!(NUM_TAG, 0);
        assert_eq!(
            NONE_TAG,
            0b01111111_11111101_00000000_00000000_00000000_00000000_00000000_00000000
        );
        assert_eq!(
            BOOL_TAG,
            0b01111111_11111110_00000000_00000000_00000000_00000000_00000000_00000000
        );
        assert_eq!(
            PTR_TAG,
            0b11111111_11111101_00000000_00000000_00000000_00000000_00000000_00000000
        );
        assert_eq!(
            PTR_OK_TAG,
            0b11111111_11111110_00000000_00000000_00000000_00000000_00000000_00000000
        );
        assert_eq!(
            PTR_ERR_TAG,
            0b11111111_11111111_00000000_00000000_00000000_00000000_00000000_00000000
        );
    }

    #[test]
    fn test_ptr_masking() {
        let ptr = 0x944fc8669b86u64 as *const i32;
        let raw = ptr as u64;
        let masked = raw & PTR_MASK;
        let tagged = PTR_TAG | masked;
        let unmasked = tagged & PTR_MASK;
        assert_eq!(raw, unmasked);
    }

    #[test]
    fn test_nanbox_predicates() {
        let none = NanBox::none();
        assert!(none.is_none());
        assert!(!none.is_num());
        assert_eq!(none.0, NONE_TAG);
        println!("{:#?}", none);

        let num = NanBox::new(Value::Num(std::f64::consts::PI));
        assert!(num.is_num());
        assert!(!num.is_none());
        assert_eq!(num.0, unsafe {
            std::mem::transmute::<f64, u64>(std::f64::consts::PI)
        });
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

        let ctx = CcContext::new();
        let ptr = ctx.cc(super::super::value::HeapObject::Str("a string".into()));
        let val = Value::from(ptr);
        let val = NanBox::new(val);
        assert!(!val.is_num());
        assert!(!val.is_none());
        assert!(!val.is_bool());
        assert!(val.is_ptr());
        assert!(!val.is_ok());
        assert!(!val.is_err());

        val.try_access_pointer(|cc| {
            assert_eq!(cc.strong_count(), 1);
        });

        let clone = val.clone();
        assert!(clone.is_ptr());
        assert_eq!(val.0, clone.0);

        val.try_access_pointer(|cc| assert_eq!(cc.strong_count(), 2));
        clone.try_access_pointer(|cc| assert_eq!(cc.strong_count(), 2));

        std::mem::drop(val);
        clone.try_access_pointer(|cc| assert_eq!(cc.strong_count(), 1));

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
