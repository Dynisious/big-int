//! Defines variable length big integers.
//! 
//! Author --- DMorgan  
//! Last Moddified --- 2019-12-31

#![no_std]
#![deny(missing_docs,)]
#![feature(const_fn, const_if_match, try_blocks, never_type, int_error_matching, str_strip, wrapping_next_power_of_two,)]

#[macro_use]
extern crate alloc;

use core::{fmt, num::IntErrorKind,};

pub mod uint;
pub mod sint;
pub mod serde;

pub use self::{uint::UInt, sint::SInt,};

/// The error returned when trying to convert a big int into another type.
#[derive(Clone, Copy,)]
pub struct FromIntError<N,>(pub(crate) N,);

impl<N,> FromIntError<N,> {
  /// Unwraps the number inside the error.
  #[inline]
  pub fn into_inner(self,) -> N { self.0 }
}

impl<N,> fmt::Debug for FromIntError<N,>
  where N: fmt::Debug, {
  #[inline]
  fn fmt(&self, fmt: &mut fmt::Formatter,) -> fmt::Result { write!(fmt, "FromUIntError({:?})", self.0,) }
}

/// An error encountered while parsing a string.
#[derive(PartialEq, Eq, Clone, Debug,)]
pub struct ParseIntError(pub(crate) IntErrorKind,);

impl ParseIntError {
  /// The detailed cause for this error.
  #[inline]
  pub const fn kind(&self,) -> &IntErrorKind { &self.0 }
}

impl fmt::Display for ParseIntError {
  fn fmt(&self, fmt: &mut fmt::Formatter,) -> fmt::Result {
    let description = match self.0 {
      IntErrorKind::Empty => "cannot parse integer from empty string",
      IntErrorKind::InvalidDigit => "invalid digit found in string",
      _ => unsafe { core::hint::unreachable_unchecked() },
    };

    fmt.write_str(description,)
  }
}

mod private {

  #[doc(hidden,)]
  pub trait Sealed {}

}
