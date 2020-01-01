//! Author --- DMorgan  
//! Last Moddified --- 2019-12-31

use crate::{UInt, FromIntError, ParseIntError, private::Sealed,};
use alloc::{vec::Vec, boxed::Box,};
use core::{
  fmt,
  ops::{
    Neg,
    Rem, RemAssign,
    Add, AddAssign,
    Sub, SubAssign,
    Mul, MulAssign,
    Div, DivAssign,
  },
  cmp::Ordering,
  convert::TryFrom,
  str::FromStr,
  borrow::{Borrow, BorrowMut,},
  iter::FromIterator,
};

mod tests;
mod serde;

//I'm treating signed ints the same way as unsigned but with all the bits shifted by one and the lowest bit flagging sign.

/// An unsigned integer.
#[derive(Clone, Copy, Hash,)]
pub struct SInt<B = Vec<u8>,>(pub(crate) UInt<B,>,)
  where B: Borrow<[u8]>,;

impl SInt<Vec<u8>,> {
  /// A zero `SInt`.
  pub const ZERO: Self = SInt(UInt::ZERO,);
}

impl SInt<[u8; 1],> {
  /// A unit `SInt`.
  pub const ONE: Self = SInt(UInt([2,],),);
  /// A negative unit `SInt`.
  pub const NEG_ONE: Self = SInt(UInt([3,],),);
}

impl SInt<Vec<u8>,> {
  /// Creates a new `SInt` from a `Vec` of little endian bytes.
  /// 
  /// # Params
  /// 
  /// le_bytes --- The little endian bytes to encode.  
  #[inline]
  pub(crate) fn new(le_bytes: Vec<u8>,) -> Self { SInt(UInt::new(le_bytes,),) }
  /// Calculates the `remainder` after division by `rhs` and mutates `self` into the
  /// `quotient`.
  /// 
  /// The remainder will keep the sign of `self`.
  /// 
  /// # Params
  /// 
  /// divisor --- The right hand side of the division.  
  pub fn rem<A,>(&mut self, mut divisor: SInt<A,>,) -> SInt<Vec<u8>,>
    where A: BorrowMut<[u8]>, {
    let div_sign = divisor.signum();
    //Calculate the final sign of `self`.
    let signum = self.signum() * div_sign;

    //Clear the sign of `divisor` for the remainder calculation.
    divisor.mark_unsigned();
    //Calculate the remainder; no special treatment is needed as an unsigned `SInt` is an
    //even `UInt` therefore the remainder will keep the sign of `self`.
    let mut rem = SInt(UInt::rem(&mut self.0, divisor.0.into_slice(),),);
    if rem.0 == UInt::ONE { rem.0 = UInt::ZERO }

    //Restore the `divisor` sign.
    divisor.set_sign(div_sign == 1,);
    //Shift the `quotient` and set its sign.
    self.0 <<= 1usize;
    self.set_sign(signum == 1,);

    rem
  }
}

impl<A,> SInt<A,>
  where A: Borrow<[u8]>, {
  /// Returns a value representing the sign of `self`.
  /// 
  /// * `0` if the number is zero  
  /// * `1` if the number is positive  
  /// * `-1` if the number is negative  
  pub fn signum(&self,) -> i8 {
    match (self.0).0.borrow().first().map(|b,| (b & bitio::Bits::B1.bit()) == 0,) {
      None => 0,
      Some(true) => 1,
      Some(false) => -1,
    }
  }
  /// Borrows the bytes within this `SInt` as `slice` backed instance.
  #[inline]
  pub fn into_slice<'a,>(&'a self,) -> SInt<&'a [u8],> { SInt(self.0.into_slice(),) }
}

impl<A,> SInt<A,>
  where A: BorrowMut<[u8]>, {
  /// Sets this `SInt` to be unsigned.
  pub(crate) fn mark_unsigned(&mut self,) -> &mut Self {
    if let Some(byte) = (self.0).0.borrow_mut().first_mut() {
      //Clear the first bit to mark this as unsigned.
      *byte &= bitio::Bits::B1.not_mask()
    }

    self
  }
  /// Sets this `SInt` to be signed.
  pub(crate) fn mark_signed(&mut self,) -> &mut Self {
    if let Some(byte) = (self.0).0.borrow_mut().first_mut() {
      //Set the first bit to mark this as signed.
      *byte |= bitio::Bits::B1.bit()
    }

    self
  }
  /// Sets this `SInt`s sign.
  pub(crate) fn set_sign(&mut self, positive: bool,) -> &mut Self {
    if *self == SInt::ZERO { return self }
    if positive { self.mark_unsigned() }
    else { self.mark_signed() }
  }
  /// Converts the `SInt` bytes into a little endian `slice` of bytes with the lower bit
  /// indicating sign.
  #[inline]
  pub fn into_inner(self,) -> A { (self.0).0 }
  /// Borrows the bytes within this `SInt` as mutable `slice` backed instance.
  #[inline]
  pub fn into_slice_mut<'a,>(&'a mut self,) -> SInt<&'a mut [u8],> { SInt(self.0.into_slice_mut(),) }
}

pub use self::into_vec::*;

mod into_vec {
  use super::*;

  /// Used to get a mutable version of a `SInt`.
  pub trait IntoVec: Sealed {
    /// Creates a `SInt` backed by a `Vec` which has the same value as this `SInt`.
    fn into_vec(self,) -> SInt<Vec<u8>,>;
  }

  impl Sealed for SInt<Vec<u8>,> {}

  impl IntoVec for SInt<Vec<u8>,> {
    #[inline]
    fn into_vec(self,) -> SInt<Vec<u8>,> { self }
  }

  impl Sealed for SInt<&'_ [u8],> {}

  impl IntoVec for SInt<&'_ [u8],> {
    #[inline]
    fn into_vec(self,) -> SInt<Vec<u8>,> { SInt(UInt((self.0).0.into(),),) }
  }

  impl Sealed for SInt<&'_ mut [u8],> {}

  impl IntoVec for SInt<&'_ mut [u8],> {
    #[inline]
    fn into_vec(self,) -> SInt<Vec<u8>,> { SInt(UInt((self.0).0.into(),),) }
  }

  impl<A,> Sealed for &'_ SInt<A,>
    where A: Borrow<[u8]>, {}

  impl<A,> IntoVec for &'_ SInt<A,>
    where A: Borrow<[u8]>, {
    #[inline]
    fn into_vec(self,) -> SInt<Vec<u8>,> { SInt(UInt((self.0).0.borrow().into(),),) }
  }

  impl<A,> Sealed for &'_ mut SInt<A,>
    where A: Borrow<[u8]>, {}

  impl<A,> IntoVec for &'_ mut SInt<A,>
    where A: Borrow<[u8]>, {
    #[inline]
    fn into_vec(self,) -> SInt<Vec<u8>,> { SInt(UInt((self.0).0.borrow().into(),),) }
  }

}

mod cmp {
  use super::*;

  impl<A, B,> PartialEq<SInt<B,>> for SInt<A,>
    where A: Borrow<[u8]>,
      B: Borrow<[u8]>, {
    #[inline]
    fn eq(&self, rhs: &SInt<B,>,) -> bool { self.0.borrow() == rhs.0.borrow() }
  }

  impl<A,> Eq for SInt<A,>
    where A: Borrow<[u8]>, {}

  impl<A,> PartialEq<isize> for SInt<A,>
    where A: Borrow<[u8]>, {
    fn eq(&self, rhs: &isize,) -> bool { *self == SInt::from(*rhs,) }
  }

  impl<A, B,> PartialOrd<SInt<B,>> for SInt<A,>
    where A: Borrow<[u8]>,
      B: Borrow<[u8]>, {
    fn partial_cmp(&self, rhs: &SInt<B,>,) -> Option<Ordering> { Some(self.into_slice().cmp(&rhs.into_slice(),)) }
  }

  impl<A,> Ord for SInt<A,>
    where A: Eq + Borrow<[u8]>, {
    fn cmp(&self, rhs: &Self,) -> Ordering {
      let lhs_sign = self.signum();
      let rhs_sign = rhs.signum();

      //Compare the signums.
      let cmp = lhs_sign.cmp(&rhs_sign,);
      if cmp != Ordering::Equal { return cmp }

      let cmp = self.0.cmp(&rhs.0,);
      //If the signum is negative then the ordering is reversed.
      if lhs_sign == 1 { cmp } else { cmp.reverse() }
    }
  }

  impl<A,> PartialOrd<isize> for SInt<A,>
    where A: Borrow<[u8]>, {
    fn partial_cmp(&self, rhs: &isize,) -> Option<Ordering> { self.partial_cmp(&SInt::from(*rhs,),) }
  }

}

impl<A,> Neg for SInt<A,>
  where A: BorrowMut<[u8]>, {
  type Output = Self;

  fn neg(mut self,) -> Self::Output {
    //Flip the sign bit.
    if let Some(byte) = (self.0).0.borrow_mut().first_mut() { *byte ^= bitio::Bits::B1.bit() }

    self
  }
}

mod add {
  use super::*;

  impl AddAssign<SInt<Vec<u8>,>> for SInt<Vec<u8>,> {
    fn add_assign(&mut self, mut rhs: SInt<Vec<u8>,>,) {
      let lhs_sign = self.signum();
      //If the signs are equal or one is zero then the values are additive.
      let addition = (lhs_sign * rhs.signum()) >= 0;
      let lhs_sign = lhs_sign == 1;

      //Clear the signums of both values.
      self.mark_unsigned();
      rhs.mark_unsigned();

      if addition {
        //Add the values.
        self.0 += rhs.0;
        //Set the sign.
        self.set_sign(lhs_sign,);

        return
      }

      //Perform subtraction.

      match self.0.cmp(&rhs.0,) {
        //This is the larger value so subtraction is straight forward.
        Ordering::Greater => {
          self.0 -= rhs.0;
          //Restore the sign.
          self.set_sign(lhs_sign,);
        },
        //`rhs` is larger so the sign of the result will flip.
        Ordering::Less => {
          self.0 = rhs.0 - core::mem::replace(&mut self.0, UInt::ZERO,);
          self.set_sign(!lhs_sign,);
        },
        //The values cancel out.
        Ordering::Equal => *self = SInt::ZERO,
      }
    }
  }

  impl<'a, A,> AddAssign<&'a SInt<A,>> for SInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn add_assign(&mut self, rhs: &'a SInt<A,>,) { *self += rhs.into_vec() }
  }

  impl<'a, A,> AddAssign<&'a mut SInt<A,>> for SInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn add_assign(&mut self, rhs: &'a mut SInt<A,>,) { *self += &*rhs }
  }

  impl AddAssign<isize> for SInt<Vec<u8>,> {
    fn add_assign(&mut self, rhs: isize,) { *self += SInt::from(rhs,) }
  }

  impl<A, Rhs,> Add<Rhs,> for SInt<A,>
    where A: Borrow<[u8]>,
      SInt<Vec<u8>,>: AddAssign<Rhs>,
      Self: IntoVec, {
    type Output = SInt<Vec<u8>,>;

    fn add(self, rhs: Rhs,) -> Self::Output {
      let mut temp = self.into_vec();

      temp += rhs; temp
    }
  } 

  impl<A, Rhs,> Add<Rhs,> for &'_ SInt<A,>
    where A: Borrow<[u8]>,
      SInt<Vec<u8>,>: Add<Rhs>, {
    type Output = <SInt as Add<Rhs>>::Output;

    fn add(self, rhs: Rhs,) -> Self::Output { self.into_vec() + rhs }
  } 

  impl<A, Rhs,> Add<Rhs,> for &'_ mut SInt<A,>
    where A: Borrow<[u8]>,
      SInt<Vec<u8>,>: Add<Rhs>, {
    type Output = <SInt as Add<Rhs>>::Output;

    #[inline]
    fn add(self, rhs: Rhs,) -> Self::Output { &*self + rhs }
  }

}

mod sub {
  use super::*;

  impl<A,> SubAssign<SInt<A,>> for SInt<Vec<u8>,>
    where A: BorrowMut<[u8]>,
      SInt<Vec<u8>,>: AddAssign<SInt<A,>>, {
    fn sub_assign(&mut self, rhs: SInt<A,>,) { *self += -rhs }
  }

  impl<'a, A,> SubAssign<&'a SInt<A,>> for SInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn sub_assign(&mut self, rhs: &'a SInt<A,>,) { *self -= rhs.into_vec() }
  }

  impl<'a, A,> SubAssign<&'a mut SInt<A,>> for SInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn sub_assign(&mut self, rhs: &'a mut SInt<A,>,) { *self -= rhs.into_vec() }
  }

  impl SubAssign<isize> for SInt<Vec<u8>,> {
    fn sub_assign(&mut self, rhs: isize,) { *self -= SInt::from(rhs,) }
  }

  impl<A, Rhs,> Sub<Rhs,> for SInt<A,>
    where A: Borrow<[u8]>,
      SInt<Vec<u8>,>: SubAssign<Rhs>,
      Self: IntoVec, {
    type Output = SInt<Vec<u8>,>;

    fn sub(self, rhs: Rhs,) -> Self::Output {
      let mut temp = self.into_vec();

      temp -= rhs; temp
    }
  } 

  impl<A, Rhs,> Sub<Rhs,> for &'_ SInt<A,>
    where A: Borrow<[u8]>,
      SInt<Vec<u8>,>: Sub<Rhs>, {
    type Output = <SInt as Sub<Rhs>>::Output;

    fn sub(self, rhs: Rhs,) -> Self::Output { self.into_vec() - rhs }
  } 

  impl<A, Rhs,> Sub<Rhs,> for &'_ mut SInt<A,>
    where A: Borrow<[u8]>,
      SInt<Vec<u8>,>: Sub<Rhs>, {
    type Output = <SInt as Sub<Rhs>>::Output;

    #[inline]
    fn sub(self, rhs: Rhs,) -> Self::Output { &*self - rhs }
  }

}

mod mul {
  use super::*;

  impl MulAssign<SInt<Vec<u8>,>> for SInt<Vec<u8>,> {
    fn mul_assign(&mut self, mut rhs: SInt<Vec<u8>,>,) {
      let signum = (self.signum() * rhs.signum()) == 1;

      //Clear the sign bits of both values.
      self.0 >>= 1usize;
      rhs.0 >>= 1usize;
      //Perform the multiplication.
      self.0 *= rhs.0;
      //Make space for the sign bit again.
      self.0 <<= 1usize;
      //Set the sign value.
      self.set_sign(signum,);
    }
  }

  impl<'a, A,> MulAssign<&'a SInt<A,>> for SInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn mul_assign(&mut self, rhs: &'a SInt<A,>,) { *self *= rhs.into_vec() }
  }

  impl<'a, A,> MulAssign<&'a mut SInt<A,>> for SInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn mul_assign(&mut self, rhs: &'a mut SInt<A,>,) { *self *= &*rhs }
  }

  impl MulAssign<isize> for SInt<Vec<u8>,> {
    fn mul_assign(&mut self, rhs: isize,) { *self *= SInt::from(rhs,) }
  }

  impl MulAssign<i8> for SInt<Vec<u8>,> {
    fn mul_assign(&mut self, rhs: i8,) { *self *= rhs as isize }
  }

  impl<A, Rhs,> Mul<Rhs> for SInt<A,>
    where A: Borrow<[u8]>,
      SInt<Vec<u8>,>: MulAssign<Rhs>,
      Self: IntoVec, {
    type Output = SInt<Vec<u8>,>;

    fn mul(self, rhs: Rhs,) -> Self::Output {
      let mut temp = self.into_vec();

      temp *= rhs; temp
    }
  }

  impl<A, Rhs,> Mul<Rhs,> for &'_ SInt<A,>
    where A: Borrow<[u8]>,
      SInt<Vec<u8>,>: MulAssign<Rhs>, {
    type Output = <SInt as Mul<Rhs>>::Output;

    fn mul(self, rhs: Rhs,) -> Self::Output { self.into_vec() * rhs }
  } 

  impl<A, Rhs,> Mul<Rhs,> for &'_ mut SInt<A,>
    where A: Borrow<[u8]>,
      SInt<Vec<u8>,>: MulAssign<Rhs>, {
    type Output = <SInt as Mul<Rhs>>::Output;

    #[inline]
    fn mul(self, rhs: Rhs,) -> Self::Output { &*self * rhs }
  }

}

mod div {
  use super::*;

  impl<A,> DivAssign<SInt<A,>> for SInt<Vec<u8>,>
    where A: BorrowMut<[u8]>, {
    fn div_assign(&mut self, rhs: SInt<A,>,) { self.rem(rhs,); }
  }

  impl<'a, A,> DivAssign<&'a SInt<A,>> for SInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn div_assign(&mut self, rhs: &'a SInt<A,>,) { *self /= rhs.into_vec() }
  }

  impl<'a, A,> DivAssign<&'a mut SInt<A,>> for SInt<Vec<u8>,>
    where A: BorrowMut<[u8]>, {
    fn div_assign(&mut self, rhs: &'a mut SInt<A,>,) { *self /= rhs.into_slice_mut() }
  }

  impl DivAssign<isize> for SInt<Vec<u8>,> {
    fn div_assign(&mut self, rhs: isize,) { *self /= SInt::from(rhs,) }
  }

  impl<A, Rhs,> Div<Rhs,> for SInt<A,>
    where A: Borrow<[u8]>,
      SInt<Vec<u8>,>: DivAssign<Rhs>,
      Self: IntoVec, {
    type Output = SInt<Vec<u8>,>;

    fn div(self, rhs: Rhs,) -> Self::Output {
      let mut temp = self.into_vec();
      
      temp /= rhs; temp
    }
  } 

  impl<A, Rhs,> Div<Rhs,> for &'_ SInt<A,>
    where A: Borrow<[u8]>,
      SInt<Vec<u8>,>: DivAssign<Rhs>, {
    type Output = SInt<Vec<u8>,>;

    fn div(self, rhs: Rhs,) -> Self::Output {
      let mut temp = self.into_vec();

      temp /= rhs; temp
    }
  } 

  impl<A, Rhs,> Div<Rhs,> for &'_ mut SInt<A,>
    where A: Borrow<[u8]>,
      SInt<Vec<u8>,>: DivAssign<Rhs>, {
    type Output = SInt<Vec<u8>,>;

    #[inline]
    fn div(self, rhs: Rhs,) -> Self::Output { &*self / rhs }
  }

}

mod rem {
  use super::*;

  impl<'a, A: 'a,> RemAssign<SInt<A,>> for SInt<Vec<u8>,>
    where A: BorrowMut<[u8]>, {
    fn rem_assign(&mut self, rhs: SInt<A,>,) { *self = self.rem(rhs,) }
  }

  impl RemAssign<isize> for SInt<Vec<u8>,> {
    fn rem_assign(&mut self, rhs: isize,) { *self %= SInt::from(rhs,) }
  }

  impl<'a, A,> RemAssign<&'a SInt<A,>> for SInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn rem_assign(&mut self, rhs: &'a SInt<A,>,) { *self %= rhs.into_vec() }
  }

  impl<'a, A,> RemAssign<&'a mut SInt<A,>> for SInt<Vec<u8>,>
    where A: BorrowMut<[u8]>, {
    fn rem_assign(&mut self, rhs: &'a mut SInt<A,>,) { *self %= rhs.into_slice_mut() }
  }

  impl<A, Rhs,> Rem<Rhs> for SInt<A,>
    where A: Borrow<[u8]>,
      SInt<Vec<u8>,>: RemAssign<Rhs>,
      Self: IntoVec, {
    type Output = SInt<Vec<u8>,>;

    fn rem(self, rhs: Rhs,) -> Self::Output {
      let mut temp = self.into_vec();
      
      temp %= rhs; temp
    }
  }

  impl<A, Rhs,> Rem<Rhs> for &'_ SInt<A,>
    where A: Borrow<[u8]>,
      SInt<Vec<u8>,>: RemAssign<Rhs>, {
    type Output = SInt<Vec<u8>,>;

    fn rem(self, rhs: Rhs,) -> Self::Output {
      let mut temp = self.into_vec();

      temp %= rhs; temp
    }
  }

  impl<A, Rhs,> Rem<Rhs> for &'_ mut SInt<A,>
    where A: Borrow<[u8]>,
      SInt<Vec<u8>,>: RemAssign<Rhs>, {
    type Output = SInt<Vec<u8>,>;

    #[inline]
    fn rem(self, rhs: Rhs,) -> Self::Output { &*self % rhs }
  }

}

impl From<i8> for SInt<Vec<u8>,> {
  fn from(from: i8,) -> Self {
    let mut temp = SInt::from(UInt::from(from.abs() as u8,),);

    if from < 0 { temp = -temp }

    temp
  }
}

impl From<i16> for SInt<Vec<u8>,> {
  fn from(from: i16,) -> Self {
    let mut temp = SInt::from(UInt::from(from.abs() as u16,),);

    if from < 0 { temp = -temp }

    temp
  }
}

impl From<i32> for SInt<Vec<u8>,> {
  fn from(from: i32,) -> Self {
    let mut temp = SInt::from(UInt::from(from.abs() as u32,),);

    if from < 0 { temp = -temp }

    temp
  }
}

impl From<i64> for SInt<Vec<u8>,> {
  fn from(from: i64,) -> Self {
    let mut temp = SInt::from(UInt::from(from.abs() as u64,),);

    if from < 0 { temp = -temp }

    temp
  }
}

impl From<i128> for SInt<Vec<u8>,> {
  fn from(from: i128,) -> Self {
    let mut temp = SInt::from(UInt::from(from.abs() as u128,),);

    if from < 0 { temp = -temp }

    temp
  }
}

impl From<isize> for SInt<Vec<u8>,> {
  fn from(from: isize,) -> Self {
    let mut temp = SInt::from(UInt::from(from.abs() as usize,),);

    if from < 0 { temp = -temp }

    temp
  }
}

impl From<Vec<u8>> for SInt<Vec<u8>,> {
  #[inline]
  fn from(from: Vec<u8>,) -> Self { Self::new(from,) }
}

impl<'a,> From<&'a [u8]> for SInt<Vec<u8>,> {
  fn from(from: &'a [u8],) -> Self { SInt::new(from.into(),) }
}

impl<'a,> From<&'a mut [u8]> for SInt<Vec<u8>,> {
  fn from(from: &'a mut [u8],) -> Self { SInt::new(from.into(),) }
}

impl From<Box<[u8]>> for SInt<Vec<u8>,> {
  fn from(from: Box<[u8]>,) -> Self { SInt::new(from.into(),) }
}

impl From<UInt<Vec<u8>,>> for SInt<Vec<u8>,> {
  #[inline]
  fn from(from: UInt<Vec<u8>,>,) -> Self { SInt(from << 1usize,) }
}

impl FromStr for SInt<Vec<u8>,> {
  type Err = ParseIntError;

  fn from_str(s: &str,) -> Result<Self, Self::Err> {
    //Strip the prefix.
    let sign = s.strip_prefix('-',);
    let s = sign.unwrap_or(s,);
    //Get the sign of the int.
    let sign = sign.is_none();

    //Parse the int and set the sign.
    UInt::from_str(s,).map(move |n,| {
      let mut temp = SInt::from(n,);
      temp.set_sign(sign,);

      temp
    },)
  }
}

impl<A,> FromIterator<A> for SInt<Vec<u8>,>
  where A: Into<u8>, {
  fn from_iter<I,>(iter: I,) -> Self
    where I: IntoIterator<Item = A>, {
    Self::new(iter.into_iter().map(A::into,).collect(),)
  }
}

impl<A,> fmt::Display for SInt<A,>
  where A: Borrow<[u8]>, {
  fn fmt(&self, fmt: &mut fmt::Formatter,) -> fmt::Result {
    use crate::uint::IntoVec;
    use core::fmt::Write;

    //Get the sign.
    let neg = self.signum() == -1;

    //Write the sign.
    if neg { fmt.write_char('-',)? }
    //Write the number.
    write!(fmt, "{}", self.0.into_vec() >> 1usize,)
  }
}

impl<A,> fmt::Debug for SInt<A,>
  where A: Borrow<[u8]>, {
  #[inline]
  fn fmt(&self, fmt: &mut fmt::Formatter,) -> fmt::Result { write!(fmt, "{}", *self,) }
}

impl<A,> fmt::Binary for SInt<A,>
  where A: Borrow<[u8]>, {
  #[inline]
  fn fmt(&self, fmt: &mut fmt::Formatter,) -> fmt::Result { self.0.fmt(fmt,) }
}

impl<A,> fmt::LowerHex for SInt<A,>
  where A: Borrow<[u8]>, {
  #[inline]
  fn fmt(&self, fmt: &mut fmt::Formatter,) -> fmt::Result { self.0.fmt(fmt,) }
}

impl<A,> fmt::UpperHex for SInt<A,>
  where A: Borrow<[u8]>, {
  #[inline]
  fn fmt(&self, fmt: &mut fmt::Formatter,) -> fmt::Result { self.0.fmt(fmt,) }
}

impl From<SInt<Vec<u8>,>> for Vec<u8> {
  #[inline]
  fn from(from: SInt<Vec<u8>,>,) -> Self { from.into_inner() }
}

impl TryFrom<SInt<Vec<u8>,>> for isize {
  type Error = FromIntError<SInt<Vec<u8>,>,>;

  fn try_from(from: SInt<Vec<u8>,>,) -> Result<Self, Self::Error> {
    //Record the signum.
    let sign = from.signum();

    //Convert the value into an unsigned and then restore the sign on the output.
    usize::try_from(from.0 >> 1usize,).map(move |n,| n as isize * sign as isize,)
    //Restore the `SInt` value on error.
    .map_err(move |FromIntError(n,),| {
      let mut temp = SInt::from(n,);
      temp.set_sign(sign == 1,);

      FromIntError(temp,)
    },)
  }
}

impl TryFrom<SInt<Vec<u8>,>> for i8 {
  type Error = FromIntError<SInt<Vec<u8>,>,>;

  fn try_from(from: SInt<Vec<u8>,>,) -> Result<Self, Self::Error> {
    //Record the signum.
    let sign = from.signum();

    //Convert the value into an unsigned and then restore the sign on the output.
    u8::try_from(from.0 >> 1usize,).map(move |n,| n as i8 * sign as i8,)
    //Restore the `SInt` value on error.
    .map_err(move |FromIntError(n,),| {
      let mut temp = SInt::from(n,);
      temp.set_sign(sign == 1,);

      FromIntError(temp,)
    },)
  }
}

impl TryFrom<SInt<Vec<u8>,>> for i16 {
  type Error = FromIntError<SInt<Vec<u8>,>,>;

  fn try_from(from: SInt<Vec<u8>,>,) -> Result<Self, Self::Error> {
    //Record the signum.
    let sign = from.signum();

    //Convert the value into an unsigned and then restore the sign on the output.
    u16::try_from(from.0 >> 1usize,).map(move |n,| n as i16 * sign as i16,)
    //Restore the `SInt` value on error.
    .map_err(move |FromIntError(n,),| {
      let mut temp = SInt::from(n,);
      temp.set_sign(sign == 1,);

      FromIntError(temp,)
    },)
  }
}

impl TryFrom<SInt<Vec<u8>,>> for i32 {
  type Error = FromIntError<SInt<Vec<u8>,>,>;

  fn try_from(from: SInt<Vec<u8>,>,) -> Result<Self, Self::Error> {
    //Record the signum.
    let sign = from.signum();

    //Convert the value into an unsigned and then restore the sign on the output.
    u32::try_from(from.0 >> 1usize,).map(move |n,| n as i32 * sign as i32,)
    //Restore the `SInt` value on error.
    .map_err(move |FromIntError(n,),| {
      let mut temp = SInt::from(n,);
      temp.set_sign(sign == 1,);

      FromIntError(temp,)
    },)
  }
}

impl TryFrom<SInt<Vec<u8>,>> for i64 {
  type Error = FromIntError<SInt<Vec<u8>,>,>;

  fn try_from(from: SInt<Vec<u8>,>,) -> Result<Self, Self::Error> {
    //Record the signum.
    let sign = from.signum();

    //Convert the value into an unsigned and then restore the sign on the output.
    u64::try_from(from.0 >> 1usize,).map(move |n,| n as i64 * sign as i64,)
    //Restore the `SInt` value on error.
    .map_err(move |FromIntError(n,),| {
      let mut temp = SInt::from(n,);
      temp.set_sign(sign == 1,);

      FromIntError(temp,)
    },)
  }
}

impl TryFrom<SInt<Vec<u8>,>> for i128 {
  type Error = FromIntError<SInt<Vec<u8>,>,>;

  fn try_from(from: SInt<Vec<u8>,>,) -> Result<Self, Self::Error> {
    //Record the signum.
    let sign = from.signum();

    //Convert the value into an unsigned and then restore the sign on the output.
    u128::try_from(from.0 >> 1usize,).map(move |n,| n as i128 * sign as i128,)
    //Restore the `SInt` value on error.
    .map_err(move |FromIntError(n,),| {
      let mut temp = SInt::from(n,);
      temp.set_sign(sign == 1,);

      FromIntError(temp,)
    },)
  }
}
