//! Author --- DMorgan  
//! Last Moddified --- 2019-01-03

use crate::{SInt, FromIntError, IntErrorKind, ParseIntError, private::Sealed,};
use alloc::{vec::Vec, boxed::Box,};
use core::{
  fmt,
  ops::{
    Rem, RemAssign,
    Shl, ShlAssign,
    Shr, ShrAssign,
    Add, AddAssign,
    Sub, SubAssign,
    Mul, MulAssign,
    Div, DivAssign,
    BitAnd, BitAndAssign,
    BitOr, BitOrAssign,
    BitXor, BitXorAssign,
  },
  num::NonZeroUsize,
  cmp::Ordering,
  convert::TryFrom,
  str::FromStr,
  borrow::{Borrow, BorrowMut,},
  iter::FromIterator,
};

mod tests;
mod serde;

//The VLQ encoding I am using treats a slice as a little endian unsigned integer.

/// An unsigned integer.
#[derive(Clone, Copy, Hash,)]
pub struct UInt<B = Vec<u8>,>(pub(crate) B,)
  where B: Borrow<[u8]>,;

impl<'a,> UInt<&'a mut [u8],> {
  /// Converts the `le` slice bytes into `UInt` bytes.
  /// 
  /// # Params
  /// 
  /// bytes --- The `le` bytes to convert.
  pub(crate) fn bytes_to_uint(bytes: &'a mut [u8],) -> &'a mut [u8] {
    //The high zero bytes being ignored.
    let ignored = bytes.iter().cloned().rev()
      .take_while(|&b,| b == 0,).count();

    //Ignore the high zero bytes.
    let len = bytes.len() - ignored;
    &mut bytes[..len]
  }
  /// Performs half addition between the `le` slices.
  /// 
  /// `rhs` must be shorter or equal to `self` in length or the data will be corrupted.
  /// 
  /// Returns `true` if `self` was overflown.
  pub(crate) unsafe fn half_add_bytes(&mut self, rhs: &[u8],) -> bool {
    //Shortcut for zero.
    if rhs.is_empty() == true { return false }

    //Iterate over the right hand bytes.
    let rhs_bytes = rhs.iter().copied();
    //Iterate over the byte pairs.
    let pairs = self.0.iter_mut().zip(rhs_bytes,);
    //Calculate the overflow from the pairs.
    let overflow = pairs.fold(false, |over, (byte, rhs,),| {
      //Add the bytes pairs.
      let (v, check1,) = byte.overflowing_add(rhs,);
      //Add the overflow and the offset from `rhs`.
      let (v, check2,) = v.overflowing_add(over as u8,);

      //Update the byte.
      *byte = v;

      //Return the new overflow.
      check1 || check2
    },);

    //Carry the overflow.
    overflow && self.0[rhs.len()..].iter_mut().all(|byte,| {
      //Update the byte.
      let (v, check,) = byte.overflowing_add(1,);
      *byte = v;

      check
    },)
  }
  /// Performs half subtraction between the `le` slices.
  /// 
  /// `rhs` must be less or equal to `self` in value or the data will be corrupted.
  /// 
  /// Returns `true` if `self` was underflown.
  pub(crate) unsafe fn half_sub_bytes(&mut self, rhs: &[u8],) -> Option<NonZeroUsize> {
    //Iterate over the right hand bytes in reverse order.
    let bytes = rhs.iter().copied().enumerate().rev();
    //Perform subtraction.
    for (index, byte,) in bytes {
      //Subtract the byte.
      let (v, check,) = self.0[index].overflowing_sub(byte,);
      self.0[index] = v;

      if check {
        //Underflow occoured, carry the borrow.
        self.0[(index + 1)..].iter_mut().all(|byte,| {
          //Subtract the borrow.
          let (v, check,) = byte.overflowing_sub(1,);
          *byte = v;

          check
        },);
      }
    }

    //Calculate the underflow.
    let underflow = self.0.iter().rev()
      .take_while(|&&b,| b == 0,).count();

    NonZeroUsize::new(underflow,)
  }
}

impl UInt<[u8; 1],> {
  /// A unit `UInt`.
  pub const ONE: Self = UInt([1,],);
}

impl UInt<Vec<u8>,> {
  /// A zero `UInt`.
  pub const ZERO: Self = UInt(Vec::new(),);

  /// Creates a new `UInt` from a `Vec` of little endian bytes.
  /// 
  /// # Params
  /// 
  /// le_bytes --- The little endian bytes to encode.  
  pub(crate) fn new(mut le_bytes: Vec<u8>,) -> Self {
    //Convert the bytes.
    let len = UInt::bytes_to_uint(&mut le_bytes,).len();
    //Truncate the bytes.
    le_bytes.truncate(len,);

    UInt(le_bytes,)
  }
  /// Calculates the previous power of two less than or equal too `self`.
  /// 
  /// A value of zero remains at zero.
  pub fn prev_power_of_two(mut self,) -> Self {
    //Calculate the previous power of two.
    if let Some((last, rest,)) = self.0.split_last_mut() {
      //Get the leading byte.

      //Zero the rest of the bytes.
      for b in rest { *b = 0 }

      //Calculate the previous power of two.
      *last = ((*last >> 1) + 1).next_power_of_two();
    }

    self
  }
  /// Calculates the next power of two greater than `self`.
  pub fn next_power_of_two(mut self,) -> Self {
    //`0` maps to `1`.
    if self == UInt::ZERO { self.0.push(1,); self }
    //Calculating the next power of two is just the previous power of two doubled.
    else { self.prev_power_of_two() << 1u8 }
  }
  /// Calculates the `remainder` after division by `rhs` and mutates `self` into the
  /// `quotient`.
  /// 
  /// # Params
  /// 
  /// divisor --- The right hand side of the division.  
  pub fn rem<A,>(&mut self, divisor: &UInt<A,>,) -> UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    use core::{iter, mem,};

    let rhs = divisor.into_slice();
    //Shortcut for 1.
    if rhs.0 == &[1] { return UInt::ZERO.into_vec() }
    //If the `lhs` value is smaller than `rhs` it cannot be divided.
    else if *self < rhs { return mem::replace(self, UInt::ZERO.into_vec(),) }

    assert!(&rhs != &UInt::ZERO, "`lhs / rhs` requires `rhs` be non zero",);

    //The number of low zero bytes common to both numbers and therefore irrelevant during division.
    let trailing_zeros = {
      let lhs_trailing_zeros = self.0.iter().take_while(|&&b,| b == 0,).count();
      let rhs_trailing_zeros = rhs.0.iter().take_while(|&&b,| b == 0,).count();

      usize::min(lhs_trailing_zeros, rhs_trailing_zeros,)
    };
    //Trim the trailing zeros from `rhs`.
    let rhs = UInt(&rhs.0[trailing_zeros..],);
    //Trim the trailing zeros from `self`.
    self.0.drain(..trailing_zeros,);

    //The cursor used to modify `self` by multiples of `rhs`.
    let mut cursor = rhs.into_vec();
    //A complement to `cursor` indicating how many multiples of `rhs` it represents.
    //`multiple` is shifted to account for the removal of trailing zeros from both sided.
    let mut multiple = UInt::ONE.into_vec();
    //The reservoir of state from `self` to remove instances of `rhs` from until its the remainder.
    let mut remainder = mem::replace(self, UInt::ZERO,);
    //The difference in byte length between `remainder` and `cursor`.
    let shift = remainder.0.len() - cursor.0.len();

    //Shift `cursor` to start at the same byte length as `remainder`.
    cursor.0.splice(..0, iter::repeat(0,).take(shift,),);
    multiple.0.splice(..0, iter::repeat(0,).take(shift,),);
    //Count the instances of `rhs` in `remainder`.
    loop {
      //Remove instances of `rhs` from `remainder`.

      let cmp = cursor.cmp(&remainder,);
      //If `cursor` is greater than remainder then there are less than `multiple` instances to count.
      if cmp == Ordering::Greater {
        //`cursor` is too big, shrink it.

        //Calculate the length difference between `remainder` and `cursor`.
        let shift = NonZeroUsize::new(cursor.0.len() - remainder.0.len(),);
        //Check if shifting the cursor will corrupt it by making it smaller than `rhs` which it represents.
        //Also be sure not to underflow multiple.
        if let Some(shift) = shift.filter(|shift,| shift.get() + rhs.0.len() <= cursor.0.len() && multiple > 255,) {
          //There is a gap to shift across.

          let shift = shift.get();
          //Remove the trailing zero bytes.
          cursor.0.drain(..shift,);
          multiple.0.drain(..shift,);
        //Check if a bit shift will underflow multiple.
        } else if multiple > 1 {
          //There's still instances to count.

          //Half the cursor.
          cursor >>= 1usize; multiple >>= 1usize;
        //There are no more instances to count.
        } else { break }

        continue
      }

      //Update the `self` with the instances of `rhs` seen.
      *self += &multiple;
      //Remove the instances.
      remainder -= &cursor;

      //There was exactly `multiple` instances of `cursor`; `remainder` is now zero.
      if cmp == Ordering::Equal { return remainder }
    }

    //Add back in the trailing zeros we had removed for quick division.
    remainder.0.splice(..0, iter::repeat(0,).take(trailing_zeros,),);
    remainder
  }
  /// Performs full addition between the VLQs.
  /// 
  /// `rhs` must be shorter or equal to `self` or the data will be corrupted.
  unsafe fn add_bytes(&mut self, rhs: &[u8],) {
    //Perform addition and check for overflow.
    let overflow = self.into_slice_mut().half_add_bytes(rhs,);
    //If overflow occoured push an additional byte.
    if overflow { self.0.push(1,) }
  }
  /// Performs full subtraction between the VLQs.
  /// 
  /// `rhs` must be less or equal to `self` or the data will be corrupted.
  unsafe fn sub_bytes(&mut self, rhs: &[u8],) {
    //Perform the subtraction.
    let underflow = self.into_slice_mut().half_sub_bytes(rhs,);
    //If underflow occoured, truncate the bytes.
    if let Some(underflow) = underflow { self.0.truncate(self.0.len() - underflow.get(),) }
  }
  /// Performs full multiplication between the VLQs.
  /// 
  /// `rhs` is optimal when less or equal to `self`.
  fn mul_bytes(&mut self, rhs: UInt<&[u8],>,) {
    use core::mem;

    //Multiplying by zero.
    if self.0.is_empty() { return }
    if rhs.0.is_empty() { return *self = UInt::ZERO }
    //Multiplying by one.
    else if rhs.0 == &[1] { return }

    //The number of instances of each shifted version of `self` to be accumulated.
    let mut quantity = rhs.0.iter().copied();
    //The shifted instance of `self` to add instances of to the sum.
    //Also clear `self` to be the accumulator.
    let mut shifted_instance = mem::replace(self, UInt::ZERO,);

    //Accumulate quantities of each shift to `self`.
    if let Some(instances) = quantity.next() { *self += &shifted_instance * instances }
    for instances in quantity {
      shifted_instance <<= 8usize;
      *self += &shifted_instance * instances;
    }
  }
}

impl<A,> UInt<A,>
  where A: Borrow<[u8]>, {
  /// Borrows the bytes within this `UInt` as `slice` backed instance.
  #[inline]
  pub fn into_slice<'a,>(&'a self,) -> UInt<&'a [u8],> { UInt(self.0.borrow(),) }
}

impl<A,> UInt<A,>
  where A: BorrowMut<[u8]>, {
  /// Converts the `UInt` bytes into a little endian `slice` of bytes.
  #[inline]
  pub fn into_inner(self,) -> A { self.0 }
  /// Borrows the bytes within this `UInt` as mutable `slice` backed instance.
  #[inline]
  pub fn into_slice_mut<'a,>(&'a mut self,) -> UInt<&'a mut [u8],> { UInt(self.0.borrow_mut(),) }
}

pub use self::into_vec::*;

mod into_vec {
  use super::*;

  /// Used to get a mutable version of a `UInt`.
  pub trait IntoVec: Sealed {
    /// Creates a `UInt` backed by a `Vec` which has the same value as this `UInt`.
    fn into_vec(self,) -> UInt<Vec<u8>,>;
  }

  impl Sealed for UInt<Vec<u8>,> {}

  impl IntoVec for UInt<Vec<u8>,> {
    #[inline]
    fn into_vec(self,) -> UInt<Vec<u8>,> { self }
  }

  impl Sealed for UInt<&'_ [u8],> {}

  impl IntoVec for UInt<&'_ [u8],> {
    #[inline]
    fn into_vec(self,) -> UInt<Vec<u8>,> { UInt::from(self.0,) }
  }

  impl Sealed for UInt<&'_ mut [u8],> {}

  impl IntoVec for UInt<&'_ mut [u8],> {
    #[inline]
    fn into_vec(self,) -> UInt<Vec<u8>,> { UInt::from(self.0,) }
  }

  impl<A,> Sealed for &'_ UInt<A,>
    where A: Borrow<[u8]>, {}

  impl<A,> IntoVec for &'_ UInt<A,>
    where A: Borrow<[u8]>, {
    #[inline]
    fn into_vec(self,) -> UInt<Vec<u8>,> { UInt(self.0.borrow().into(),) }
  }

  impl<A,> Sealed for &'_ mut UInt<A,>
    where A: Borrow<[u8]>, {}

  impl<A,> IntoVec for &'_ mut UInt<A,>
    where A: Borrow<[u8]>, {
    #[inline]
    fn into_vec(self,) -> UInt<Vec<u8>,> { UInt(self.0.borrow().into(),) }
  }

}

mod cmp {
  use super::*;

  impl<A, B,> PartialEq<UInt<B,>> for UInt<A,>
    where A: Borrow<[u8]>,
      B: Borrow<[u8]>, {
    #[inline]
    fn eq(&self, rhs: &UInt<B,>,) -> bool { self.0.borrow() == rhs.0.borrow() }
  }

  impl<A,> Eq for UInt<A,>
    where A: Borrow<[u8]>, {}

  impl<A,> PartialEq<usize> for UInt<A,>
    where A: Borrow<[u8]>, {
    fn eq(&self, rhs: &usize,) -> bool { *self == UInt::from(*rhs,) }
  }

  impl<A, B,> PartialOrd<UInt<B,>> for UInt<A,>
    where A: Borrow<[u8]>,
      B: Borrow<[u8]>, {
    fn partial_cmp(&self, rhs: &UInt<B,>,) -> Option<Ordering> { Some(self.into_slice().cmp(&rhs.into_slice(),)) }
  }

  impl<A,> Ord for UInt<A,>
    where A: Eq + Borrow<[u8]>, {
    fn cmp(&self, rhs: &Self,) -> Ordering {
      let lhs = self.0.borrow();
      let rhs = rhs.0.borrow();
      //The longest value has a greater magnituid.
      let cmp = lhs.len().cmp(&rhs.len(),);
      if cmp != Ordering::Equal { return cmp }

      let lhs = lhs.iter().copied().rev();
      let rhs = rhs.iter().rev();

      //Compare from the highest bytes first.
      lhs.zip(rhs,).map(|(a, b,),| a.cmp(b,),)
      //Filter out equal bytes.
      .filter(|&c,| c != Ordering::Equal,)
      //Unwrap the first ordering.
      .next().unwrap_or(Ordering::Equal,)
    }
  }

  impl<A,> PartialOrd<usize> for UInt<A,>
    where A: Borrow<[u8]>, {
    fn partial_cmp(&self, rhs: &usize,) -> Option<Ordering> { self.partial_cmp(&UInt::from(*rhs,),) }
  }

}

mod add {
  use super::*;

  impl AddAssign<UInt<Vec<u8>,>> for UInt<Vec<u8>,> {
    fn add_assign(&mut self, mut rhs: UInt<Vec<u8>,>,) {
      use core::mem;

      //Find the longer VLQ.
      let len_cmp = self.0.len().cmp(&rhs.0.len(),);
      //Ensure `self` is the longer of the two VLQs.
      if len_cmp == Ordering::Less { mem::swap(self, &mut rhs,) }

      unsafe { self.add_bytes(&rhs.0,) }
    }
  }

  impl<'a, A,> AddAssign<&'a UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn add_assign(&mut self, rhs: &'a UInt<A,>,) {
      use core::mem;

      let rhs = rhs.0.borrow();
      //Find the longer VLQ.
      let len_cmp = self.0.len().cmp(&rhs.len(),);
      //Ensure `self` is the longer of the two VLQs and perform addition.
      if len_cmp == Ordering::Less {
        //`self` is shorter than `rhs`.
        let mut rhs = UInt(rhs,).into_vec();

        mem::swap(self, &mut rhs,);
        unsafe { self.add_bytes(&rhs.0,); }
      //Their lengths are no issue.
      } else { unsafe { self.add_bytes(&rhs,) } };
    }
  }

  impl<'a, A,> AddAssign<&'a mut UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn add_assign(&mut self, rhs: &'a mut UInt<A,>,) { *self += &*rhs }
  }

  impl AddAssign<u8> for UInt<Vec<u8>,> {
    fn add_assign(&mut self, rhs: u8,) { *self += &UInt::from(rhs,) }
  }

  impl AddAssign<usize> for UInt<Vec<u8>,> {
    fn add_assign(&mut self, rhs: usize,) { *self += &UInt::from(rhs,) }
  }

  impl<Rhs,> Add<Rhs,> for UInt<Vec<u8>,>
    where UInt<Vec<u8>,>: AddAssign<Rhs>, {
    type Output = UInt<Vec<u8>,>;

    fn add(mut self, rhs: Rhs,) -> Self::Output { self += rhs; self }
  }

  impl<A, Rhs,> Add<Rhs,> for &'_ UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: Add<Rhs>, {
    type Output = <UInt as Add<Rhs>>::Output;

    fn add(self, rhs: Rhs,) -> Self::Output { self.into_vec() + rhs }
  } 

  impl<A, Rhs,> Add<Rhs,> for &'_ mut UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: Add<Rhs>, {
    type Output = <UInt as Add<Rhs>>::Output;

    #[inline]
    fn add(self, rhs: Rhs,) -> Self::Output { &*self + rhs }
  }

}

mod sub {
  use super::*;

  impl<A,> SubAssign<UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn sub_assign(&mut self, rhs: UInt<A,>,) {
      let rhs = rhs.into_slice();

      assert!(*self >= rhs, "`lhs - rhs` requires `rhs` be smaller than `lhs`",);

      unsafe { self.sub_bytes(rhs.0,) }
    }
  }

  impl<'a, A,> SubAssign<&'a UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn sub_assign(&mut self, rhs: &'a UInt<A,>,) { *self -= rhs.into_slice() }
  }

  impl<'a, A,> SubAssign<&'a mut UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn sub_assign(&mut self, rhs: &'a mut UInt<A,>,) { *self -= &*rhs }
  }

  impl SubAssign<u8> for UInt<Vec<u8>,> {
    fn sub_assign(&mut self, rhs: u8,) { *self -= UInt::from(rhs,) }
  }

  impl SubAssign<usize> for UInt<Vec<u8>,> {
    fn sub_assign(&mut self, rhs: usize,) { *self -= UInt::from(rhs,) }
  }

  impl<Rhs,> Sub<Rhs,> for UInt<Vec<u8>,>
    where UInt<Vec<u8>,>: SubAssign<Rhs>,
      Self: IntoVec, {
    type Output = UInt<Vec<u8>,>;

    fn sub(mut self, rhs: Rhs,) -> Self::Output {
      self -= rhs; self
    }
  } 

  impl<A, Rhs,> Sub<Rhs,> for &'_ UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: Sub<Rhs>, {
    type Output = <UInt as Sub<Rhs>>::Output;

    fn sub(self, rhs: Rhs,) -> Self::Output { self.into_vec() - rhs }
  } 

  impl<A, Rhs,> Sub<Rhs,> for &'_ mut UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: Sub<Rhs>, {
    type Output = <UInt as Sub<Rhs>>::Output;

    #[inline]
    fn sub(self, rhs: Rhs,) -> Self::Output { &*self - rhs }
  }

}

mod mul {
  use super::*;

  impl<A,> MulAssign<UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn mul_assign(&mut self, rhs: UInt<A,>,) { self.mul_bytes(rhs.into_slice(),) }
  }

  impl<'a, A,> MulAssign<&'a UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn mul_assign(&mut self, rhs: &'a UInt<A,>,) { *self *= rhs.into_slice() }
  }

  impl<'a, A,> MulAssign<&'a mut UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn mul_assign(&mut self, rhs: &'a mut UInt<A,>,) { *self *= &*rhs }
  }

  impl MulAssign<usize> for UInt<Vec<u8>,> {
    fn mul_assign(&mut self, rhs: usize,) { *self *= UInt::from(rhs,) }
  }

  impl MulAssign<u8> for UInt<Vec<u8>,> {
    fn mul_assign(&mut self, rhs: u8,) {
      //Multiplication by 0 or 1 shortcut.
      if rhs == 0 { return *self = UInt::ZERO }
      else if rhs == 1 { return }

      //Expand the `rhs` for the multiplication.
      let rhs = rhs as u16;

      //Multiply all of the bytes and return the overflow.
      let overflow = self.0.iter_mut().fold(0u8, move |over, byte,| {
        //Multiply the byte and `rhs` and convert them to bytes.
        let [v, high,] = (*byte as u16 * rhs).to_le_bytes();
        //Carry in the overflow from the last multiplication.
        let (v, check,) = v.overflowing_add(over,);
        //Update the byte.
        *byte = v;

        //Update the overflow from this multiplication.
        high + check as u8
      },);
      //Extend the value with the overflow.
      if overflow > 0 { self.0.push(overflow,) }
    }
  }

  impl<Rhs,> Mul<Rhs> for UInt<Vec<u8>,>
    where UInt<Vec<u8>,>: MulAssign<Rhs>, {
    type Output = UInt<Vec<u8>,>;

    fn mul(mut self, rhs: Rhs,) -> Self::Output {
      self *= rhs; self
    }
  }

  impl<A, Rhs,> Mul<Rhs,> for &'_ UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: MulAssign<Rhs>, {
    type Output = <UInt as Mul<Rhs>>::Output;

    fn mul(self, rhs: Rhs,) -> Self::Output { self.into_vec() * rhs }
  } 

  impl<A, Rhs,> Mul<Rhs,> for &'_ mut UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: MulAssign<Rhs>, {
    type Output = <UInt as Mul<Rhs>>::Output;

    #[inline]
    fn mul(self, rhs: Rhs,) -> Self::Output { &*self * rhs }
  }

}

mod div {
  use super::*;

  impl<A,> DivAssign<UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn div_assign(&mut self, rhs: UInt<A,>,) { self.rem(&rhs,); }
  }

  impl<'a, A,> DivAssign<&'a UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn div_assign(&mut self, rhs: &'a UInt<A,>,) { *self /= rhs.into_slice() }
  }

  impl<'a, A,> DivAssign<&'a mut UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn div_assign(&mut self, rhs: &'a mut UInt<A,>,) { *self /= &*rhs }
  }

  impl DivAssign<u8> for UInt<Vec<u8>,> {
    fn div_assign(&mut self, rhs: u8,) { *self /= UInt::from(rhs,) }
  }

  impl DivAssign<usize> for UInt<Vec<u8>,> {
    fn div_assign(&mut self, rhs: usize,) { *self /= UInt::from(rhs,) }
  }

  impl<Rhs,> Div<Rhs,> for UInt<Vec<u8>,>
    where UInt<Vec<u8>,>: DivAssign<Rhs>, {
    type Output = UInt<Vec<u8>,>;

    fn div(mut self, rhs: Rhs,) -> Self::Output { self /= rhs; self }
  } 

  impl<A, Rhs,> Div<Rhs,> for &'_ UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: DivAssign<Rhs>, {
    type Output = UInt<Vec<u8>,>;

    fn div(self, rhs: Rhs,) -> Self::Output { self.into_vec() / rhs }
  } 

  impl<A, Rhs,> Div<Rhs,> for &'_ mut UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: DivAssign<Rhs>, {
    type Output = UInt<Vec<u8>,>;

    #[inline]
    fn div(self, rhs: Rhs,) -> Self::Output { &*self / rhs }
  }

}

mod rem {
  use super::*;

  impl<'a, A: 'a,> RemAssign<UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn rem_assign(&mut self, rhs: UInt<A,>,) { *self = self.rem(&rhs,) }
  }

  impl RemAssign<u8> for UInt<Vec<u8>,> {
    fn rem_assign(&mut self, rhs: u8,) { *self %= UInt::from(rhs,) }
  }

  impl RemAssign<usize> for UInt<Vec<u8>,> {
    fn rem_assign(&mut self, rhs: usize,) { *self %= UInt::from(rhs,) }
  }

  impl<'a, A,> RemAssign<&'a UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn rem_assign(&mut self, rhs: &'a UInt<A,>,) { *self %= rhs.into_slice() }
  }

  impl<'a, A,> RemAssign<&'a mut UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn rem_assign(&mut self, rhs: &'a mut UInt<A,>,) { *self %= rhs.into_slice() }
  }

  impl<Rhs,> Rem<Rhs> for UInt<Vec<u8>,>
    where UInt<Vec<u8>,>: RemAssign<Rhs>, {
    type Output = UInt<Vec<u8>,>;

    fn rem(mut self, rhs: Rhs,) -> Self::Output { self %= rhs; self }
  }

  impl<A, Rhs,> Rem<Rhs> for &'_ UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: RemAssign<Rhs>, {
    type Output = UInt<Vec<u8>,>;

    fn rem(self, rhs: Rhs,) -> Self::Output { self.into_vec() % rhs }
  }

  impl<A, Rhs,> Rem<Rhs> for &'_ mut UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: RemAssign<Rhs>, {
    type Output = UInt<Vec<u8>,>;

    #[inline]
    fn rem(self, rhs: Rhs,) -> Self::Output { &*self % rhs }
  }

}

mod shl {
  use super::*;

  impl ShlAssign<usize> for UInt<Vec<u8>,> {
    fn shl_assign(&mut self, rhs: usize,) {
      use bitio::Bits;
      use core::iter;

      //Shifting zero or by zero has no effect.
      if rhs == 0 || *self == UInt::ZERO { return }

      //Calculate the number of full bytes which will be shifted in.
      let full_bytes = rhs / 8;
      //Calculate the number of trailing zero bits which will be shifted in.
      let trailing_bits = Bits::try_from((rhs % 8) as u8,).ok();

      //Check the final length will be valid.
      debug_assert!(
        (full_bytes + trailing_bits.is_some() as usize)
        .checked_add(self.0.len(),).is_some(),
        "`lhs << rhs` overflowed the buffer",
      );

      //Shift all of the bytes.
      if let Some(trailing_bits) = trailing_bits {
        //Shift all of the bytes and return the bits shifted out.
        let overflow = self.0.iter_mut().fold(0u8, move |mut buf, byte,| {
          //Rotate the bits being shifted out into the low bits.
          *byte = byte.rotate_left(trailing_bits as u32,);

          //Mix the low bits with the bits in the buffer.
          *byte ^= buf;
          //Replace the bits in the buffer with the low bits of the byte.
          buf ^= *byte & trailing_bits.mask();
          //Cancel out the original low bits of the byte.
          *byte ^= buf;

          buf
        },);
        //Append the new high byte.
        if overflow > 0 { self.0.push(overflow,) }
      }

      //Insert all of the full bytes.
      self.0.splice(..0, iter::repeat(0,).take(full_bytes,),);
    }
  }

  impl ShlAssign<u8> for UInt<Vec<u8>,> {
    fn shl_assign(&mut self, rhs: u8,) { *self <<= rhs as usize }
  }

  impl<Rhs,> Shl<Rhs> for UInt<Vec<u8>,>
    where UInt<Vec<u8>,>: ShlAssign<Rhs>, {
    type Output = UInt<Vec<u8>,>;

    fn shl(mut self, rhs: Rhs,) -> Self::Output { self <<= rhs; self }
  }

  impl<A, Rhs,> Shl<Rhs> for &'_ UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: ShlAssign<Rhs>, {
    type Output = UInt<Vec<u8>,>;

    fn shl(self, rhs: Rhs,) -> Self::Output { self.into_vec() << rhs }
  }

  impl<A, Rhs,> Shl<Rhs> for &'_ mut UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: ShlAssign<Rhs>, {
    type Output = UInt<Vec<u8>,>;

    #[inline]
    fn shl(self, rhs: Rhs,) -> Self::Output { &*self << rhs }
  }

}

mod shr {
  use super::*;

  impl ShrAssign<usize> for UInt<Vec<u8>,> {
    fn shr_assign(&mut self, rhs: usize,) {
      use bitio::Bits;

      //Shifting zero or by zero has no effect.
      if rhs == 0 || *self == UInt::ZERO { return }

      //Calculate the number of full bytes which will be shifted out.
      let full_bytes = rhs / 8;
      //If all of the bits will be shifted out simply clear the buffer.
      if full_bytes >= self.0.len() { return self.0.clear() }

      //Calculate the number of trailing bits which will be shifted out.
      let trailing_bits = Bits::try_from((rhs % 8) as u8,).ok();

      //Remove all of the full bytes.
      self.0.drain(..full_bytes,);
      //Shift all of the bytes.
      if let Some(trailing_bits) = trailing_bits {
        //Shift all of the bytes and return the bits shifted out.
        self.0.iter_mut().rev().fold(0u8, move |mut buf, byte,| {
          //Mix the low bits with the bits in the buffer.
          *byte ^= buf;
          //Replace the bits in the buffer with the low bits of the byte.
          buf ^= *byte & trailing_bits.mask();
          //Cancel out the original low bits of the byte.
          *byte ^= buf;

          //Rotate the bits being shifted in into the high bits.
          *byte = byte.rotate_right(trailing_bits as u32,);

          buf
        },);
        //Remove the high byte if its been zeroed.
        if self.0[self.0.len() - 1] == 0 { self.0.pop(); }
      }
    }
  }

  impl ShrAssign<u8> for UInt<Vec<u8>,> {
    #[inline]
    fn shr_assign(&mut self, rhs: u8,) { *self >>= rhs as usize }
  }

  impl<Rhs,> Shr<Rhs> for UInt<Vec<u8>,>
    where UInt<Vec<u8>,>: ShrAssign<Rhs>, {
    type Output = UInt<Vec<u8>,>;

    fn shr(mut self, rhs: Rhs,) -> Self::Output { self >>= rhs; self }
  }

  impl<A, Rhs,> Shr<Rhs> for &'_ UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: Shr<Rhs>, {
    type Output = <UInt<Vec<u8>,> as Shr<Rhs>>::Output;

    fn shr(self, rhs: Rhs,) -> Self::Output { self.into_vec() >> rhs }
  }

  impl<'a, A, Rhs,> Shr<Rhs> for &'a mut UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: Shr<Rhs>, {
    type Output = <&'a UInt<A,> as Shr<Rhs>>::Output;

    #[inline]
    fn shr(self, rhs: Rhs,) -> Self::Output { &*self >> rhs }
  }

}

mod and {
  use super::*;

  impl<'a, A,> BitAndAssign<&'a UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn bitand_assign(&mut self, rhs: &'a UInt<A,>,) {
      let rhs = rhs.into_slice();

      self.0.truncate(rhs.0.len(),);

      for (a, &b,) in self.0.iter_mut().zip(rhs.0,) { *a &= b }

      let len = UInt::bytes_to_uint(&mut self.0,).len();
      self.0.truncate(len,);
    }
  }

  impl<A,> BitAndAssign<UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn bitand_assign(&mut self, rhs: UInt<A,>,) { *self &= &rhs }
  }

  impl<'a, A,> BitAndAssign<&'a mut UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn bitand_assign(&mut self, rhs: &'a mut UInt<A,>,) { *self &= &*rhs }
  }

  impl BitAndAssign<usize> for UInt<Vec<u8>,> {
    fn bitand_assign(&mut self, rhs: usize,) { *self &= UInt::from(rhs,) }
  }

  impl BitAndAssign<u8> for UInt<Vec<u8>,> {
    #[inline]
    fn bitand_assign(&mut self, rhs: u8,) { *self &= UInt::from(rhs,) }
  }

  impl<Rhs,> BitAnd<Rhs> for UInt<Vec<u8>,>
    where UInt<Vec<u8>,>: BitAndAssign<Rhs>, {
    type Output = UInt<Vec<u8>,>;

    fn bitand(mut self, rhs: Rhs,) -> Self::Output { self &= rhs; self }
  }

  impl<A, Rhs,> BitAnd<Rhs> for &'_ UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: BitAnd<Rhs>, {
    type Output = <UInt<Vec<u8>,> as BitAnd<Rhs>>::Output;

    fn bitand(self, rhs: Rhs,) -> Self::Output { self.into_vec() & rhs }
  }

  impl<'a, A, Rhs,> BitAnd<Rhs> for &'a mut UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: BitAnd<Rhs>, {
    type Output = <&'a UInt<A,> as BitAnd<Rhs>>::Output;

    #[inline]
    fn bitand(self, rhs: Rhs,) -> Self::Output { &*self & rhs }
  }

}

mod or {
  use super::*;

  impl<'a, A,> BitOrAssign<&'a UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn bitor_assign(&mut self, rhs: &'a UInt<A,>,) {
      let rhs = rhs.into_slice();

      for (a, &b,) in self.0.iter_mut().zip(rhs.0,) { *a |= b }
      if self.0.len() < rhs.0.len() { self.0.extend(rhs.0[self.0.len()..].iter().copied(),) }

      let len = UInt::bytes_to_uint(&mut self.0,).len();
      self.0.truncate(len,);
    }
  }

  impl<A,> BitOrAssign<UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn bitor_assign(&mut self, rhs: UInt<A,>,) { *self |= &rhs }
  }

  impl<'a, A,> BitOrAssign<&'a mut UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn bitor_assign(&mut self, rhs: &'a mut UInt<A,>,) { *self |= &*rhs }
  }

  impl BitOrAssign<usize> for UInt<Vec<u8>,> {
    fn bitor_assign(&mut self, rhs: usize,) { *self |= UInt::from(rhs,) }
  }

  impl BitOrAssign<u8> for UInt<Vec<u8>,> {
    #[inline]
    fn bitor_assign(&mut self, rhs: u8,) { *self |= UInt::from(rhs,) }
  }

  impl<Rhs,> BitOr<Rhs> for UInt<Vec<u8>,>
    where UInt<Vec<u8>,>: BitOrAssign<Rhs>, {
    type Output = UInt<Vec<u8>,>;

    fn bitor(mut self, rhs: Rhs,) -> Self::Output { self |= rhs; self }
  }

  impl<A, Rhs,> BitOr<Rhs> for &'_ UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: BitOr<Rhs>, {
    type Output = <UInt<Vec<u8>,> as BitOr<Rhs>>::Output;

    fn bitor(self, rhs: Rhs,) -> Self::Output { self.into_vec() | rhs }
  }

  impl<'a, A, Rhs,> BitOr<Rhs> for &'a mut UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: BitOr<Rhs>, {
    type Output = <&'a UInt<A,> as BitOr<Rhs>>::Output;

    #[inline]
    fn bitor(self, rhs: Rhs,) -> Self::Output { &*self | rhs }
  }

}

mod xor {
  use super::*;

  impl<'a, A,> BitXorAssign<&'a UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn bitxor_assign(&mut self, rhs: &'a UInt<A,>,) {
      let rhs = rhs.into_slice();

      for (a, &b,) in self.0.iter_mut().zip(rhs.0,) { *a ^= b }
      if self.0.len() < rhs.0.len() { self.0.extend(rhs.0[self.0.len()..].iter().copied(),) }

      let len = UInt::bytes_to_uint(&mut self.0,).len();
      self.0.truncate(len,);
    }
  }

  impl<A,> BitXorAssign<UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn bitxor_assign(&mut self, rhs: UInt<A,>,) { *self ^= &rhs }
  }

  impl<'a, A,> BitXorAssign<&'a mut UInt<A,>> for UInt<Vec<u8>,>
    where A: Borrow<[u8]>, {
    fn bitxor_assign(&mut self, rhs: &'a mut UInt<A,>,) { *self ^= &*rhs }
  }

  impl BitXorAssign<usize> for UInt<Vec<u8>,> {
    fn bitxor_assign(&mut self, rhs: usize,) { *self ^= UInt::from(rhs,) }
  }

  impl BitXorAssign<u8> for UInt<Vec<u8>,> {
    #[inline]
    fn bitxor_assign(&mut self, rhs: u8,) { *self ^= UInt::from(rhs,) }
  }

  impl<Rhs,> BitXor<Rhs> for UInt<Vec<u8>,>
    where UInt<Vec<u8>,>: BitXorAssign<Rhs>, {
    type Output = UInt<Vec<u8>,>;

    fn bitxor(mut self, rhs: Rhs,) -> Self::Output { self ^= rhs; self }
  }

  impl<A, Rhs,> BitXor<Rhs> for &'_ UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: BitXor<Rhs>, {
    type Output = <UInt<Vec<u8>,> as BitXor<Rhs>>::Output;

    fn bitxor(self, rhs: Rhs,) -> Self::Output { self.into_vec() ^ rhs }
  }

  impl<'a, A, Rhs,> BitXor<Rhs> for &'a mut UInt<A,>
    where A: Borrow<[u8]>,
      UInt<Vec<u8>,>: BitXor<Rhs>, {
    type Output = <&'a UInt<A,> as BitXor<Rhs>>::Output;

    #[inline]
    fn bitxor(self, rhs: Rhs,) -> Self::Output { &*self ^ rhs }
  }

}

impl From<u8> for UInt<Vec<u8>,> {
  fn from(from: u8,) -> Self {
    if from == 0 { Self::ZERO }
    else { UInt(alloc::vec![from,],) }
  }
}

impl From<u16> for UInt<Vec<u8>,> {
  fn from(from: u16,) -> Self {
    UInt(UInt::bytes_to_uint(&mut u16::to_le_bytes(from,),).into(),)
  }
}

impl From<u32> for UInt<Vec<u8>,> {
  fn from(from: u32,) -> Self {
    UInt(UInt::bytes_to_uint(&mut u32::to_le_bytes(from,),).into(),)
  }
}

impl From<u64> for UInt<Vec<u8>,> {
  fn from(from: u64,) -> Self {
    UInt(UInt::bytes_to_uint(&mut u64::to_le_bytes(from,),).into(),)
  }
}

impl From<u128> for UInt<Vec<u8>,> {
  fn from(from: u128,) -> Self {
    UInt(UInt::bytes_to_uint(&mut u128::to_le_bytes(from,),).into(),)
  }
}

impl From<usize> for UInt<Vec<u8>,> {
  fn from(from: usize,) -> Self {
    UInt(UInt::bytes_to_uint(&mut usize::to_le_bytes(from,),).into(),)
  }
}

impl From<Vec<u8>> for UInt<Vec<u8>,> {
  #[inline]
  fn from(from: Vec<u8>,) -> Self { Self::new(from,) }
}

impl<'a,> From<&'a [u8]> for UInt<Vec<u8>,> {
  fn from(from: &'a [u8],) -> Self { UInt::new(from.into(),) }
}

impl<'a,> From<&'a mut [u8]> for UInt<Vec<u8>,> {
  fn from(from: &'a mut [u8],) -> Self { UInt::new(from.into(),) }
}

impl From<Box<[u8]>> for UInt<Vec<u8>,> {
  fn from(from: Box<[u8]>,) -> Self { UInt::new(from.into(),) }
}

impl FromStr for UInt<Vec<u8>,> {
  type Err = ParseIntError;

  fn from_str(s: &str,) -> Result<Self, Self::Err> {
    if s.starts_with('-',) { return Err(ParseIntError(IntErrorKind::InvalidDigit,)) }
    let s = s.strip_prefix('+',).unwrap_or(s,);

    //Accumulate all of the digits into a value.
    s.chars().try_fold(UInt::ZERO.into_vec(), |mut acc, c,| {
      //Convert the char to a digit.
      let digit = c.to_digit(10,).ok_or(ParseIntError(IntErrorKind::InvalidDigit,),)? as usize;

      //Shift all of the previous digits by one `base10` digit for the next digit to come in.
      acc *= 10usize;
      //Add the digit to the accumulator.
      acc += digit;

      Ok(acc)
    },)
  }
}

impl<A,> FromIterator<A> for UInt<Vec<u8>,>
  where A: Into<u8>, {
  fn from_iter<I,>(iter: I,) -> Self
    where I: IntoIterator<Item = A>, {
    Self::new(iter.into_iter().map(A::into,).collect(),)
  }
}

impl<A,> fmt::Display for UInt<A,>
  where A: Borrow<[u8]>, {
  fn fmt(&self, fmt: &mut fmt::Formatter,) -> fmt::Result {
    use core::{iter, fmt::Write,};

    //Handle the zero case.
    if *self == UInt::ZERO { return fmt.write_char('0',) }

    let mut num = self.into_vec();
    let ten = UInt::from(10usize,);
    //Get the digits in reverse order.
    let buffer = iter::from_fn(move || {
      if num == UInt::ZERO { return None }

      //Get the next digit.
      let digit = u8::try_from(UInt::rem(&mut num, &ten,),).unwrap_or(0,);

      Some(digit)
    },).collect::<Vec<_>>();

    //Write the digits in the correct order.
    for digit in buffer.into_iter().rev().skip_while(|&c,| c == 0,) { fmt.write_char((b'0' + digit) as char,)? }

    Ok(())
  }
}

impl<A,> fmt::Debug for UInt<A,>
  where A: Borrow<[u8]>, {
  #[inline]
  fn fmt(&self, fmt: &mut fmt::Formatter,) -> fmt::Result { write!(fmt, "{}", *self,) }
}

impl<A,> fmt::Binary for UInt<A,>
  where A: Borrow<[u8]>, {
  fn fmt(&self, fmt: &mut fmt::Formatter,) -> fmt::Result {
    use bitio::{Bits, BitRead, ReadIter,};
    use core::fmt::Write;

    if fmt.alternate() { fmt.write_str("0b",)? }
    //Handle the zero case.
    if *self == UInt::ZERO { return fmt.write_str("0",) }

    let bytes = self.0.borrow();
    let last = bytes.len() - 1;
    let leading_zeros = unsafe { Bits::from_u8(bytes[last].leading_zeros() as u8,) };
    let mut bytes = ReadIter::new(bytes.iter().copied().rev(),);
    bytes.skip(leading_zeros,).or(Err(fmt::Error),)?;

    loop {
      match bytes.read_byte() {
        //Write the digits.
        Ok(byte) => write!(fmt, "{:b}", byte,)?,
        //Write the final bits.
        Err(bits) => {
          for _ in 0..Bits::as_u8(bits) {
            let bit = if let Ok(v) = bytes.read_bit() { v }
              else { return Err(fmt::Error) };
            let digit = (b'0' + bit as u8) as char;
            fmt.write_char(digit,)?;
          }

          return Ok(())
        },
      }
    }
  }
}

impl<A,> fmt::LowerHex for UInt<A,>
  where A: Borrow<[u8]>, {
  fn fmt(&self, fmt: &mut fmt::Formatter,) -> fmt::Result {
    if fmt.alternate() { fmt.write_str("0x",)? }
    //Handle the zero case.
    if *self == UInt::ZERO { return fmt.write_str("0",) }

    let bytes = self.0.borrow();
    let mut digits = bytes.iter().copied().rev();

    if let Some(digit) = digits.next() { write!(fmt, "{:x}", digit,)? }
    for digit in digits {
      if digit >= 16 { write!(fmt, "{:x}", digit,) }
      else { write!(fmt, "0{:x}", digit,) }?
    }

    Ok(())
  }
}

impl<A,> fmt::UpperHex for UInt<A,>
  where A: Borrow<[u8]>, {
  fn fmt(&self, fmt: &mut fmt::Formatter,) -> fmt::Result {
    if fmt.alternate() { fmt.write_str("0x",)? }
    //Handle the zero case.
    if *self == UInt::ZERO { return fmt.write_str("0",) }

    let bytes = self.0.borrow();
    let mut digits = bytes.iter().copied().rev();

    if let Some(digit) = digits.next() { write!(fmt, "{:X}", digit,)? }
    for digit in digits {
      if digit >= 16 { write!(fmt, "{:X}", digit,) }
      else { write!(fmt, "0{:X}", digit,) }?
    }

    Ok(())
  }
}

impl From<UInt<Vec<u8>,>> for Vec<u8> {
  #[inline]
  fn from(from: UInt<Vec<u8>,>,) -> Self { from.into_inner() }
}

impl TryFrom<SInt<Vec<u8>,>> for UInt<Vec<u8>,> {
  type Error = FromIntError<SInt<Vec<u8>,>,>;

  fn try_from(from: SInt<Vec<u8>,>,) -> Result<Self, Self::Error> {
    if from.signum() == -1 { Err(FromIntError(from,)) }
    else { Ok(from.0 >> 1usize) }
  }
}

impl<A,> TryFrom<UInt<A,>> for usize
  where A: BorrowMut<[u8]>, {
  type Error = FromIntError<UInt<A,>,>;

  fn try_from(mut from: UInt<A,>,) -> Result<Self, Self::Error> {
    use core::mem::size_of;

    //Get the slice view of the value.
    let bytes = from.into_slice_mut();
    //Get the bytes from the slice.
    let bytes = bytes.into_inner();
    if bytes.len() <= size_of::<usize>() {
      let mut buffer = [0; size_of::<usize>()];
      for i in 0..bytes.len() { buffer[i] = bytes[i] }

      Ok(usize::from_le_bytes(buffer,))
    } else { Err(FromIntError(from,)) }
  }
}

impl<A,> TryFrom<UInt<A,>> for u8
  where A: BorrowMut<[u8]>, {
  type Error = FromIntError<UInt<A,>,>;

  fn try_from(mut from: UInt<A,>,) -> Result<Self, Self::Error> {
    use core::mem::size_of;

    //Get the slice view of the value.
    let bytes = from.into_slice_mut();
    //Get the bytes from the slice.
    let bytes = bytes.into_inner();
    if bytes.len() <= size_of::<u8>() {
      let mut buffer = [0; size_of::<u8>()];
      for i in 0..bytes.len() { buffer[i] = bytes[i] }

      Ok(u8::from_le_bytes(buffer,))
    } else { Err(FromIntError(from,)) }
  }
}

impl<A,> TryFrom<UInt<A,>> for u16
  where A: BorrowMut<[u8]>, {
  type Error = FromIntError<UInt<A,>,>;

  fn try_from(mut from: UInt<A,>,) -> Result<Self, Self::Error> {
    use core::mem::size_of;

    //Get the slice view of the value.
    let bytes = from.into_slice_mut();
    //Get the bytes from the slice.
    let bytes = bytes.into_inner();
    if bytes.len() <= size_of::<u16>() {
      let mut buffer = [0; size_of::<u16>()];
      for i in 0..bytes.len() { buffer[i] = bytes[i] }

      Ok(u16::from_le_bytes(buffer,))
    } else { Err(FromIntError(from,)) }
  }
}

impl<A,> TryFrom<UInt<A,>> for u32
  where A: BorrowMut<[u8]>, {
  type Error = FromIntError<UInt<A,>,>;

  fn try_from(mut from: UInt<A,>,) -> Result<Self, Self::Error> {
    use core::mem::size_of;

    //Get the slice view of the value.
    let bytes = from.into_slice_mut();
    //Get the bytes from the slice.
    let bytes = bytes.into_inner();
    if bytes.len() <= size_of::<u32>() {
      let mut buffer = [0; size_of::<u32>()];
      for i in 0..bytes.len() { buffer[i] = bytes[i] }

      Ok(u32::from_le_bytes(buffer,))
    } else { Err(FromIntError(from,)) }
  }
}

impl<A,> TryFrom<UInt<A,>> for u64
  where A: BorrowMut<[u8]>, {
  type Error = FromIntError<UInt<A,>,>;

  fn try_from(mut from: UInt<A,>,) -> Result<Self, Self::Error> {
    use core::mem::size_of;

    //Get the slice view of the value.
    let bytes = from.into_slice_mut();
    //Get the bytes from the slice.
    let bytes = bytes.into_inner();
    if bytes.len() <= size_of::<u64>() {
      let mut buffer = [0; size_of::<u64>()];
      for i in 0..bytes.len() { buffer[i] = bytes[i] }

      Ok(u64::from_le_bytes(buffer,))
    } else { Err(FromIntError(from,)) }
  }
}

impl<A,> TryFrom<UInt<A,>> for u128
  where A: BorrowMut<[u8]>, {
  type Error = FromIntError<UInt<A,>,>;

  fn try_from(mut from: UInt<A,>,) -> Result<Self, Self::Error> {
    use core::mem::size_of;

    //Get the slice view of the value.
    let bytes = from.into_slice_mut();
    //Get the bytes from the slice.
    let bytes = bytes.into_inner();
    if bytes.len() <= size_of::<u128>() {
      let mut buffer = [0; size_of::<u128>()];
      for i in 0..bytes.len() { buffer[i] = bytes[i] }

      Ok(u128::from_le_bytes(buffer,))
    } else { Err(FromIntError(from,)) }
  }
}
