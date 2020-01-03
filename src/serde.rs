//! Author --- DMorgan  
//! Last Moddified --- 2019-01-03

use crate::{SInt, uint::*,};
use bitio::{Bits, BitWrite, BitRead, ReadIter, WriteIter,};
use alloc::vec::Vec;
use core::convert::TryFrom;

/// Uses a compact self encoding format to encode `num` in a bitwise manner.
/// 
/// Returns the number of bits written.
/// 
/// # Params
/// 
/// num --- The number to encode.  
/// writer --- The writer to write too.  
pub fn uint_encode<W,>(mut num: UInt<Vec<u8>,>, writer: &mut W,) -> Result<UInt<Vec<u8>,>, W::Error>
  where W: BitWrite, {
  /// # Params
  /// 
  /// num --- The number to encode.  
  /// skip --- The number of leading zeros to skip from the leading bit.
  /// writer --- The writer to write too.  
  fn encode<W,>(num: &[u8], skip: Option<Bits>, writer: &mut W,) -> Result<UInt<Vec<u8>,>, W::Error>
    where W: BitWrite, {
    //Get the length of `num` in bits, subtract one so that the lengths will tend towards zero.
    let mut length = (UInt::from(num.len() - 1,) << 3usize) + (7 - Bits::as_u8(skip,)) as usize;
    //Get the number of bits encoded and encode `length` first if it is non zero.
    let encoded_length = if let Some(last) = length.0.last_mut() {
      //Get the leading bit of the leading byte.
      let leading_bit = match Bits::used_bits(*last,) {
        Some(v) => v,
        //It is impossible for the leading byte of a `UInt` to be zero.
        None => unsafe { core::hint::unreachable_unchecked() },
      };
      //Get the number of leading zeros to skip when encoding.
      let skip = leading_bit.recip();
      let leading_bit = leading_bit.bit();

      //Zero the leading bit to mark this as a length component.
      *last ^= leading_bit;
      //Encode the length component.
      let encoded_length = encode(&length.0, skip, writer,)?;

      //Unzero the leading bit to restore the bit count.
      let last = length.0.len() - 1;
      length.0[last] ^= leading_bit;

      //Add in the length to the count of encoded bits.
      length + 1u8 + encoded_length
    } else { length + 1u8 };

    //Read all of the bytes in `big endian` order.
    let mut reader = ReadIter::new(num.iter().rev(),);
    //Skip the leading zeros.
    if let Some(skip) = skip { reader.skip(skip,).expect("Error skipping leading zeros",); }
    //Encode all the bits.
    loop { match reader.read_byte() {
      //Encode the full byte.
      Ok(byte) => { writer.write_byte(byte,)?; },
      //Encode the final bits.
      Err(remaining) => {
        if let Some(remaining) = remaining {
          writer.write_bits(remaining, reader.read_bits(remaining,)
            .expect("Failed to read the exact bits available",),
          )?;
        }

        //Return the encoded length.
        break Ok(encoded_length)
      },
    } }
  }

  //Increment `num` as `0` has no encoding.
  num += 1u8;
  //Skip any leading zeros.
  let skip = Bits::unused_bits(*num.0.last().expect("Failed to read the last byte",),);
  encode(&num.0, skip, writer,)
}

/// Decodes a number from `reader` in a bitwise manner.
/// 
/// The number must have been encoded using `bit_encode`.
/// 
/// # Params
/// 
/// reader --- The reader to read from.  
pub fn uint_decode<R,>(reader: &mut R,) -> Result<UInt<Vec<u8>,>, R::Error>
  where R: BitRead, {
  fn decode<R,>(mut length: UInt<Vec<u8>,>, reader: &mut R,) -> Result<UInt<Vec<u8>,>, R::Error>
    where R: BitRead, {
    //If the first bit is a `1` then this is the value component.
    let is_value = reader.read_bit()?;
    //Count the bit we just read.
    length -= 1u8;

    //Calculate the number of trailing bits we will need to read in.
    let trailing_bits = try {
      //The number of trailing bits is the remainder after division by `8`.
      let trailing_bits = length.rem(&UInt::from(8u8,),);

      //Convert the trailing bits into a `Bits` value.
      Bits::try_from(u8::try_from(trailing_bits,).ok()?,).ok()?
    };
    //While calculating the remainder `length` became the `quotient` of `length / 8`, and
    //therefore the number of full bytes to be read.
    let full_bytes = usize::try_from(length,).expect("The number of full bytes overflows a usize",);
    //The number of leading zeros we need to align the writer, taking into acount that we
    //read in one bit already.
    let leading_zeros = Bits::try_from(7 - Bits::as_u8(trailing_bits,),).ok();

    //Allocate space for the number.
    let mut num = UInt(vec![0; full_bytes + (leading_zeros.is_some() || trailing_bits.is_some()) as usize],);
    //Write all of the bits to a `Vec`.
    let mut writer = WriteIter::new(num.0.iter_mut().rev(),);
    //Write in the leading zeros.
    if let Some(leading_zeros) = leading_zeros {
      writer.write_bits(leading_zeros, 0,)
      .expect("Error writing the leading zeros",);
    }
    //Write in the leading bit we read already.
    writer.write_bit(true,).expect("Error writing the lead bit",);
    //Write all of the full bytes.
    for _ in 0..full_bytes {
      writer.write_byte(reader.read_byte()?,)
      .expect("Error writing the full bytes",);
    }
    //Write all of the trailing bits.
    if let Some(trailing_bits) = trailing_bits {
      writer.write_bits(trailing_bits, reader.read_bits(trailing_bits,)?,)
      .expect("Error writing the trailing bits",);
    }

    debug_assert!(
      writer.into_iter().expect("Failed to unwrap the writer",).next().is_none(),
      "Unwritten bytes remained in the writer",
    );
    //All values are incremented before encoding.
    if is_value { Ok(num - 1u8) }
    //All length components are decremented before encoding.
    else { decode(num + 1u8, reader,) }
  }

  decode(UInt::ONE.into_vec(), reader,)
}

/// Uses a compact self encoding format to encode `num` in a bitwise manner.
/// 
/// Returns the number of bits written.
/// 
/// # Params
/// 
/// num --- The number to encode.  
/// writer --- The writer to write too.  
pub fn sint_encode<W,>(num: SInt<Vec<u8>,>, writer: &mut W,) -> Result<UInt<Vec<u8>,>, W::Error>
  where W: BitWrite, {
  uint_encode(num.0, writer,)
}

/// Decodes a number from `reader` in a bitwise manner.
/// 
/// The number must have been encoded using `bit_encode`.
/// 
/// # Params
/// 
/// reader --- The reader to read from.  
pub fn sint_decode<R,>(reader: &mut R,) -> Result<SInt<Vec<u8>,>, R::Error>
  where R: BitRead, {
  uint_decode(reader,).map(SInt,)
}

#[cfg(test,)]
mod tests {
  use super::*;
  use bitio::WriteVec;

  #[allow(non_snake_case,)]
  #[test]
  fn test_UInt_encoding() {
    for num in (0usize..1000).step_by(10,).map(|n,| n * n,).map(UInt::from,) {
      let mut writer = WriteVec::new();
      uint_encode(num.clone(), &mut writer,)
        .expect(&format!("`encoding {}` failed", num,),);
      let buffer = match writer.into_vec() {
        Ok(v) => v,
        Err(e) => {
          let skip = e.misalign();
          let mut writer = e.into_inner();

          writer.write_bits(skip, 0,).ok();
          writer.into_vec().expect("There was an error unwrapping the buffer",)
        },
      };
      let decoded = uint_decode(&mut ReadIter::new(buffer),)
        .expect(&format!("`decoding {}` failed", num,),);

      assert_eq!(decoded, num, "Error encoding/decoding {}", num,);
    }
  }

  #[allow(non_snake_case,)]
  #[test]
  fn test_SInt_encoding() {
    for num in (-1000isize..1000).step_by(10,).map(|n,| n * n.abs(),).map(SInt::from,) {
      let mut writer = WriteVec::new();
      sint_encode(num.clone(), &mut writer,)
        .expect(&format!("`encoding {}` failed", num,),);
      let buffer = match writer.into_vec() {
        Ok(v) => v,
        Err(e) => {
          let skip = e.misalign();
          let mut writer = e.into_inner();

          writer.write_bits(skip, 0,).ok();
          writer.into_vec().expect("There was an error unwrapping the buffer",)
        },
      };
      let decoded = sint_decode(&mut ReadIter::new(buffer),)
        .expect(&format!("`decoding {}` failed", num,),);

      assert_eq!(decoded, num, "Error encoding/decoding {}", num,);
    }
  }
}
