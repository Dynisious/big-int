//! Author --- DMorgan  
//! Last Moddified --- 2019-12-31

#![cfg(feature = "serde",)]

use super::*;
use ::serde::{
  ser::{Serialize, Serializer,},
  de::{Deserialize, Deserializer, SeqAccess, Visitor, Error, Unexpected,},
};
use core::fmt;

impl<A,> Serialize for UInt<A,>
  where A: Borrow<[u8]>, {
  fn serialize<S,>(&self, serializer: S,) -> Result<S::Ok, S::Error>
    where S: Serializer, {
    serializer.serialize_bytes(&self.into_slice().0,)
  }
}

impl<'de,> Deserialize<'de,> for UInt<Vec<u8>> {
  fn deserialize<D,>(deserializer: D,) -> Result<Self, D::Error>
    where D: Deserializer<'de,>, {
    struct UIntVisitor;

    impl UIntVisitor {
      fn check_buf<E,>(buf: &[u8],) -> Result<(), E>
        where E: Error, {
        if buf.last().copied() == Some(255) {
          return Err(E::invalid_value(
            Unexpected::Bytes(buf,),
            &"a byte buffer ending in a value `v < 255`",
          ))
        }

        Ok(())
      }
    }

    impl<'de,> Visitor<'de,> for UIntVisitor {
      type Value = UInt<Vec<u8>,>;

      #[inline]
      fn expecting(&self, fmt: &mut fmt::Formatter,) -> fmt::Result { write!(fmt, "an array of bytes",) }
      fn visit_byte_buf<E,>(self, bytes: Vec<u8>,) -> Result<Self::Value, E,>
        where E: Error, {
        //Check the buffer.
        Self::check_buf(&bytes,)?;

        //Wrap the bytes.
        Ok(UInt(bytes,))
      }
      fn visit_bytes<E,>(self, bytes: &[u8],) -> Result<Self::Value, E,>
        where E: Error, {
        //Check the buffer.
        Self::check_buf(bytes,)?;

        //Copy the bytes.
        Ok(UInt(Vec::from(bytes,),))
      }
      fn visit_seq<A,>(self, mut seq: A,) -> Result<Self::Value, A::Error>
        where A: SeqAccess<'de,>, {
        //Create a store for the bytes.
        let mut bytes = Vec::with_capacity(seq.size_hint().unwrap_or(0,),);
        //Read in all of the bytes.
        while let Some(v) = seq.next_element()? { bytes.push(v,) }
        //Check the bytes.
        Self::check_buf(&bytes,)?;

        //Wrap the bytes.
        Ok(UInt(bytes,))
      }
    }
  
    deserializer.deserialize_byte_buf(UIntVisitor,)
  }
}

#[cfg(test,)]
mod tests {
  use super::*;
  use serde_cbor;

  #[allow(non_snake_case,)]
  #[test]
  fn test_UInt_serde() {
    let data = serde_cbor::to_vec(&UInt::from(100usize,),)
      .expect("Failed to serialise `100`",);
    let int = serde_cbor::from_slice::<UInt,>(&data,)
      .expect("Failed to deserialise `UInt`",);

    assert_eq!(int, UInt::from(100usize,), "Deserialised value corrupted",);
  }
}
