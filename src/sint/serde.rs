//! Author --- DMorgan  
//! Last Moddified --- 2019-12-31

#![cfg(feature = "serde",)]

use super::*;
use ::serde::{
  ser::{Serialize, Serializer,},
  de::{Deserialize, Deserializer,},
};

impl<A,> Serialize for SInt<A,>
  where A: Borrow<[u8]>,
    UInt<A,>: Serialize, {
  #[inline]
  fn serialize<S,>(&self, serializer: S,) -> Result<S::Ok, S::Error>
    where S: Serializer, { self.0.serialize(serializer,) }
}

impl<'de,> Deserialize<'de,> for SInt<Vec<u8>> {
  #[inline]
  fn deserialize<D,>(deserializer: D,) -> Result<Self, D::Error>
    where D: Deserializer<'de,>, { UInt::deserialize(deserializer,).map(SInt,) }
}

#[cfg(test,)]
mod tests {
  use super::*;
  use serde_cbor;

  #[allow(non_snake_case,)]
  #[test]
  fn test_SInt_serde() {
    let data = serde_cbor::to_vec(&SInt::from(100isize,),)
      .expect("Failed to serialise `100`",);
    let int = serde_cbor::from_slice::<SInt,>(&data,)
      .expect("Failed to deserialise `SInt`",);

    assert_eq!(int, SInt::from(100isize,), "Deserialised value corrupted",);
  }
}
