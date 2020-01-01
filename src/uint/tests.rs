//! Author --- DMorgan  
//! Last Moddified --- 2019-12-31

#![cfg(test,)]

use super::*;

#[allow(non_snake_case,)]
#[test]
fn test_UInt_convert() {
  assert_eq!(UInt::ZERO, UInt::from(0usize,), "`convert 0` failed",);
  assert_eq!(UInt(vec![1],), UInt::from(1usize,), "`convert 1` failed.",);
  assert_eq!(UInt(vec![0, 1,],), UInt::from(256usize,), "`convert 256` failed.",);
  assert_eq!(UInt(vec![0, 2,],), UInt::from(512usize,), "`convert 512` failed.",);
  assert_eq!(UInt(vec![0, 4,],), UInt::from(1024usize,), "`convert 1024` failed.",);

  let pairs = (0usize..=1000).map(|n,| n * n,).map(|n,| (UInt::from(n,), n,),);
  for (int, num,) in pairs {
    let bytes = usize::to_le_bytes(num,);
    let len = bytes.len() - bytes.iter().rev().take_while(|&&b,| b == 0,).count();
    let bytes = &bytes[..len];

    assert_eq!(bytes, &*int.0, "Conversion failed on {} with {:?}", num, int,);
  }
}

#[allow(non_snake_case,)]
#[test]
fn test_UInt_add_sub() {
  let one = UInt(vec![1,],);
  let two = UInt(vec![2,],);
  let ten = UInt(vec![0b1010,],);

  let mut data = [!0,];
  let overflow = unsafe { UInt(&mut data[..],).half_add_bytes(&one.0,) };
  assert_eq!(data[0], 0, "`half_add` corrupted data",);
  assert_eq!(overflow, true, "`half_add` did not overflow",);

  let mut num = ten.clone();
  unsafe { num.add_bytes(&UInt::ZERO.0,); }
  assert_eq!(num, ten, "`add_bytes 10 + 0` failed",);
  assert_eq!(&ten + UInt::ZERO, ten, "`10 + 0` failed",);

  let three = UInt(vec![0b11,],);
  let mut num = one.clone();
  unsafe { num.add_bytes(&two.0,); }
  assert_eq!(num, three, "`add_bytes 1 + 2` failed",);
  assert_eq!(&one + &two, three, "`1 + 2` failed",);

  for (a, b,) in (0usize..1000).map(|n,| (n * n, n,),) {
    let target = UInt::from(a + b,);
    let num_b = UInt::from(b,);
    let num_a = UInt::from(a,);
    let mut num = num_a.clone();
    unsafe { num.add_bytes(&num_b.0,); }
    assert_eq!(num, target, "`add_bytes {} + {}` failed, got {}", a, b, num,);
    assert_eq!(num_a + num_b, target, "`{} + {}` failed", a, b,);
  }

  let mut data = [0,];
  let underflow = unsafe { UInt(&mut data[..],).half_sub_bytes(&one.0,) }.is_none();
  assert_eq!(data[0], !0, "`half_sub` corrupted data",);
  assert_eq!(underflow, true, "`half_sub` did not underflow",);

  let mut num = ten.clone();
  unsafe { num.sub_bytes(&UInt::ZERO.0,); }
  assert_eq!(num, ten, "`add_bytes 10 - 0` failed",);
  assert_eq!(&ten + UInt::ZERO, ten, "`10 - 0` failed",);

  let eight = UInt(vec![0b1000,],);
  let mut num = ten.clone();
  unsafe { num.sub_bytes(&two.0,); }
  assert_eq!(num, eight, "`sub_bytes 10 - 2` failed",);
  assert_eq!(&ten - &two, eight, "`10 - 2` failed",);

  for (a, b,) in (0usize..1000).map(|n,| (n * n, n,),) {
    let target = UInt::from(a - b,);
    let num_b = UInt::from(b,);
    let num_a = UInt::from(a,);
    let mut num = num_a.clone();
    unsafe { num.sub_bytes(&num_b.0,); }
    assert_eq!(num, target, "`sub_bytes {} - {}` failed, got {}", a, b, num,);
    assert_eq!(num_a - num_b, target, "`{} - {}` failed", a, b,);
  }
}

#[allow(non_snake_case,)]
#[test]
fn test_UInt_mul_div() {
  let one = UInt(vec![1],);
  let two = UInt(vec![2,],);
  let five = UInt(vec![0b101,],);
  let ten = UInt(vec![0b1010,],);

  let mut num = five.clone();
  num.mul_bytes(UInt::ZERO.into_slice(),);
  assert_eq!(num, UInt::ZERO, "`mul_bytes 5 * 0` failed",);
  assert_eq!(&five * &UInt::ZERO, UInt::ZERO, "`5 * 0` failed",);

  let mut num = ten.clone();
  num.mul_bytes(one.into_slice(),);
  assert_eq!(num, ten, "`mul_bytes 10 * 1` failed",);
  assert_eq!(&ten * &one, ten, "`10 * 1` failed",);

  let twenty = UInt(vec![0b10100,],);
  let mut num = ten.clone();
  num.mul_bytes(two.into_slice(),);
  assert_eq!(num, twenty, "`mul_bytes 10 * 2` failed",);
  assert_eq!(&ten * &two, twenty, "`10 * 2` failed",);

  for (a, b,) in (0usize..1000).map(|n,| (n, n * n,),) {
    let target = UInt::from(a * b,);
    let num_b = UInt::from(b,);
    let num_a = UInt::from(a,);
    let mut num = num_a.clone();
    num.mul_bytes(num_b.into_slice(),);
    assert_eq!(num, target, "`mul_bytes {} * {}` failed, got {}", a, b, num,);
    assert_eq!(num_a * num_b, target, "`{} * {}` failed", a, b,);
  }

  let mut num = ten.clone();
  UInt::rem(&mut num, one.into_slice(),);
  assert_eq!(num, ten, "`div_bytes 10 / 1` failed",);
  assert_eq!(&ten / &one, ten, "`10 / 1` failed",);

  let four = UInt(vec![0b100,],);
  let mut num = twenty.clone();
  UInt::rem(&mut num, five.into_slice(),);
  assert_eq!(num, four, "`div_bytes 20 / 5` failed",);
  assert_eq!(&twenty / &five, four, "`20 / 5` failed",);

  for (a, b,) in (1usize..=1000).map(|n,| (n * n, n,),) {
    let target = UInt::from(a / b,);
    let num_b = UInt::from(b,);
    let num_a = UInt::from(a,);
    let mut num = num_a.clone();
    UInt::rem(&mut num, num_b.into_slice(),);
    assert_eq!(num, target, "`mul_bytes {} / {}` failed, got {}", a, b, num,);
    assert_eq!(num_a / num_b, target, "`{} / {}` failed", a, b,);
  }
}

#[allow(non_snake_case,)]
#[test]
fn test_UInt_shift() {
  let five = UInt(vec![0b101,],);
  let ten = UInt(vec![0b1010,],);

  let twenty = UInt(vec![0b10100,],);
  assert_eq!(&ten << 1usize, twenty, "`10 << 1` failed",);

  for (a, b,) in (1usize..32).map(|n,| (n * n, n,),) {
    let target = UInt::from(a << b,);
    let num_a = UInt::from(a,);
    assert_eq!(num_a << b, target, "`{} << {}` failed", a, b,);
  }

  assert_eq!(&ten >> 1usize, five, "`10 >> 1` failed",);

  for (a, b,) in (1usize..32).map(|n,| (n * n, n,),) {
    let target = UInt::from(a.wrapping_shr(b as u32,),);
    let num_a = UInt::from(a,);
    assert_eq!(num_a >> b, target, "`{} >> {}` failed", a, b,);
  }
}

#[allow(non_snake_case,)]
#[test]
fn test_UInt_rem() {
  let one = UInt(vec![1],);
  let two = UInt(vec![2,],);
  let ten = UInt(vec![0b1010,],);
  let twenty = UInt(vec![0b10100,],);

  let mut num = ten.clone();
  num %= 3;
  assert_eq!(num, one, "`10 % 3` failed, got {}", num,);

  let mut num = twenty.clone();
  num %= 3;
  assert_eq!(num, two, "`20 % 2` failed, got {}", num,);

  for (a, b,) in (1usize..1000).map(|n,| (n * n, n,),) {
    let target = UInt::from(a % b,);
    let num_a = UInt::from(a,);
    let mut num = num_a.clone();
    num %= b;
    assert_eq!(num, target, "`{} % {}` failed, got {}", a, b, num,);
    assert_eq!(num_a % b, target, "`{} % {}` failed", a, b,);
  }
}

#[allow(non_snake_case,)]
#[test]
fn test_UInt_display() {
  let five = UInt(vec![0b101,],);
  let ten = UInt(vec![0b1010,],);
  let one_hundered = UInt(vec![0b1100100,],);

  assert_eq!(format!("{}", five,), "5",);
  assert_eq!(format!("{}", ten,), "10",);
  assert_eq!(format!("{}", one_hundered,), "100",);

  for num in (1usize..128).map(|n,| n * n,) {
    let int = UInt::from(num,);

    assert_eq!(
      format!(
        "Dsp:{}, Dbg:{:?}, Bin:{:b}, hex:{:x}, Hex:{:X}, Dbg:{:#?}, Bin:{:#b}, hex:{:#x}, Hex:{:#X},",
        int, int, int, int, int, int, int, int, int,
      ),
      format!(
        "Dsp:{}, Dbg:{:?}, Bin:{:b}, hex:{:x}, Hex:{:X}, Dbg:{:#?}, Bin:{:#b}, hex:{:#x}, Hex:{:#X},",
        num, num, num, num, num, num, num, num, num,
      ),
    );
  }
}
