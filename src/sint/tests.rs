//! Author --- DMorgan  
//! Last Moddified --- 2019-12-31

#![cfg(test,)]

use super::*;

#[allow(non_snake_case,)]
#[test]
fn test_SInt_convert() {
  assert_eq!(SInt::ZERO, SInt::from(0isize,), "`convert 0` failed",);
  
  assert_eq!(SInt(UInt(vec![2],),), SInt::from(1isize,), "`convert 1` failed.",);
  assert_eq!(SInt(UInt(vec![0, 2,],),), SInt::from(256isize,), "`convert 256` failed.",);
  assert_eq!(SInt(UInt(vec![0, 4,],),), SInt::from(512isize,), "`convert 512` failed.",);
  assert_eq!(SInt(UInt(vec![0, 8,],),), SInt::from(1024isize,), "`convert 1024` failed.",);
  assert_eq!(SInt(UInt(vec![3],),), SInt::from(-1isize,), "`convert -1` failed.",);
  assert_eq!(SInt(UInt(vec![1, 2,],),), SInt::from(-256isize,), "`convert -256` failed.",);
  assert_eq!(SInt(UInt(vec![1, 4,],),), SInt::from(-512isize,), "`convert -512` failed.",);
  assert_eq!(SInt(UInt(vec![1, 8,],),), SInt::from(-1024isize,), "`convert -1024` failed.",);

  let pairs = (-1000isize..=1000).map(|n,| n.abs() * n,).map(|n,| (SInt::from(n,), n,),);
  for (int, num,) in pairs {
    let int = isize::try_from(int,).expect("Failed to recover int",);

    assert_eq!(int, num, "Conversion failed on",);
  }
}

#[allow(non_snake_case,)]
#[test]
fn test_SInt_neg() {
  let pairs = (-1000isize..=1000).map(|n,| n.abs() * n,).map(|n,| (SInt::from(n,), -n,),);
  for (int, num,) in pairs {
    let int = isize::try_from(-int,).expect("Failed to recover int",);

    assert_eq!(int, num, "Negation failed on",);
  }
}

#[allow(non_snake_case,)]
#[test]
fn test_SInt_add_sub() {
  let one = SInt(UInt(vec![2,],),);
  let two = SInt(UInt(vec![4,],),);
  let ten = SInt(UInt(vec![0b10100,],),);

  let three = SInt(UInt(vec![0b110,],),);
  assert_eq!(&one + &two, three, "`1 + 2` failed",);

  assert_eq!(&ten + SInt::ZERO, ten, "`10 + 0` failed",);

  let three = SInt(UInt(vec![0b110,],),);
  assert_eq!(&one + &two, three, "`1 + 2` failed",);

  for (a, b,) in (-1000isize..1000).map(|n,| (n * n, n,),) {
    let target = SInt::from(a + b,);
    let num_b = SInt::from(b,);
    let num_a = SInt::from(a,);
    assert_eq!(num_a + num_b, target, "`{} + {}` failed", a, b,);
  }

  assert_eq!(&ten + SInt::ZERO, ten, "`10 - 0` failed",);

  let eight = SInt(UInt(vec![0b10000,],),);
  assert_eq!(&ten - &two, eight, "`10 - 2` failed",);

  for (a, b,) in (-1000isize..1000).map(|n,| (n * n, n,),) {
    let target = SInt::from(a - b,);
    let num_b = SInt::from(b,);
    let num_a = SInt::from(a,);
    assert_eq!(num_a - num_b, target, "`{} - {}` failed", a, b,);
  }
}

#[allow(non_snake_case,)]
#[test]
fn test_SInt_mul_div() {
  let one = SInt(UInt(vec![2],),);
  let two = SInt(UInt(vec![4,],),);
  let five = SInt(UInt(vec![0b1010,],),);
  let ten = SInt(UInt(vec![0b10100,],),);

  assert_eq!(&five * &SInt::ZERO, SInt::ZERO, "`5 * 0` failed",);
  assert_eq!(&ten * &one, ten, "`10 * 1` failed",);

  let twenty = SInt(UInt(vec![0b101000,],),);
  assert_eq!(&ten * &two, twenty, "`10 * 2` failed",);

  for (a, b,) in (-1000isize..1000).map(|n,| (n, n * n,),) {
    let target = SInt::from(a * b,);
    let num_b = SInt::from(b,);
    let num_a = SInt::from(a,);
    assert_eq!(num_a * num_b, target, "`{} * {}` failed", a, b,);
  }

  assert_eq!(&ten / &one, ten, "`10 / 1` failed",);

  let four = SInt(UInt(vec![0b1000,],),);
  assert_eq!(&twenty / &five, four, "`20 / 5` failed",);

  for (a, b,) in (-1000isize..0).chain(1isize..=1000,).map(|n,| (n * n.abs(), n,),) {
    let target = SInt::from(a / b,);
    let mut num_b = SInt::from(b,);
    let num_a = SInt::from(a,);
    let mut num = num_a.clone();
    SInt::rem(&mut num, num_b.into_slice_mut(),);
    assert_eq!(num, target, "`mul_bytes {} / {}` failed, got {}", a, b, num,);
    assert_eq!(num_a / num_b, target, "`{} / {}` failed", a, b,);
  }
}

#[allow(non_snake_case,)]
#[test]
fn test_SInt_rem() {
  let one = SInt(UInt(vec![2],),);
  let two = SInt(UInt(vec![4,],),);
  let ten = SInt(UInt(vec![0b10100,],),);
  let twenty = SInt(UInt(vec![0b101000,],),);

  let mut num = ten.clone();
  num %= 3;
  assert_eq!(num, one, "`10 % 3` failed, got {}", num,);

  let mut num = twenty.clone();
  num %= 3;
  assert_eq!(num, two, "`20 % 2` failed, got {}", num,);

  for (a, b,) in (-1000isize..0).chain(1isize..1000,).map(|n,| (n * n.abs(), n,),) {
    let target = SInt::from(a % b,);
    let num_a = SInt::from(a,);
    let mut num = num_a.clone();
    num %= b;
    assert_eq!(num, target, "`{} % {}` failed, got {}", a, b, num,);
    assert_eq!(num_a % b, target, "`{} % {}` failed", a, b,);
  }
}

#[allow(non_snake_case,)]
#[test]
fn test_SInt_display() {
  let five = SInt(UInt(vec![0b1010,],),);
  let ten = SInt(UInt(vec![0b10100,],),);
  let one_hundered = SInt(UInt(vec![0b11001000,],),);

  assert_eq!(format!("{}", five,), "5",);
  assert_eq!(format!("{}", ten,), "10",);
  assert_eq!(format!("{}", one_hundered,), "100",);

  for num in (-128isize..128).map(|n,| n * n.abs(),) {
    let int = SInt::from(num,);

    assert_eq!(
      format!("Dsp:{}, Dbg:{:?}, Dbg:{:#?},", int, int, int,),
      format!("Dsp:{}, Dbg:{:?}, Dbg:{:#?},", num, num, num,),
    );
  }
}
