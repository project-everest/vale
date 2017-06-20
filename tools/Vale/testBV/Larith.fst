module Larith

open FStar.BaseTypes
// val bound : pos
// val max_nat : nat
// val max_nat_correct: Lemma (max_nat == pow2 bound)
// type bounded_nat = x:nat{x < max_nat}

abstract
let logxor (#n : pos) (x:int) (y:int) : res:nat{res < pow2 n} =
  if FStar.UInt.fits x n
  && FStar.UInt.fits y n
  then FStar.UInt.logxor #n x y
  else 0

let logxor_uint  (#n:pos) (x:int) (y:int)
  : Lemma (ensures (FStar.UInt.fits x n /\
                    FStar.UInt.fits y n) ==>
                    logxor #n x y = FStar.UInt.logxor #n x y)
           [SMTPat (logxor #n x y)]
  = ()          

// abstract
// let logand (#n:pos) (x:int) (y:int) : nat64 =
//   if FStar.UInt.fits x n
//   && FStar.UInt.fits y n
//   then FStar.UInt.logand #n x y
//   else 0

// let logand_uint64 (x:int) (y:int)
//   : Lemma (ensures (FStar.UInt.fits x 64 /\
//                     FStar.UInt.fits y 64) ==>
//                     logand x y = FStar.UInt.logand #64 x y)
//           [SMTPat (logand x y)]
//   = ()          

// abstract
// let shift_right (x:int) (y:int) : nat64 =
//   if FStar.UInt.fits x 64
//   && y >= 0
//   then FStar.UInt.shift_right #64 x y
//   else 0

// let shift_right_uint64 (x:int) (y:int)
//   : Lemma (ensures (FStar.UInt.fits x 64 /\
//                     0 <= y /\
//                     y < 64 ==>
//                     shift_right x y = FStar.UInt.shift_right #64 x y))
//           [SMTPat (shift_right x y)]
//   = ()          

// abstract
// let shift_left (x:int) (y:int) : nat64 =
//   if FStar.UInt.fits x 64
//   && y >= 0
//   then FStar.UInt.shift_left #64 x y
//   else 0

// let shift_left_uint64 (x:int) (y:int)
//   : Lemma (ensures (FStar.UInt.fits x 64 /\
//                     0 <= y /\
//                     y < 64 ==>
//                     shift_left x y = FStar.UInt.shift_left #64 x y))
//           [SMTPat (shift_left x y)]
//   = (
