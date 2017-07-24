module FStar.UInt.Vectors
open FStar.UInt.Types

val logand: (#n:pos) -> (a:uint_t n) -> (b:uint_t n) -> Tot (uint_t n)
val logxor: (#n:pos) -> (a:uint_t n) -> (b:uint_t n) -> Tot (uint_t n)
val logor: (#n:pos) -> (a:uint_t n) -> (b:uint_t n) -> Tot (uint_t n)
val lognot: (#n:pos) -> (a:uint_t n) -> Tot (uint_t n)

val shift_left: (#n:pos) -> (a:uint_t n) -> (s:nat) -> Tot (uint_t n) 
val shift_right: (#n:pos) -> (a:uint_t n) -> (s:nat) -> Tot (uint_t n)
