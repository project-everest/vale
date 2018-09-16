module types {

/////////////////
// Native types
/////////////////

newtype{:nativeType "byte"} byte = i:int | 0 <= i < 0x100
newtype{:nativeType "uint"} uint = i:int | 0 <= i < 0x1_0000_0000
newtype{:nativeType "ulong"} ulong = i:int | 0 <= i < 0x1_0000_0000_0000_0000

/////////////////
// Subset types
/////////////////

type uint8   = i:int | 0 <= i < 0x100
type uint16  = i:int | 0 <= i < 0x10000
type uint32  = i:int | 0 <= i < 0x1_0000_0000
type uint64  = i:int | 0 <= i < 0x1_0000_0000_0000_0000
type uint128 = i:int | 0 <= i < 0x1_00000000_00000000_00000000_00000000

/////////////////
// Quadword
/////////////////

datatype Quadword = Quadword(lo:uint32, mid_lo:uint32, mid_hi:uint32, hi:uint32)

/////////////////
// BitsOfByte
/////////////////

newtype twobits = i:int | 0 <= i < 4
datatype BitsOfByte = BitsOfByte(lo:twobits,
                                 mid_lo:twobits,
                                 mid_hi:twobits,
                                 hi:twobits)

function bits_to_byte(bits:BitsOfByte) : uint8
{
    64 * (bits.hi as uint8) + 16 * (bits.mid_hi as uint8) + 4 * (bits.mid_lo as uint8) + (bits.lo as uint8)
}

function byte_to_bits(b:uint8) : BitsOfByte
{
    BitsOfByte((b % 4) as twobits, ((b / 4) % 4) as twobits, ((b / 16) % 4) as twobits, ((b / 64) % 4) as twobits)
}

/////////////////
// Bit vectors
/////////////////

function method {:opaque} BitsToWord(b:bv32) : uint32 { b as uint32 }
function method {:opaque} WordToBits(w:uint32) : bv32 { w as bv32 }

lemma {:axiom} lemma_BitsToWordToBits(b:bv32)
    ensures WordToBits(BitsToWord(b)) == b;

lemma {:axiom} lemma_WordToBitsToWord(w:uint32)
    ensures BitsToWord(WordToBits(w)) == w;

function method {:opaque} BitsToWord64(b:bv64) : uint64 { b as uint64 }
function method {:opaque} WordToBits64(w:uint64) : bv64 { w as bv64 }

lemma {:axiom} lemma_BitsToWordToBits64(b:bv64)
    ensures WordToBits64(BitsToWord64(b)) == b;

lemma {:axiom} lemma_WordToBitsToWord64(w:uint64)
    ensures BitsToWord64(WordToBits64(w)) == w;

} // end module types
