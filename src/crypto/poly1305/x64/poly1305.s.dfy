include "../../../lib/math/power2.s.dfy"
include "../../../lib/math/bitvectors128.s.dfy"
include "../../../lib/util/operations.s.dfy"

module x64__Poly1305_s
{
import opened Math__power2_s
import opened bitvectors128_s
import opened operations_s

function{:opaque} modp(x:int):int
{
    x % (0x1_00000000_00000000_00000000_00000000 * 4 - 5)
}

function{:opaque} and128_opaque(x:uint128, y:uint128):uint128 { U128(bv128and(B128(x), B128(y))) }
function and128(x:uint128, y:uint128):uint128 { and128_opaque(x, y) }

// case for exact multiples of 16 bytes:
function{:opaque} poly1305_hash_blocks(h:int, pad:int, r:int, inp:map<int, uint128>, i:int, k:int):int
    requires i <= k
    requires (k - i) % 16 == 0
    requires forall j :: i <= j < k && (j - i) % 16 == 0 ==> j in inp
    decreases k - i
{
    if i == k then h
    else
        var kk := k - 16;
        var hh := poly1305_hash_blocks(h, pad, r, inp, i, kk);
        modp((hh + pad + inp[kk]) * r)
}

// general case:
function{:opaque} poly1305_hash(key_r:uint128, key_s:uint128, inp:map<int, uint128>, start:int, len:nat):int
    requires forall j :: start <= j < start + len && (j - start) % 16 == 0 ==> j in inp
{
    var r := and128(key_r, 0x0ffffffc_0ffffffc_0ffffffc_0fffffff);
    var nBlocks := len / 16;
    var nExtra := len % 16;
    var padBlocks := 0x1_00000000_00000000_00000000_00000000;
    var hBlocks := poly1305_hash_blocks(0, padBlocks, r, inp, start, start + 16 * nBlocks);
    if nExtra == 0 then
        mod2_128(hBlocks + key_s)
    else
        var k := start + 16 * nBlocks;
        var padLast := power2(nExtra * 8);
        var hLast := modp((hBlocks + padLast + (inp[k] % padLast)) * r);
        mod2_128(hLast + key_s)
}

}
