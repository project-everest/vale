include "aes.s.dfy"

// Derived from NIST Special Publication 800-38D
// http://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38d.pdf

module GCM {

import opened AESModule

function {:axiom} BlockMul(X:Quadword, Y:Quadword) : Quadword

function GHASH(H:Quadword, X:seq<Quadword>) : Quadword
    requires |X| > 0;
{
    if |X| == 1 then
        var  Y_0 := Quadword(0, 0, 0, 0);
        BlockMul(QuadwordXor(Y_0, X[0]), H)
    else
        var Y_i_minus_1 := GHASH(H, all_but_last(X));
        BlockMul(QuadwordXor(Y_i_minus_1, last(X)), H)

}

/*
function BytesToQuads(bytes:seq<uint8>) : (seq<Quadword>, seq<uint8>)
{
    if |bytes| < 16 then ([], bytes)
    else
        var q := Quadword(
            BytesToWord(bytes[12], bytes[13], bytes[14], bytes[15]),
            BytesToWord(bytes[ 8], bytes[ 9], bytes[10], bytes[11]),
            BytesToWord(bytes[ 4], bytes[ 5], bytes[ 6], bytes[ 7]),
            BytesToWord(bytes[ 0], bytes[ 1], bytes[ 2], bytes[ 3]));
        var (rest_q, rest_bytes) := BytesToQuads(bytes[16..]);
        ([q] + rest_q, rest_bytes)
}
*/

function inc32(cb_i_minus_1:Quadword) : Quadword
{
    cb_i_minus_1.(lo := (cb_i_minus_1.lo + 1) % 0x1_0000_0000)
}

function ComputeCB(i:int, CB_1:Quadword) : Quadword
{
    if i <= 1 then CB_1 else inc32(ComputeCB(i-1, CB_1))
}

function {:autoReq} ComputeYs(i:int, key:seq<uint32>, X:seq<Quadword>, CB_1:Quadword) : seq<Quadword>
    decreases |X|;
    ensures |ComputeYs(i, key, X, CB_1)| == |X|
{
    if |X| == 0 then []
    else [QuadwordXor(X[0], AES_Encrypt(key, ComputeCB(i, CB_1), AES_128))] + ComputeYs(i+1, key, X[1..], CB_1)
}
/*
function byte_xor(x:uint8, y:uint8) : uint8 
function bytewise_xor(us:seq<uint8>, them:seq<uint8>) : seq<uint8>
    requires |us| == |them|;
{
    if us == [] then [] else [byte_xor(us[0], them[0])] + bytewise_xor(us[1..], them[1..])
}

function Quadword_to_bytes(q:Quadword) : seq<uint8>
{
    WordToBytes(q.lo) + WordToBytes(q.mid_lo) + WordToBytes(q.mid_hi) + WordToBytes(q.hi)
}

function Quadwords_to_bytes(q:seq<Quadword>) : seq<uint8>
{
    if q == [] then [] else Quadword_to_bytes(q[0]) + Quadwords_to_bytes(q[1..])
}

function {:autoReq} GCTR(key:seq<uint32>, ICB:Quadword, X_bytes:seq<uint8>) : seq<uint8>
{
    var (X_1_to_n_minus_1, X_n) := BytesToQuads(X_bytes);
    var n := |X_1_to_n_minus_1| + 1;
    var CB_1 := ICB;
    var Y_1_to_n_minus_1 := ComputeYs(1, key, X_1_to_n_minus_1, CB_1);
    var Y_n := bytewise_xor(X_n, Quadword_to_bytes(AES_Encrypt(key, ComputeCB(n, CB_1), AES_128))[..|X_n|]);
    var bytes := Quadwords_to_bytes(Y_1_to_n_minus_1) + Y_n;
    bytes
}
*/

function {:autoReq} GCTR_quad(key:seq<uint32>, ICB:Quadword, X:seq<Quadword>) : seq<Quadword>
    ensures |GCTR_quad(key, ICB, X)| == |X|
{
    // If X is the empty string, then below, Y will be the empty string
    //var n := |X|;
    var CB_1 := ICB;
    var Y := ComputeYs(1, key, X, CB_1);
    Y
}

function {:autoReq} GCM_AE_qad(key:seq<uint32>, IV:Quadword, plaintext:seq<Quadword>, additional_data:seq<Quadword>) : (seq<Quadword>, Quadword)
    // Spec says we're allowed to accept less than max length
    requires |plaintext|*128 < 0x1_0000_0000; //<= power2(39) - 256;
    requires |additional_data|*128 < 0x1_0000_0000; //0x1_0000_0000_0000_0000;
{
    var H := AES_Encrypt(key, Quadword(0, 0, 0, 0), AES_128);
    var J_0 := IV.(lo := 1);        // Consider the top 96 bits of the IV quadword to be the "real" IV
    var C := GCTR_quad(key, inc32(J_0), plaintext);
    var lengths := Quadword(|C|*128, 0, |additional_data|*128, 0);
    var S := GHASH(H, additional_data + C + [lengths]);
    var T := GCTR_quad(key, J_0, [S])[0];
    (C, T)
}

/*
function GCM_AE(key:seq<uint32>, IV:Quadword, plaintext:seq<uint8>, additional_data:seq<Quadword>) : (seq<Quadword>, Quadword)
    requires |plaintext|*128 < 0x1_0000_0000; //<= power2(39) - 256;
    requires |additional_data|*128 < 0x1_0000_0000_0000_0000;
{
    var H := AES_Encrypt(key, Quadword(0, 0, 0, 0), AES_128);
    var J_0 := IV.(lo := 1);
    var C := GCTR(key, inc32(J_0), plaintext);
    var S := GHASH(H, additional_data + C + zero_pad + lengths);
    var T := GCTR(key, J_0, S);
    (C, T)
}
*/

}
