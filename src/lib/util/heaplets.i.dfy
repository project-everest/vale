include "../../arch/x86/vale.i.dfy"
include "../collections/Sets.i.dfy"
include "../math/div_nonlinear.i.dfy"

module heaplets_i {

import opened x86_vale_heaplets_i = x86_vale_i
import opened Math__div_nonlinear_i_heaplets_i = Math__div_nonlinear_i
import opened Collections__Sets_i_heaplets_i = Collections__Sets_i

function RemoveBytes(addr:int, src:Heaplet, num_words:nat) : Heaplet
    requires src.ByteHeaplet?;
{
    var new_bytes := map a | a in src.bytes && (a < addr || a >= addr + 4*num_words) 
                          :: src.bytes[a];
    ByteHeaplet(new_bytes)
}

function AddWords(addr:int, src:Heaplet, dst:Heaplet, num_words:nat) : Heaplet
    requires src.ByteHeaplet?;
    requires forall a :: addr <= a < addr + 4*num_words && (a - addr) % 4 == 0
                      ==> a + 0 in src.bytes
                       && a + 1 in src.bytes
                       && a + 2 in src.bytes
                       && a + 3 in src.bytes;
{
    var words := map a | addr <= a < addr + 4*num_words && (a - addr) % 4 == 0 
                      :: WordHeapletEntry(
                            BytesToWord(src.bytes[a+3].v,
                                        src.bytes[a+2].v,
                                        src.bytes[a+1].v,
                                        src.bytes[a+0].v),
                            src.bytes[a].t);
    WordHeaplet(words)
}

function CastBytesToWords(addr:int, src:Heaplet, dst:Heaplet, num_words:nat) : (Heaplet, Heaplet)
    requires src.ByteHeaplet?;
    requires dst.WordHeaplet?;
    requires forall a :: addr <= a < addr + 4*num_words && (a - addr) % 4 == 0
                      ==> a + 0 in src.bytes
                       && a + 1 in src.bytes
                       && a + 2 in src.bytes
                       && a + 3 in src.bytes;
    ensures  var (new_src, new_dst) := CastBytesToWords(addr, src, dst, num_words);
             // We removed all of the specified bytes
             (forall a :: addr <= a < addr + num_words * 4 ==> a !in new_src.bytes)
             // But left the rest
          && (forall a {:trigger a in src.bytes} {:trigger a in new_src.bytes}
                       :: (a < addr || a  >= addr + num_words * 4) 
                       ==> if a in src.bytes then a in new_src.bytes && src.bytes[a] == new_src.bytes[a]
                           else a !in new_src.bytes)
{
    (RemoveBytes(addr, src, num_words), AddWords(addr, src, dst, num_words))
}


////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////
//
// Everything above is the core of doing the cast.
// Everything below is dealing with the x86vale wrappings.
//
////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////

lemma lemma_CastBytesToWords(heaplets:Heaplets, heap:heap, addr:int, B_id:heaplet_id, taint:taint, num_bytes:nat)
    returns (heaplets':Heaplets, W_id:heaplet_id)
    requires HeapletsExclusive(heaplets);
    requires HeapletsConsistent(heaplets, heap);
    requires ValidSrcAddrs(heaplets, B_id, addr, 8, taint, num_bytes); 

    requires 0 < num_bytes && num_bytes % 4 == 0;

    // Result
    ensures  HeapletsExclusive(heaplets');
    ensures  HeapletsConsistent(heaplets', heap);
    ensures  W_id !in heaplets && W_id in heaplets';
    ensures  var (new_bytes, new_words) := CastBytesToWords(addr, heaplets[B_id], WordHeaplet(map[]), num_bytes/4);
             heaplets' == heaplets[W_id := new_words][B_id := new_bytes];
    ensures  heaplets'[W_id].WordHeaplet?;
    ensures  ValidSrcAddrs(heaplets', W_id, addr, 32, taint, num_bytes); 
{
    reveal_x86_ValidState();

    var bytes := heaplets[B_id];
    var words := WordHeaplet(map []);

    // Do the actual cast
    var tuple := CastBytesToWords(addr, bytes, words, num_bytes / 4);
    var new_bytes, new_words := tuple.0, tuple.1;

    // Add the resulting word heaplet into the state, ensuring that it has a unique ID
    var heaplet_ids := set id | id in heaplets;
    W_id := pick_unused_int(heaplet_ids);
    heaplets' := heaplets[W_id := new_words][B_id := new_bytes];

    assert (num_bytes / 4)*4 == num_bytes;
    var num_words := num_bytes / 4;

    // Prove HeapletsConsistent 
    forall a, h_id | h_id in heaplets'
                  && ValidHeapletAddr(heaplets'[h_id], a)
        ensures ConsistentHeapletAddr(heaplets'[h_id], heap, a)
             && ConsistentHeapletValue(heaplets'[h_id], heap, a)
             && ConsistentHeapletTaint(heaplets'[h_id], heap, a);
    {
        if h_id == W_id {
//            assert addr <= a < addr + num_words * 4 && (a - addr) % 4 == 0;
            assert a in bytes.bytes;        // OBSERVE
            assert a+1 in bytes.bytes;      // OBSERVE
            assert a+2 in bytes.bytes;      // OBSERVE
            assert a+3 in bytes.bytes;      // OBSERVE
//            assert ConsistentHeapletTaint(heaplets'[h_id], heap, a);
//            assert ConsistentHeapletValue(heaplets'[h_id], heap, a);
        } else if h_id == B_id {
            assert ConsistentHeapletAddr(heaplets[h_id], heap, a);      // OBSERVE
//            assert ConsistentHeapletTaint(heaplets'[h_id], heap, a);
//            assert ConsistentHeapletValue(heaplets'[h_id], heap, a);
        } else {
//            assert ConsistentHeapletTaint(heaplets'[h_id], heap, a);
//            assert ConsistentHeapletValue(heaplets'[h_id], heap, a);
        }
    }

    // Prove HeapletsExclusive 
    forall a, h_id, h_id' | h_id in heaplets'
                         && h_id' in heaplets' 
                         && h_id != h_id'
                         && ValidHeapletAddr(heaplets'[h_id], a)
        ensures AddrExclusive(heaplets', h_id, h_id', a);
    {
        if h_id == W_id {
        } else if h_id == B_id {
            if h_id' == W_id {
            } else {
                assert AddrExclusive(heaplets, h_id, h_id', a);   // OBSERVE
            }
        } else {
        }
    }
}

lemma lemma_HeapletsExclusive_implication(s:State, addr:int, id:heaplet_id, id':heaplet_id)
    requires x86_ValidState(s);
    requires id in s.heaplets && id' in s.heaplets;
    requires AddrInHeaplet(addr, s.heaplets[id]);
    requires AddrInHeaplet(addr, s.heaplets[id']);
    ensures  id == id';
{
    reveal_x86_ValidState();
}
/*
//function GetBytesToWord(mem:Heaplets, bytes_id:heaplet_id, addr:int) : int
//    // We don't care about taint for this function's purposes, so call it a dst
//    requires ValidDstAddr(mem, bytes_id, addr,   8);
//    requires ValidDstAddr(mem, bytes_id, addr+1, 8);
//    requires ValidDstAddr(mem, bytes_id, addr+2, 8);
//    requires ValidDstAddr(mem, bytes_id, addr+3, 8);
//{
//    BytesToWord(mem[bytes_id].bytes[addr].v,
//                mem[bytes_id].bytes[addr+1].v,
//                mem[bytes_id].bytes[addr+2].v,
//                mem[bytes_id].bytes[addr+3].v)
//}
//
//function bswap32(x:uint32) : uint32 { 
//    var bytes := WordToBytes(x);
//    BytesToWord(bytes[3], bytes[2], bytes[1], bytes[0])
//}
//
//predicate ConsistentHeapletValue(h:Heaplet, H:heap, addr:int)
//    requires ConsistentHeapletAddr(h, H, addr);
//    requires ValidHeapletAddr(h, addr);
//{
//    match h
//        case WordHeaplet(w) => w[addr].v == BytesToWord(H[addr+3].v,
//                                                        H[addr+2].v,
//                                                        H[addr+1].v,
//                                                        H[addr].v)
//}
lemma lemma_bswap32_properties(b_mem:Heaplets, bytes_id:heaplet_id, m_mem:Heaplets, M_id:heaplet_id, addr:int, H:heap)
    requires ValidDstAddr(b_mem, bytes_id, addr,   8);
    requires ValidDstAddr(b_mem, bytes_id, addr+1, 8);
    requires ValidDstAddr(b_mem, bytes_id, addr+2, 8);
    requires ValidDstAddr(b_mem, bytes_id, addr+3, 8);
    requires ValidDstAddr(m_mem, M_id, addr, 32);
    requires HeapletsConsistent(b_mem, H);
    requires HeapletsConsistent(m_mem, H);
    ensures  GetBytesToWord(b_mem, bytes_id, addr) == bswap32(m_mem[M_id].words[addr].v);
{

    lemma_BytesToWord_WordToBytes_inverses(H[addr+3].v, H[addr+2].v, H[addr+1].v, H[addr].v);
//    calc {
//        GetBytesToWord(b_mem, bytes_id, addr);
//        BytesToWord(b_mem[bytes_id].bytes[addr].v,
//                    b_mem[bytes_id].bytes[addr+1].v,
//                    b_mem[bytes_id].bytes[addr+2].v,
//                    b_mem[bytes_id].bytes[addr+3].v);
//        BytesToWord(H[addr].v,
//                    H[addr+1].v,
//                    H[addr+2].v,
//                    H[addr+3].v);
//        var bytes := [H[addr+3].v,
//                      H[addr+2].v,
//                      H[addr+1].v,
//                      H[addr].v];
//        BytesToWord(bytes[3], bytes[2], bytes[1], bytes[0]);
//            { lemma_BytesToWord_WordToBytes_inverses(H[addr+3].v, H[addr+2].v, H[addr+1].v, H[addr].v); }
//        var bytes := WordToBytes(BytesToWord(H[addr+3].v,
//                           H[addr+2].v,
//                           H[addr+1].v,
//                           H[addr].v));
//        BytesToWord(bytes[3], bytes[2], bytes[1], bytes[0]);
//        bswap32(BytesToWord(H[addr+3].v,
//                            H[addr+2].v,
//                            H[addr+1].v,
//                            H[addr].v));
//        bswap32(m_mem[M_id].words[addr].v);
//    }
}
*/

} // end module heaplets_i

