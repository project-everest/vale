module X64.Semantics_Equiv_i

module S = X64.Bytes_Semantics_s
open X64.Memory_i_s
open X64.Semantics_s

val equiv_eval_ins (s:state) (ins:S.ins) : Lemma (
   let s_hi = run (eval_ins ins) s in
   let s_bytes = S.run (S.eval_ins ins) s.state in
   s_hi.state.S.ok /\ s_bytes.S.ok ==> s_hi.state == s_bytes)

// val equiv_eval_code (s:state) (fuel:nat) (code:code) : Lemma (
//   let s_hi = eval_code code fuel s in
//   let s_bytes = S.eval_code code fuel s.state in
//     (None? s_hi /\ None? s_bytes) \/
//   ( Some? s_hi /\ Some? s_bytes /\ 
//     ((Some?.v s_hi).state.S.ok /\ (Some?.v s_bytes).S.ok ==> 
//     (Some?.v s_hi).state == Some?.v s_bytes
//   ))
// )
