module X64.Vale.InsLemmas_i

open X64.Vale.StateLemmas_i
open X64.Taint_Semantics_i

let lemma_valid_taint64_operand m t s =
  let open X64.Taint_Semantics_s in
  let tainted_mem:X64.Memory_i_s.memtaint = (state_to_S s).memTaint in
  let real_mem:X64.Memory_i_s.mem = s.mem in
  Meta.exists_elim2
    (Map.sel tainted_mem (eval_maddr m s) == t)
    ()
    (fun (b:X64.Memory_i.buffer64) (index:nat{valid_maddr (eval_maddr m s) real_mem tainted_mem b index t}) ->
      lemma_valid_taint64 b tainted_mem real_mem index t)

