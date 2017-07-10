module X64.Vale.StrongPost_i
open X64.Machine_s
open X64.Vale.State_i
open X64.Vale.Decls

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

// REVIEW: Hide polymorphic Map functions behind monomorphic functions
// until we have a better way to prevent the nat64 type argument from getting normalized
let mem_contains m i = Map.contains m i
let mem_sel m i = Map.sel m i
let mem_upd m i n = Map.upd m i n

let lemma_mem_contains m i = ()
let lemma_mem_sel m i = ()
let lemma_mem_upd m i n = ()

let rec lemma_regs_match_self (regs:list reg) (s:state) : Lemma
  (requires True)
  (ensures (regs_match regs s s)) =
  match regs with
  | [] -> ()
  | r::regs -> lemma_regs_match_self regs s

let rec lemma_strong_post (inss:list ins) (s0:state) (sN:state) : Lemma
  (requires
    Some sN == va_eval_code (va_Block (inss_to_codes inss)) s0 /\
    s0.ok)
  (ensures
    strong_post inss s0 sN) =
  let b0 = inss_to_codes inss in
  match inss with
  | [] ->
      let _ = va_lemma_empty s0 sN in
      let regs = [Rax; Rbx; Rcx; Rdx; Rsi; Rdi; Rbp; Rsp; R8; R9; R10; R11; R12; R13; R14; R15] in
      lemma_regs_match_self regs s0;
      ()
  | (Load64 (OReg dst) (OReg src) offset)::inss ->
      if dst <> Rsp && valid_src_addr s0.mem (s0.regs src + offset) then
        let (bM, sM) = va_lemma_Load64 b0 s0 sN (OReg dst) (OReg src) offset in
        lemma_strong_post inss sM sN
      else ()
  | (Store64 (OReg dst) (OReg src) offset)::inss ->
      if valid_dst_addr s0.mem (s0.regs dst + offset) then
        let (bM, sM) = va_lemma_Store64 b0 s0 sN (OReg dst) (OReg src) offset in
        lemma_strong_post inss sM sN
      else ()
  | _ -> ()

let assert_to_norm (p:Type0) : Lemma
  (requires p)
  (ensures (normalize p))
  = ()

let va_lemma_strong_post_norm inss s0 sN =
  lemma_strong_post inss s0 sN;
  assert_to_norm (strong_post inss s0 sN);
  ()

