module X64.Vale.StrongPost_i
open X64.Machine_s
open X64.Vale.State_i
open X64.Vale.Decls

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 20"

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

let lemma_update_reg_equal (r:reg) (v:nat64) (s1:state) (s2:state) : Lemma
  (requires (Regs_i.equal (update_reg r v s1).regs s2.regs))
  (ensures ((update_reg r v s1).regs == s2.regs)) =
  ()

let lemma_strong_post_ins (i:ins) (inss:list ins) (s0:state) (sN:state) : Ghost (option state)
  (requires
    Some sN == va_eval_code (va_Block (inss_to_codes (i::inss))) s0 /\
    s0.ok)
  (ensures (fun sM ->
    match sM with
    | None -> strong_post (i::inss) s0 sN
    | Some sM ->
        Some sN == va_eval_code (va_Block (inss_to_codes inss)) sM /\
        sM.ok /\
        (strong_post inss sM sN ==> strong_post (i::inss) s0 sN))) =
  let b0 = inss_to_codes (i::inss) in
  let none_post () : Ghost (option state)
    (requires normalize (strong_post (i::inss) s0 sN))
    (ensures fun _ -> strong_post (i::inss) s0 sN) =
    assert_norm (strong_post (i::inss) s0 sN);
    None
    in
  let some_post_helper (sM:state) (p:Type0) : Ghost (option state)
    (requires strong_post inss sM sN ==> normalize p)
    (ensures fun _ -> strong_post inss sM sN ==> p) =
    Some sM
    in
  let some_post (sM:state) : Ghost (option state)
    (requires strong_post inss sM sN ==> normalize (strong_post (i::inss) s0 sN))
    (ensures fun _ -> strong_post inss sM sN ==> strong_post (i::inss) s0 sN) =
    some_post_helper sM (strong_post (i::inss) s0 sN)
    in
  match i with
  | Mov64 (OReg dst) src ->
      if dst <> Rsp && valid_operand_norm src s0 then
        let (bM, sM) = va_lemma_Mov64 b0 s0 sN (OReg dst) src in
        some_post sM
      else none_post ()
  | Load64 (OReg dst) (OReg src) offset ->
      if dst <> Rsp && valid_src_addr s0.mem (s0.regs src + offset) then
        let (bM, sM) = va_lemma_Load64 b0 s0 sN (OReg dst) (OReg src) offset in
        some_post sM
      else none_post ()
  | Store64 (OReg dst) src offset ->
      if valid_dst_addr s0.mem (s0.regs dst + offset) && valid_operand_norm src s0 then
        let (bM, sM) = va_lemma_Store64 b0 s0 sN (OReg dst) src offset in
        some_post sM
      else none_post ()
  | Add64Wrap (OReg dst) src ->
      if dst <> Rsp && valid_operand_norm src s0 then
        let (bM, sM) = va_lemma_Add64Wrap b0 s0 sN (OReg dst) src in
        some_post sM
      else none_post ()
  | Adc64Wrap (OReg dst) src ->
      if dst <> Rsp && valid_operand_norm src s0 then
        let (bM, sM) = va_lemma_Adc64Wrap b0 s0 sN (OReg dst) src in
        some_post sM
      else none_post ()
  | Mul64Wrap src ->
      if valid_operand_norm src s0 then
        let (bM, sM) = va_lemma_Mul64Wrap b0 s0 sN src in
        some_post sM
      else none_post ()
  | IMul64 (OReg dst) src ->
      let a = s0.regs dst `op_Multiply` eval_operand_norm src s0 in
      if dst <> Rsp && valid_operand_norm src s0 && a < nat64_max then
        let (bM, sM) = va_lemma_IMul64 b0 s0 sN (OReg dst) src in
        some_post sM
      else none_post ()
  | And64 (OReg dst) src ->
    let a = logand64 (s0.regs dst) (eval_operand_norm src s0) in
    if dst <> Rsp && valid_operand_norm src s0 then
      let (bM, sM) = va_lemma_And64 b0 s0 sN (OReg dst) src in
      some_post sM
    else none_post ()
  | Shr64 (OReg dst) src ->
    let a = shift_right64 (s0.regs dst) (eval_operand_norm src s0) in
    if dst <> Rsp && valid_operand_norm src s0 then
      let (bM, sM) = va_lemma_Shr64 b0 s0 sN (OReg dst) src in
      some_post sM
    else none_post ()
  | Sub64 (OReg dst) src ->
    if dst <> Rsp && valid_operand_norm src s0 && 0 <= (s0.regs dst) - (eval_operand_norm src s0) then
      let (bM, sM) = va_lemma_Sub64 b0 s0 sN (OReg dst) src in
      some_post sM
    else none_post ()
  | _ -> assume false; None

let rec lemma_strong_post (inss:list ins) (s0:state) (sN:state) : Lemma
  (requires
    Some sN == va_eval_code (va_Block (inss_to_codes inss)) s0 /\
    s0.ok)
  (ensures
    strong_post inss s0 sN) =
  match inss with
  | [] ->
      let _ = va_lemma_empty s0 sN in
      let regs = [Rax; Rbx; Rcx; Rdx; Rsi; Rdi; Rbp; Rsp; R8; R9; R10; R11; R12; R13; R14; R15] in
      lemma_regs_match_self regs s0;
      assert_norm (strong_post inss s0 sN);
      ()
  | i::inss ->
    (
      match lemma_strong_post_ins i inss s0 sN with
      | None -> ()
      | Some sM -> lemma_strong_post inss sM sN
    )

let assert_to_norm (p:Type0) : Lemma
  (requires p)
  (ensures (normalize p))
  = ()

let va_lemma_strong_post_norm inss s0 sN =
  lemma_strong_post inss s0 sN;
  assert_to_norm (strong_post inss s0 sN);
  ()

let lemma_weakest_pre_norm inss s0 = admit ()
