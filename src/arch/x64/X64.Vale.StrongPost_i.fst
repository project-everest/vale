module X64.Vale.StrongPost_i
open X64.Machine_s
open X64.Vale.State_i
open X64.Vale.Decls

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1 --z3rlimit 20"

let empty = ()

(*
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

let assert_from_norm' (p:Type0): Lemma
  (requires (Prims.norm [delta_only wp_code_delta; zeta; iota; primops] p))
  (ensures p)
  = ()

let assert_to_norm' (p:Type0): Lemma
  (requires p)
  (ensures (Prims.norm [delta_only wp_code_delta; zeta; iota; primops] p))
  = ()

let lemma_weak_pre_ins (i:ins) (inss:list ins) 
                   (s0:state) (sN:state) (post: unit -> Type) :
  Ghost (option state)
         (requires (s0.ok /\
            eval_code (va_Block (inss_to_codes (i::inss))) s0 sN) /\
            wp_code (i::inss) (augment sN post) s0)
     (ensures (fun sM ->
             match sM with
             | None -> False
             | Some sM ->
                eval_code (va_Block (inss_to_codes inss)) sM sN /\
                sM.ok /\
                wp_code inss (augment sN post) sM)) =
  let b0 = inss_to_codes (i::inss) in
  (* this results in:
   Not an embedded list: X64.Vale.StrongPost_i.wp_code_delta")
  let some_pre (sM:state) (p:Type0) : Ghost (option state)
    (requires p)
    (ensures fun _ -> Prims.norm [delta_only wp_code_delta; zeta; iota; primops] p) =
    assert_to_norm' p;
    Some sM
  in*)
  let _ = assert_to_norm'(wp_code (i::inss) (augment sN post) s0) in
  match i with
  | Mov64 (OReg dst) src ->
      if dst <> Rsp && valid_operand_norm src s0 then
        let (bM, sM) = va_lemma_Mov64 b0 s0 sN (OReg dst) src in
        Some sM
      else 
        None
  | Load64 (OReg dst) (OReg src) offset ->
      if dst <> Rsp && valid_src_addr s0.mem (s0.regs src + offset) then
        let (bM, sM) = va_lemma_Load64 b0 s0 sN (OReg dst) (OReg src) offset in
        Some sM
      else
        None
  | Store64 (OReg dst) src offset ->
      if valid_dst_addr s0.mem (s0.regs dst + offset) && valid_operand_norm src s0 then
        let (bM, sM) = va_lemma_Store64 b0 s0 sN (OReg dst) src offset in
        Some sM
      else
        None
  | Add64Wrap (OReg dst) src ->
      if dst <> Rsp && valid_operand_norm src s0 then
        let (bM, sM) = va_lemma_Add64Wrap b0 s0 sN (OReg dst) src in
        Some sM
      else
        None
  | Adc64Wrap (OReg dst) src ->
      if dst <> Rsp && valid_operand_norm src s0 then
        let (bM, sM) = va_lemma_Adc64Wrap b0 s0 sN (OReg dst) src in
        Some sM
      else
        None
  | Mul64Wrap src ->
      if valid_operand_norm src s0 then
        let (bM, sM) = va_lemma_Mul64Wrap b0 s0 sN src in
        Some sM
      else
        None
  | IMul64 (OReg dst) src ->
      let a = s0.regs dst `op_Multiply` eval_operand_norm src s0 in
      if dst <> Rsp && valid_operand_norm src s0 && a < pow2_64 then
        let (bM, sM) = va_lemma_IMul64 b0 s0 sN (OReg dst) src in
        Some sM
      else
        None
  | And64 (OReg dst) src ->
    let a = logand64 (s0.regs dst) (eval_operand_norm src s0) in
    if dst <> Rsp && valid_operand_norm src s0 then
      let (bM, sM) = va_lemma_And64 b0 s0 sN (OReg dst) src in
        Some sM
      else
        None
  | Shr64 (OReg dst) src ->
    let a = shift_right64 (s0.regs dst) (eval_operand_norm src s0) in
    if dst <> Rsp && valid_operand_norm src s0 then
      let (bM, sM) = va_lemma_Shr64 b0 s0 sN (OReg dst) src in
        Some sM
      else
        None
  | Sub64 (OReg dst) src ->
    if dst <> Rsp && valid_operand_norm src s0 && 0 <= 
            (s0.regs dst) - (eval_operand_norm src s0) then
      let (bM, sM) = va_lemma_Sub64 b0 s0 sN (OReg dst) src in
        Some sM
      else
        None
  | _ -> None


 let rec lemma_weak_pre (inss:list ins) (s0:state) (sN:state) (post: unit -> Type0) : Lemma
  (requires
    eval_code (va_Block (inss_to_codes inss)) s0 sN /\
    s0.ok /\
    wp_code inss (augment sN post) s0)
  (ensures
    post ())
   =
  match inss with
  | [] ->
      let _ = va_lemma_empty s0 sN in
      let regs = [Rax; Rbx; Rcx; Rdx; Rsi; Rdi; Rbp; 
          Rsp; R8; R9; R10; R11; R12; R13; R14; R15] in
      lemma_regs_match_self regs s0;
      assert_to_norm'(wp_code [] (augment sN post) s0);
      ()
  | i::inss ->
    ( 
      match lemma_weak_pre_ins i inss s0 sN post with
      | None -> assert(post ())
      | Some sM -> lemma_weak_pre inss sM sN post
    )

let lemma_weakest_pre_norm' (inss:list ins) (s0:state) (f0:va_fuel) (sN:state) (#post:unit -> Type0) :
  Lemma (requires
      (forall ok0 regs0 flags0 mem0.
             ok0 == s0.ok /\
             regs0 == s0.regs /\
             flags0 == s0.flags /\
             mem0 == s0.mem ==>
        s0.ok /\
        eval_code (va_Block (normalize_term (inss_to_codes inss))) s0 f0 sN /\
        Prims.norm [delta_only wp_code_delta; zeta; iota; primops]
               (wp_code (normalize_term inss) (augment sN post)
                   ({ok=ok0; regs=regs0; flags=flags0; mem=mem0}))))
    (ensures (post ())) = 
  assert_from_norm' (wp_code inss (augment sN post) s0);
  lemma_weak_pre inss s0 sN post
*)

let va_lemma_weakest_pre_norm inss s0 f0 =
  admit () // connect with proof above
