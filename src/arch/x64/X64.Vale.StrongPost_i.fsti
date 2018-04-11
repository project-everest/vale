module X64.Vale.StrongPost_i
open X64.Machine_s
open X64.Vale.State_i
open X64.Vale.Decls

#reset-options "--z3rlimit 20"

val empty : unit //annoying

type ins =
  | Mov64 : dst:va_operand -> src:va_operand -> ins
  | Load64_buffer : dst:va_operand -> src:va_operand -> offset:int -> ins
  | Store64_buffer : dst:va_operand -> src:va_operand -> offset:int -> ins
  | Add64Wrap : dst:va_operand -> src:va_operand -> ins
  | Adc64Wrap : dst:va_operand -> src:va_operand -> ins
  | Mul64Wrap : src:va_operand -> ins
  | IMul64 : dst:va_operand -> src:va_operand -> ins
  | And64 : dst:va_operand -> amt:va_operand -> ins
  | Shr64 : dst:va_operand -> amt:va_operand -> ins
  | Sub64 : dst:va_operand -> src:va_operand -> ins

unfold let va_fast_ins_Mov64 = Mov64
unfold let va_fast_ins_Load64_buffer = Load64_buffer
unfold let va_fast_ins_Store64_buffer = Store64_buffer
unfold let va_fast_ins_Add64Wrap = Add64Wrap
unfold let va_fast_ins_Adc64Wrap = Adc64Wrap
unfold let va_fast_ins_Mul64Wrap = Mul64Wrap
unfold let va_fast_ins_IMul64 = IMul64
unfold let va_fast_ins_And64 = And64
unfold let va_fast_ins_Shr64 = Shr64
unfold let va_fast_ins_Sub64 = Sub64

unfold let va_inss = list ins

[@va_qattr]
let valid_maddr_norm (addr:maddr) (s:state) : bool =
  //Map.contains s.mem (eval_maddr addr s)
  valid_mem64 (eval_maddr addr s) s.mem

[@va_qattr]
let valid_operand_norm (o:operand) (s:state) : bool =
    match o with
    | OConst n -> 0 <= n && n < pow2_64
    | OReg r -> true
    | OMem m -> valid_maddr_norm m s

[@va_qattr]
let eval_operand_norm (o:operand) (s:state) : nat64 =
  match o with
  | OConst n -> if 0 <= n && n < pow2_64 then n else 0
  | OReg r -> s.regs r
  | OMem m -> load_mem64 (eval_maddr m s) s.mem
             //Map.sel s.mem (eval_maddr m s)

[@va_qattr]
let rec regs_match (regs:list reg) (s0:state) (s1:state) =
  match regs with
  | [] -> True
  | r::regs -> s0.regs r == s1.regs r /\ regs_match regs s0 s1

[@va_qattr]
let all_regs_match (s0:state) (s1:state) =
  let regs = [Rax; Rbx; Rcx; Rdx; Rsi; Rdi; Rbp; Rsp; R8; 
              R9; R10; R11; R12; R13; R14; R15] in
  regs_match regs s0 s1

let rec inss_to_codes (inss:list ins) : list va_code =
  match inss with
  | (Mov64 (OReg Rsp) _)::inss -> []
  | (Mov64 (OReg dst) src)::inss -> (va_code_Mov64 (OReg dst) src)::(inss_to_codes inss)
  | (Load64_buffer (OReg Rsp) _ _)::inss -> []
  | (Load64_buffer (OReg dst) (OReg src) offset)::inss ->
    (va_code_Load64_buffer (OReg dst) (OReg src) offset)::(inss_to_codes inss)
  | (Store64_buffer (OReg dst) src offset)::inss -> 
    (va_code_Store64_buffer (OReg dst) src offset)::(inss_to_codes inss)
  | (Add64Wrap (OReg Rsp) _)::inss -> []
  | (Add64Wrap (OReg dst) src)::inss -> 
    (va_code_Add64Wrap (OReg dst) src)::(inss_to_codes inss)
  | (Adc64Wrap (OReg Rsp) _)::inss -> []
  | (Adc64Wrap (OReg dst) src)::inss -> 
    (va_code_Adc64Wrap (OReg dst) src)::(inss_to_codes inss)
  | (Mul64Wrap src)::inss -> (va_code_Mul64Wrap src)::(inss_to_codes inss)
  | (IMul64 (OReg Rsp) _)::inss -> []
  | (IMul64 (OReg dst) src)::inss -> (va_code_IMul64 (OReg dst) src)::(inss_to_codes inss)
  | (And64 (OReg Rsp) _)::inss -> []
  | (And64 (OReg dst) src)::inss -> (va_code_And64 (OReg dst) src)::(inss_to_codes inss)
  | (Shr64 (OReg Rsp) _)::inss -> []
  | (Shr64 (OReg dst) src)::inss -> (va_code_Shr64 (OReg dst) src)::(inss_to_codes inss)
  | (Sub64 (OReg Rsp) _)::inss -> []
  | (Sub64 (OReg dst) src)::inss -> (va_code_Sub64 (OReg dst) src)::(inss_to_codes inss)
  | _ -> []

[@va_qattr]
let augment (c:va_code) (s0:state) (f0:va_fuel) (post:state -> Type0) (sN:state) : Type0 =
  eval_code c s0 f0 sN ==> post sN

[@"opaque_to_smt" va_qattr]
let rec wp_code (inss : list ins) (post: state -> Type0) (s0:state) : Type0 =
  match inss with
  | [] ->
       (forall okN regsN flagsN memN.
       let sN = {ok=okN; regs=regsN; flags=flagsN; mem=memN} in
       okN == s0.ok /\
       memN == s0.mem /\
       flagsN == s0.flags /\
       all_regs_match s0 sN ==>
       post sN)
  | hd :: inss ->
    begin
      match hd with
      | (Mov64 (OReg Rsp) _) -> False
      | (Mov64 (OReg dst) src) ->
	      valid_operand_norm src s0 /\
	      (forall x. x == eval_operand_norm src s0 ==>
              wp_code inss post (update_reg dst x s0))
      | (Load64_buffer (OReg Rsp) _ _) -> False
      | (Load64_buffer (OReg dst) (OReg src) offset) ->
        valid_maddr_norm (MConst (s0.regs src + offset)) s0 /\
        (forall x. x == eval_mem (s0.regs src + offset) s0 ==>
                       //load_mem64 (s0.regs src + offset) s0.mem ==>
                       //Map.sel s0.mem (s0.regs src + offset) ==>
                  wp_code inss post (update_reg dst x s0))
      | (Store64_buffer (OReg dst) src offset) ->
        (valid_operand_norm src s0) /\
              (valid_mem64 (s0.regs dst + offset) s0.mem) /\
        //(Map.contains s0.mem (s0.regs dst + offset)) /\
        (forall x.
          //x == Map.upd s0.mem (s0.regs dst + offset) (eval_operand_norm src s0) ==>
                x == update_mem (s0.regs dst + offset) (eval_operand_norm src s0) s0 ==>
          wp_code inss post ({s0 with mem = x.mem}))
      | (Add64Wrap (OReg Rsp) _) -> False
      | (Add64Wrap (OReg dst) src) ->
          (valid_operand_norm src s0) /\
          (forall a x (f:nat64).
            a == s0.regs dst + eval_operand_norm src s0 /\
            x == (if a < pow2_64 then a else a - pow2_64) /\
            cf f == (a >= pow2_64) ==>
            wp_code inss post ({update_reg dst x s0 with flags = f}))
      | (Adc64Wrap (OReg Rsp) _) -> False
      | (Adc64Wrap (OReg dst) src) ->
          (valid_operand_norm src s0) /\
          (forall a x (f:nat64).
            a == s0.regs dst + eval_operand_norm src s0 + (if cf s0.flags then 1 else 0) /\
            x == (if a < pow2_64 then a else a - pow2_64) /\ cf f == (a >= pow2_64) ==>
            wp_code inss post ({update_reg dst x s0 with flags = f}))
      | (Mul64Wrap src) ->
          (valid_operand_norm src s0) /\
          (forall (rax:nat64) (rdx:nat64) (f:nat64).
            pow2_64 `op_Multiply` rdx + rax == s0.regs Rax `op_Multiply` eval_operand_norm src s0 ==>
            wp_code inss post (update_reg Rdx rdx (update_reg Rax rax ({s0 with flags = f}))))
      | (IMul64 (OReg Rsp) _) -> False
      | (IMul64 (OReg dst) src) ->
          let a = s0.regs dst `op_Multiply` eval_operand_norm src s0 in
          (valid_operand_norm src s0) /\
          (a < pow2_64) /\ //TODO:label this
          (forall (x:nat64) (f:nat64).
            x == a ==>
            wp_code inss post ({update_reg dst x s0 with flags = f}))
      | (And64 (OReg Rsp) _) -> False
      | (And64 (OReg dst) src) ->
          let a = logand64 (s0.regs dst) (eval_operand_norm src s0) in
          (valid_operand_norm src s0) /\
          (forall (x:nat64) (f:nat64).
            x == a ==>
            wp_code inss post ({update_reg dst x s0 with flags = f}))
      | (Shr64 (OReg Rsp) _) -> False
      | (Shr64 (OReg dst) src) ->
          let a = shift_right64 (s0.regs dst) (eval_operand_norm src s0) in
          (valid_operand_norm src s0) /\
          (forall (x:nat64) (f:nat64).
            x == a ==>
            wp_code inss post ({update_reg dst x s0 with flags = f}))
      | (Sub64 (OReg Rsp) _) -> False
      | (Sub64 (OReg dst) src) ->
          (valid_operand_norm src s0) /\
          (0 <= s0.regs dst - eval_operand_norm src s0) /\
          (forall a x (f:nat64).
            a == s0.regs dst - eval_operand_norm src s0 /\
            x == a ==>
            wp_code inss post ({update_reg dst x s0 with flags = f}))
      | _ -> False
    end

let wp_code_delta = [
  "X64.Vale.State_i.__proj__Mkstate__item__regs";
  "X64.Vale.State_i.__proj__Mkstate__item__ok" ;
  "X64.Vale.State_i.__proj__Mkstate__item__flags";
  "X64.Vale.State_i.__proj__Mkstate__item__mem";
  ]

[@"uninterpreted_by_smt"]
val va_lemma_weakest_pre_norm (inss:list ins) (s0:state) (f0:va_fuel) : PURE (sN:state)
  (fun (post:(state -> Type)) ->
    forall ok0 regs0 flags0 mem0.
      ok0 == s0.ok /\
      regs0 == s0.regs /\
      flags0 == s0.flags /\
      mem0 == s0.mem ==>
      s0.ok /\
      Prims.norm
        [delta_only wp_code_delta; delta_attr va_qattr; zeta; iota; primops]
        (wp_code
          (normalize_term inss)
          (augment (va_Block (normalize_term (inss_to_codes inss))) s0 f0 post)
          ({ok=ok0; regs=regs0; flags=flags0; mem=mem0})))


(* #reset-options "--log_queries --debug X64.Vale.StrongPost_i --debug_level print_normalized_terms" *)
// let test_lemma (s0:state) (sN:state) =
//     assume (s0.ok);
//     // assume (Map.contains s0.mem (s0.regs Rsi));
//     assume (Map.contains s0.mem (s0.regs Rcx));
//     let i1 = Prims.set_range_of (Load64 (OReg Rax) (OReg Rsi) 0)
//                                 (mk_range "load-instruction-1" 1 1 2 0) in
//     let i2 = Prims.set_range_of (Load64 (OReg Rbx) (OReg Rcx) 0)
//                                 (mk_range "load-instruction-2" 2 1 3 0) in
//     let i3 = Mov64 (OReg Rax) (OReg Rbx) in
//     assume (eval_code (va_Block (inss_to_codes [i1;i2;i3])) s0 sN);
//     va_lemma_weakest_pre_norm [i1; i2; i3] s0 sN;
//     //this assertion is what F* uses to implicitly instantiate
//     //the post-condition predicate in lemma_weakest_pre_norm
//     assert (state_eq sN (update_reg Rbx (sN.regs Rbx)
//                         (update_reg Rax (sN.regs Rax) s0)))
