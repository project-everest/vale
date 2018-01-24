// Optimized weakest precondition generation for 'quick' procedures

module X64.Vale.Quick_i
open X64.Machine_s
open X64.Vale.State_i
open X64.Vale.Decls

unfold let code = va_code
unfold let codes = va_codes
unfold let fuel = va_fuel
unfold let eval = eval_code
let if_codes (b:bool) (cs1:codes) (cs2:codes) : codes = if b then cs1 else cs2

noeq type quickCodes (a:Type0) : codes -> Type =
| QEmpty: a -> quickCodes a []
| QSeq: #b:Type -> #c:code -> #cs:codes -> quickCode b c -> quickCodes a cs -> quickCodes a (c::cs)
| QBind: #b:Type -> #c:code -> #cs:codes -> quickCode b c -> (state -> b -> quickCodes a cs) -> quickCodes a (c::cs)
| QGetState: #cs:codes -> (state -> quickCodes a cs) -> quickCodes a ((Block [])::cs)
| QLemma: #cs:codes -> pre:Type0 -> post:Type0 -> (unit -> Lemma (requires pre) (ensures post)) -> quickCodes a cs -> quickCodes a cs

let wpLemma (#cs:codes) (#pre:Type0) (#post:Type0) (#a:Type0) ($l:unit -> Lemma (requires pre) (ensures post)) (qcs:quickCodes a cs) : quickCodes a cs =
  QLemma pre post l qcs

let wp_proc (#a:Type0) (c:code) (qc:quickCode a c) (s0:state) (k:state -> a -> Type0) : Type0 =
  match qc with
  | QProc _ wp _ _ _ -> wp s0 k

let wp_Seq_t (a:Type0) = state -> a -> Type0
let wp_Bind_t (a:Type0) = state -> a -> Type0
let rec wp (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (k:state -> a -> Type0) (s0:state) :
  Tot Type0 (decreases %[cs; 0; qcs])
  =
  match qcs with
  | QEmpty g -> k s0 g
  | QSeq qc qcs ->
      let c::cs = cs in
      wp_proc c qc s0 (wp_Seq cs qcs k)
  | QBind qc qcs ->
      let c::cs = cs in
      wp_proc c qc s0 (wp_Bind cs qcs k)
  | QGetState f ->
      let c::cs = cs in
      wp cs (f s0) k s0
  | QLemma pre post l qcs -> pre /\ (post ==> wp cs qcs k s0)
// Hoist lambdas out of main definition to avoid issues with function equality 
and wp_Seq (#a:Type0) (#b:Type0) (cs:codes) (qcs:quickCodes b cs) (k:state -> b -> Type0) :
  Tot (wp_Seq_t a) (decreases %[cs; 1; qcs])
  =
  let f s0 _ = wp cs qcs k s0 in f
and wp_Bind (#a:Type0) (#b:Type0) (cs:codes) (qcs:state -> a -> quickCodes b cs) (k:state -> b -> Type0) :
  Tot (wp_Bind_t a) (decreases %[cs; 1; qcs])
  =
  let f s0 g = wp cs (qcs s0 g) k s0 in f

val wp_monotone (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (k1:state -> a -> Type0) (k2:state -> a -> Type0) (s0:state) : Lemma
  (requires (forall (s:state) (g:a). k1 s g ==> k2 s g))
  (ensures wp cs qcs k1 s0 ==> wp cs qcs k2 s0)

val wp_compute (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (s0:state) :
  Ghost ((sN:state) * (fN:fuel) * (g:a))
  (requires wp cs qcs k_true s0)
  (ensures fun _ -> True)

val wp_sound (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (k:state -> a -> Type0) (s0:state) : Lemma
  (requires wp cs qcs k s0)
  (ensures (wp_monotone cs qcs k k_true s0; let (sN, fN, gN) = wp_compute cs qcs s0 in eval (Block cs) s0 fN sN /\ k sN gN))

unfold let block = va_Block

let wp_block (#a:Type) (#cs:codes) (qcs:state -> quickCodes a cs) (s0:state) (k:state -> a -> Type0) : Type0 =
  wp cs (qcs s0) k s0

val qblock_monotone (#a:Type) (#cs:codes) (qcs:state -> quickCodes a cs) (s0:state) (k1:state -> a -> Type0) (k2:state -> a -> Type0) : Lemma
  (requires (forall (s:state) (g:a). k1 s g ==> k2 s g))
  (ensures wp_block qcs s0 k1 ==> wp_block qcs s0 k2)

val qblock_compute (#a:Type) (#cs:codes) (qcs:state -> quickCodes a cs) (s0:state) : Ghost (state * fuel * a)
  (requires wp_block qcs s0 k_true)
  (ensures fun _ -> True)

val qblock_proof (#a:Type) (#cs:codes) (qcs:state -> quickCodes a cs) (s0:state) (k:state -> a -> Type0) : Lemma
  (requires wp_block qcs s0 k)
  (ensures (qblock_monotone qcs s0 k k_true; let (sM, f0, g) = qblock_compute qcs s0 in eval_code (block cs) s0 f0 sM /\ k sM g))

[@"opaque_to_smt"]
let qblock (#a:Type) (#cs:codes) (qcs:state -> quickCodes a cs) : quickCode a (block cs) =
  QProc (block cs) (wp_block qcs) (qblock_monotone qcs) (qblock_compute qcs) (qblock_proof qcs)

val wp_sound_code (#a:Type0) (c:code) (qc:quickCode a c) (k:state -> a -> Type0) (s0:state) :
  Ghost ((sN:state) * (fN:fuel) * (g:a))
  (requires QProc?.wp qc s0 k)
  (ensures fun (sN, fN, gN) -> eval_code c s0 fN sN /\ k sN gN)

let rec regs_match (regs:list reg) (r0:Regs_i.t) (r1:Regs_i.t) : Type0 =
  match regs with
  | [] -> True
  | r::regs -> r0 r == r1 r /\ regs_match regs r0 r1

let all_regs_match (r0:Regs_i.t) (r1:Regs_i.t) : Type0
  =
  let regs = [Rax; Rbx; Rcx; Rdx; Rsi; Rdi; Rbp; Rsp; R8; R9; R10; R11; R12; R13; R14; R15] in
  regs_match regs r0 r1

let va_state_match (s0:state) (s1:state) : Pure Type0
  (requires True)
  (ensures fun b -> b ==> state_eq s0 s1)
  =
  assert_norm (all_regs_match s0.regs s1.regs ==> Regs_i.equal s0.regs s1.regs);
  s0.ok == s1.ok /\
  all_regs_match s0.regs s1.regs /\
  s0.flags == s1.flags /\
  s0.mem == s1.mem

unfold let wp_sound_pre (#a:Type0) (#cs:codes) (qcs:quickCodes a cs) (s0:state) (k:state -> state -> a -> Type0) : Type0 =
  forall (ok:bool) (regs:Regs_i.t) (flags:nat64) (mem:mem).
    let s0' = {ok = ok; regs = regs; flags = flags; mem = mem} in
    s0 == s0' ==> wp cs qcs (k s0') s0'

unfold let wp_sound_post (#a:Type0) (#cs:codes) (qcs:quickCodes a cs) (s0:state) (k:state -> state -> a -> Type0) ((sN:state), (fN:fuel), (gN:a)) : Type0 =
  eval (Block cs) s0 fN sN /\
  k s0 sN gN

val wp_sound_wrap (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (s0:state) (k:state -> state -> a -> Type0) :
  Ghost (state * fuel * a)
    (wp_sound_pre qcs s0 k)
    (wp_sound_post qcs s0 k)

unfold let wp_sound_code_pre (#a:Type0) (#c:code) (qc:quickCode a c) (s0:state) (k:state -> state -> a -> Type0) : Type0 =
  forall (ok:bool) (regs:Regs_i.t) (flags:nat64) (mem:mem).
    let s0' = {ok = ok; regs = regs; flags = flags; mem = mem} in
    s0 == s0' ==> QProc?.wp qc s0' (k s0')

unfold let wp_sound_code_post (#a:Type0) (#c:code) (qc:quickCode a c) (s0:state) (k:state -> state -> a -> Type0) ((sN:state), (fN:fuel), (gN:a)) : Type0 =
  eval c s0 fN sN /\
  k s0 sN gN

val wp_sound_code_wrap (#a:Type0) (c:code) (qc:quickCode a c) (s0:state) (k:state -> state -> a -> Type0) :
  Ghost (state * fuel * a)
    (wp_sound_code_pre qc s0 k)
    (wp_sound_code_post qc s0 k)

// For efficiency, absorb the state components from the (potentially large) normalized
// final state sN into an alternate final state sN' (related to sN via 'update' and 'post':
// update describes which components changed, post describes what they changed to).
let wp_final_k (#a:Type0) (update:state -> state) (post:state -> state -> Type0) (k:state -> a -> Type0) (sN:state) (g:a) : Type0 =
  va_state_match sN (update sN) /\ post sN sN /\
    (forall (ok':bool) (regs':Regs_i.t) (flags':nat64) (mem':mem).
      let sN' = {ok = ok'; regs = regs'; flags = flags'; mem = mem'} in
      post sN sN' ==> k sN' g)

// For efficiency, introduce shorter names (e.g. ok, mem) for components of initial state s0.
let wp_wrap (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (update:state -> state -> state) (post:state -> state -> Type0) (k:state -> a -> Type0) (s0:state) : Type0 =
  forall (ok:bool) (regs:Regs_i.t) (flags:nat64) (mem:mem).
    let s0' = {ok = ok; regs = regs; flags = flags; mem = mem} in
    s0 == s0' ==> wp cs qcs (wp_final_k (update s0') post k) s0'

let wp_wrap_code (#a:Type0) (c:code) (qc:quickCode a c) (update:state -> state -> state) (post:state -> state -> Type0) (k:state -> a -> Type0) (s0:state) : Type0 =
  forall (ok:bool) (regs:Regs_i.t) (flags:nat64) (mem:mem).
    let s0' = {ok = ok; regs = regs; flags = flags; mem = mem} in
    s0 == s0' ==> QProc?.wp qc s0' (wp_final_k (update s0') post k)

unfold let wp_GHOST (#a:Type0) (c:code) (s0:state) (update:state -> state -> state) (fk:(state -> a -> Type0) -> Type0) (p:state * fuel * a -> Type0) : Type0 =
  forall (k:state -> a -> Type0).
    (forall (sN:state) (gN:a).{:pattern (k sN gN)}
      (forall (fN:fuel). eval c s0 fN sN /\ sN == update s0 sN ==> p (sN, fN, gN)) ==>
      k sN gN
    ) ==>
    fk k

// Use raw GHOST effect to integrate soundness proof into F*'s own weakest precondition generation.
val wp_run (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (s0:state) (update:state -> state -> state) (post:state -> state -> Type0) :
  GHOST (state * fuel * a) (wp_GHOST (Block cs) s0 update (fun k -> wp_wrap cs qcs update post k s0))

val wp_run_code (#a:Type0) (c:code) (qc:quickCode a c) (s0:state) (update:state -> state -> state) (post:state -> state -> Type0) :
  GHOST (state * fuel * a) (wp_GHOST c s0 update (fun k -> wp_wrap_code c qc update post k s0))

unfold let normal_steps : list string =
  [
    "X64.Vale.Quick_i.wp";
    "X64.Vale.Quick_i.wp_wrap";
    "X64.Vale.Quick_i.wp_wrap_code";
    "X64.Vale.Quick_i.wp_proc";
    "X64.Vale.Quick_i.wp_Seq";
    "X64.Vale.Quick_i.wp_Bind";
    "X64.Vale.Quick_i.wp_block";
    "X64.Vale.Quick_i.qblock";
    "X64.Vale.Quick_i.wpLemma";
    "X64.Vale.Quick_i.regs_match";
    "X64.Vale.Quick_i.all_regs_match";
    "X64.Vale.Quick_i.va_state_match";
    "X64.Vale.Quick_i.wp_sound_pre";
    "X64.Vale.Quick_i.wp_sound_code_pre";
    "X64.Vale.Quick_i.wp_final_k";
//    "X64.Vale.Quick_i.norm_all_regs_match";

    "X64.Machine_s.__proj__OReg__item__r";
    "X64.Machine_s.uu___is_OReg";

    "X64.Vale.State_i.__proj__Mkstate__item__ok";
    "X64.Vale.State_i.__proj__Mkstate__item__regs";
    "X64.Vale.State_i.__proj__Mkstate__item__flags";
    "X64.Vale.State_i.__proj__Mkstate__item__mem";
    "X64.Vale.State_i.to_nat64";
    "X64.Vale.State_i.eval_operand";
    "X64.Vale.State_i.valid_operand";
    "X64.Vale.State_i.eval_reg";
    "X64.Vale.State_i.update_reg";
    "X64.Vale.State_i.update_operand";
    "X64.Vale.State_i.state_eq";

    "X64.Vale.Decls.va_QProc";
    "X64.Vale.Decls.__proj__QProc__item__wp";
    "X64.Vale.Decls.va_eval_dst_opr64";
    "X64.Vale.Decls.va_eval_opr64";
    "X64.Vale.Decls.va_is_dst_opr64";
    "X64.Vale.Decls.va_is_dst_dst_opr64";
    "X64.Vale.Decls.va_is_src_opr64";
    "X64.Vale.Decls.va_state_eq";
    "X64.Vale.Decls.va_get_ok";
    "X64.Vale.Decls.va_get_flags";
    "X64.Vale.Decls.va_get_mem";
    "X64.Vale.Decls.va_get_reg";
    "X64.Vale.Decls.va_update_ok";
    "X64.Vale.Decls.va_update_flags";
    "X64.Vale.Decls.va_update_mem";
    "X64.Vale.Decls.va_update_reg";
    "X64.Vale.Decls.va_upd_ok";
    "X64.Vale.Decls.va_upd_reg";
    "X64.Vale.Decls.va_upd_flags";
    "X64.Vale.Decls.va_upd_mem";
    "X64.Vale.Decls.va_upd_operand_dst_opr64";
    "X64.Vale.Decls.va_CCons";
    "X64.Vale.Decls.va_CNil";
    "X64.Vale.Decls.va_op_opr64_reg";
    "X64.Vale.Decls.va_op_dst_opr64_reg";
    "X64.Vale.Decls.va_const_opr64";
  ]
