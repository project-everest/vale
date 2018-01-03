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

let lemma (pre:Type0) (post:Type0) : Type0 =
  squash pre -> GTot (squash post)

noeq type quickCodes (a:Type0) : codes -> Type =
| QEmpty: a -> quickCodes a []
| QSeq: #b:Type -> #c:code -> #cs:codes -> quickCode b c -> quickCodes a cs -> quickCodes a (c::cs)
| QBind: #b:Type -> #c:code -> #cs:codes -> quickCode b c -> (b -> quickCodes a cs) -> quickCodes a (c::cs)
| QGetState: #cs:codes -> (state -> quickCodes a cs) -> quickCodes a ((Block [])::cs)
| QLemma: #cs:codes -> pre:Type0 -> post:Type0 -> lemma pre post -> quickCodes a cs -> quickCodes a cs

let wpLemma (#cs:codes) (#pre:Type0) (#post:Type0) (#a:Type0) (l:lemma pre post) (fcs:quickCodes a cs) : quickCodes a cs =
  QLemma pre post l fcs

let wp_proc (#a:Type0) (c:code) (fc:quickCode a c) (s0:state) (wp_continue:state -> a -> Type0) : Type0 =
  match fc with
  | QProc _ wp1' _ -> wp1' s0 wp_continue

let wp_Seq_t (a:Type0) = state -> a -> Type0
let wp_Bind_t (a:Type0) = state -> a -> Type0
let rec wp (#a:Type0) (cs:codes) (fcs:quickCodes a cs) (p:state -> a -> Type0) (s0:state) :
  Tot Type0 (decreases %[cs; 0; fcs])
  =
  match fcs with
  | QEmpty g -> p s0 g
  | QSeq fc fcs ->
      let c::cs = cs in
      wp_proc c fc s0 (wp_Seq cs fcs p)
  | QBind fc fcs ->
      let c::cs = cs in
      wp_proc c fc s0 (wp_Bind cs fcs p)
  | QGetState f ->
      let c::cs = cs in
      wp cs (f s0) p s0
  | QLemma pre post l fcs -> pre /\ (post ==> wp cs fcs p s0)
// Hoist lambdas out of main definition to avoid issues with function equality 
and wp_Seq (#a:Type0) (#b:Type0) (cs:codes) (fcs:quickCodes b cs) (p:state -> b -> Type0) :
  Tot (wp_Seq_t a) (decreases %[cs; 1; fcs])
  =
  let f s0 _ = wp cs fcs p s0 in f
and wp_Bind (#a:Type0) (#b:Type0) (cs:codes) (fcs:a -> quickCodes b cs) (p:state -> b -> Type0) :
  Tot (wp_Bind_t a) (decreases %[cs; 1; fcs])
  =
  let f s0 g = wp cs (fcs g) p s0 in f

val wp_sound (#a:Type0) (cs:codes) (fcs:quickCodes a cs) (p:state -> a -> Type0) (s0:state) :
  Ghost ((sN:state) * (fN:fuel) * (g:a))
  (requires wp cs fcs p s0)
  (ensures fun (sN, fN, gN) -> eval (Block cs) s0 fN sN /\ p sN gN)

let rec regs_match (regs:list reg) (r0:Regs_i.t) (r1:Regs_i.t) : Type0 =
  match regs with
  | [] -> True
  | r::regs -> r0 r == r1 r /\ regs_match regs r0 r1

let all_regs_match (r0:Regs_i.t) (r1:Regs_i.t) : Type0
  =
  let regs = [Rax; Rbx; Rcx; Rdx; Rsi; Rdi; Rbp; Rsp; R8; R9; R10; R11; R12; R13; R14; R15] in
  regs_match regs r0 r1

let state_match (s0:state) (s1:state) : Pure Type0
  (requires True)
  (ensures fun b -> b ==> state_eq s0 s1)
  =
  assert_norm (all_regs_match s0.regs s1.regs ==> Regs_i.equal s0.regs s1.regs);
  s0.ok == s1.ok /\
  all_regs_match s0.regs s1.regs /\
  s0.flags == s1.flags /\
  s0.mem == s1.mem

unfold let normal_steps : list string =
  [
    "X64.Vale.Quick_i.wp";
    "X64.Vale.Quick_i.wp_proc";
    "X64.Vale.Quick_i.wp_Seq";
    "X64.Vale.Quick_i.wp_Bind";
    "X64.Vale.Quick_i.wpLemma";
    "X64.Vale.Quick_i.regs_match";
    "X64.Vale.Quick_i.all_regs_match";
    "X64.Vale.Quick_i.state_match";

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
    "X64.Vale.Decls.va_update_reg";
    "X64.Vale.Decls.va_update_flags";
    "X64.Vale.Decls.va_update_mem";
    "X64.Vale.Decls.va_update_reg";
    "X64.Vale.Decls.va_upd_ok";
    "X64.Vale.Decls.va_upd_flags";
    "X64.Vale.Decls.va_upd_mem";
    "X64.Vale.Decls.va_upd_operand_dst_opr64";
  ]

