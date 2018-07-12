(*
See QuickRegs1.fst for comments
*)

module QuickRegs2

irreducible let qattr = ()

let pow2_64 = 0x10000000000000000
type nat64 = i:int{0 <= i /\ i < pow2_64}

type reg = | Rax | Rbx | Rcx | Rdx
type operand = | OReg: r:reg -> operand | OConst: n:nat64 -> operand

type ins =
| Mov64: dst:operand -> src:operand -> ins
| Add64: dst:operand -> src:operand -> ins

type code =
| Ins: ins:ins -> code
| Block: block:list code -> code
| WhileLessThan: src1:operand -> src2:operand -> whileBody:code -> code

type state = reg -> nat64
type fuel = nat

[@qattr]
let eval_operand (o:operand) (s:state) : nat64 =
  match o with
  | OReg r -> s r
  | OConst n -> n

[@qattr]
let update_reg (s:state) (r:reg) (v:nat64) : state =
  fun r' -> if r = r' then v else s r'

[@qattr]
let update_state (r:reg) (s' s:state) : state =
  update_reg s r (s' r)

// We don't have an "ok" flag, so errors just result an arbitrary state:
assume val unknown_state (s:state) : state

let eval_ins (ins:ins) (s:state) : state =
  match ins with
  | Mov64 (OConst _) _ -> unknown_state s
  | Mov64 (OReg dst) src -> update_reg s dst (eval_operand src s)
  | Add64 (OConst _) _ -> unknown_state s
  | Add64 (OReg dst) src ->
      update_reg s dst ((s dst + eval_operand src s) % 0x10000000000000000)

let rec eval_code (c:code) (f:fuel) (s:state) : option state =
  match c with
  | Ins ins -> Some (eval_ins ins s)
  | Block cs -> eval_codes cs f s
  | WhileLessThan src1 src2 body ->
      if f = 0 then None
      else if eval_operand src1 s < eval_operand src2 s then
        match eval_code body f s with
        | None -> None
        | Some s -> eval_code c (f - 1) s
      else Some s
and eval_codes (cs:list code) (f:fuel) (s:state) : option state =
  match cs with
  | [] -> Some s
  | c::cs ->
    (
      match eval_code c f s with
      | None -> None
      | Some s -> eval_codes cs f s
    )

val increase_fuel (c:code) (s0:state) (f0:fuel) (sN:state) (fN:fuel) : Lemma
  (requires eval_code c f0 s0 == Some sN /\ f0 <= fN)
  (ensures eval_code c fN s0 == Some sN)
  (decreases %[f0; c])

val increase_fuels (c:list code) (s0:state) (f0:fuel) (sN:state) (fN:fuel) : Lemma
  (requires eval_code (Block c) f0 s0 == Some sN /\ f0 <= fN)
  (ensures eval_code (Block c) fN s0 == Some sN)
  (decreases %[f0; c])

let rec increase_fuel (c:code) (s0:state) (f0:fuel) (sN:state) (fN:fuel) =
  match c with
  | Ins ins -> ()
  | Block l -> increase_fuels l s0 f0 sN fN
  | WhileLessThan src1 src2 body ->
      if eval_operand src1 s0 < eval_operand src2 s0 then
        match eval_code body f0 s0 with
        | None -> ()
        | Some s1 ->
            increase_fuel body s0 f0 s1 fN;
            increase_fuel c s1 (f0 - 1) sN (fN - 1)
      else ()
and increase_fuels (c:list code) (s0:state) (f0:fuel) (sN:state) (fN:fuel) =
  match c with
  | [] -> ()
  | h::t ->
    (
      let Some s1 = eval_code h f0 s0 in
      increase_fuel h s0 f0 s1 fN;
      increase_fuels t s1 f0 sN fN
    )

let lemma_merge (c:code) (cs:list code) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) : Ghost fuel
  (requires eval_code c f0 s0 == Some sM /\ eval_code (Block cs) fM sM == Some sN)
  (ensures fun fN -> eval_code (Block (c::cs)) fN s0 == Some sN)
  =
  let f = if f0 > fM then f0 else fM in
  increase_fuel c s0 f0 sM f;
  increase_fuel (Block cs) sM fM sN f;
  f

let t_wp (a:Type0) = (a -> state -> Type0) -> (state -> Type0)

let has_wp (a:Type0) (c:code) (wp:t_wp a) : Type =
  k:(a -> state -> Type0) -> s0:state -> Ghost (a * state * fuel)
    (requires wp k s0)
    (ensures fun (g, sM, f0) -> eval_code c f0 s0 == Some sM /\ k g sM)

let t_lemma (pre:Type0) (post:Type0) = unit -> Lemma (requires pre) (ensures post)

[@qattr]
noeq type quickCode (a:Type0) : code -> Type =
| QProc: c:code -> wp:t_wp a -> hasWp:has_wp a c wp -> quickCode a c

noeq type quickCodes (a:Type0) : list code -> Type =
| QEmpty: a -> quickCodes a []
| QSeq: #b:Type0 -> #c:code -> #cs:list code -> quickCode b c -> quickCodes a cs -> quickCodes a (c::cs)
| QBind: #b:Type0 -> #c:code -> #cs:list code -> quickCode b c -> (b -> state -> quickCodes a cs) -> quickCodes a (c::cs)
| QLemma: #cs:list code -> pre:Type0 -> post:Type0 -> t_lemma pre post -> quickCodes a cs -> quickCodes a cs

type t_Bind (a:Type0) = a -> state -> Type0

[@qattr]
let rec vc_gen (#a:Type0) (cs:list code) (qcs:quickCodes a cs) (k:a -> state -> Type0) (s0:state) :
  Tot Type0 (decreases %[cs; 0; qcs])
  =
    match qcs with
    | QEmpty g -> k g s0
    | QSeq qc qcs -> qc.wp (vc_gen_Seq (Cons?.tl cs) qcs k) s0
    | QBind qc f_qcs -> qc.wp (vc_gen_Bind (Cons?.tl cs) f_qcs k) s0
    | QLemma pre post _ qcs -> pre /\ (post ==> vc_gen cs qcs k s0)
and vc_gen_Seq (#a:Type0) (#b:Type0) (cs:list code) (qcs:quickCodes b cs) (k:b -> state -> Type0) :
  a -> state -> Tot Type0 (decreases %[cs; 1; qcs])
  =
  fun _ s0 -> vc_gen cs qcs k s0
and vc_gen_Bind (#a:Type0) (#b:Type0) (cs:list code) (f_qcs:a -> state -> quickCodes b cs) (k:b -> state -> Type0) :
  Tot (t_Bind a) (decreases %[cs; 1; f_qcs])
  =
  let f g s0 = vc_gen cs (f_qcs g s0) k s0 in f

let rec vc_sound (#a:Type0) (cs:list code) (qcs:quickCodes a cs) (k:a -> state -> Type0) (s0:state) : Ghost (a * state * fuel)
  (requires vc_gen cs qcs k s0)
  (ensures fun (g, sN, fN) -> eval_code (Block cs) fN s0 == Some sN /\ k g sN)
  =
let qq = qcs in
  match qcs with
  | QEmpty g -> (g, s0, 0)
  | QSeq qc qcs ->
      let Cons c cs' = cs in
      let (gM, sM, fM) = qc.hasWp (vc_gen_Seq cs' qcs k) s0 in
      let (gN, sN, fN) = vc_sound cs' qcs k sM in
      let fN' = lemma_merge c cs' s0 fM sM fN sN in
      (gN, sN, fN')
  | QBind qc f_qcs ->
      let Cons c cs' = cs in
      let (gM, sM, fM) = qc.hasWp (vc_gen_Bind cs' f_qcs k) s0 in
      let (gN, sN, fN) = vc_sound cs' (f_qcs gM sM) k sM in
      let fN' = lemma_merge c cs' s0 fM sM fN sN in
      (gN, sN, fN')
  | QLemma pre post lem qcs' -> lem (); vc_sound cs qcs' k s0

let vc_sound' (#a:Type0) (cs:list code) (qcs:quickCodes a cs) : has_wp a (Block cs) (vc_gen cs qcs) =
  vc_sound cs qcs

unfold let normal_steps : list string =
  [
    `%OReg?;
    `%OReg?.r;
    `%QProc?.wp;
  ]

unfold let normal (x:Type0) : Type0 = norm [iota; zeta; simplify; primops; delta_attr qattr; delta_only normal_steps] x

let vc_sound_norm (#a:Type0) (cs:list code) (qcs:quickCodes a cs) (k:a -> state -> Type0) (s0:state) : Ghost (a * state * fuel)
  (requires normal (vc_gen cs qcs k s0))
  (ensures fun (g, sN, fN) -> eval_code (Block cs) fN s0 == Some sN /\ k g sN)
  =
  vc_sound cs qcs k s0

let lemma_Move (s0:state) (dst:operand) (src:operand) : Ghost (unit * state * fuel)
  (requires OReg? dst)
  (ensures fun (_, sM, fM) ->
    eval_code (Ins (Mov64 dst src)) fM s0 == Some sM /\
    eval_operand dst sM == eval_operand src s0 /\
    sM == update_state (OReg?.r dst) sM s0
  )
  =
  let Some sM = eval_code (Ins (Mov64 dst src)) 0 s0 in
  ((), sM, 0)

[@qattr]
let wp_Move (dst:operand) (src:operand) (k:unit -> state -> Type0) (s0:state) : Type0 =
  OReg? dst /\
  (forall (x:nat64).
    let sM = update_reg s0 (OReg?.r dst) x in
    eval_operand dst sM == eval_operand src s0 ==> k () sM
  )

let hasWp_Move (dst:operand) (src:operand) (k:unit -> state -> Type0) (s0:state) : Ghost (unit * state * fuel)
  (requires wp_Move dst src k s0)
  (ensures fun (_, sM, f0) -> eval_code (Ins (Mov64 dst src)) f0 s0 == Some sM /\ k () sM)
  =
  lemma_Move s0 dst src

[@qattr]
let quick_Move (dst:operand) (src:operand) : quickCode unit (Ins (Mov64 dst src)) =
  QProc (Ins (Mov64 dst src)) (wp_Move dst src) (hasWp_Move dst src)

let lemma_Add (s0:state) (dst:operand) (src:operand) : Ghost (unit * state * fuel)
  (requires OReg? dst /\ eval_operand dst s0 + eval_operand src s0 < pow2_64)
  (ensures fun (_, sM, fM) ->
    eval_code (Ins (Add64 dst src)) fM s0 == Some sM /\
    eval_operand dst sM == eval_operand dst s0 + eval_operand src s0 /\
    sM == update_state (OReg?.r dst) sM s0
  )
  =
  let Some sM = eval_code (Ins (Add64 dst src)) 0 s0 in
  ((), sM, 0)

[@qattr]
let wp_Add (dst:operand) (src:operand) (k:unit -> state -> Type0) (s0:state) : Type0 =
  OReg? dst /\ eval_operand dst s0 + eval_operand src s0 < pow2_64 /\
  (forall (x:nat64).
    let sM = update_reg s0 (OReg?.r dst) x in
    eval_operand dst sM == eval_operand dst s0 + eval_operand src s0 ==> k () sM
  )

let hasWp_Add (dst:operand) (src:operand) (k:unit -> state -> Type0) (s0:state) : Ghost (unit * state * fuel)
  (requires wp_Add dst src k s0)
  (ensures fun (_, sM, f0) -> eval_code (Ins (Add64 dst src)) f0 s0 == Some sM /\ k () sM)
  =
  lemma_Add s0 dst src

[@qattr]
let quick_Add (dst:operand) (src:operand) : quickCode unit (Ins (Add64 dst src)) =
  QProc (Ins (Add64 dst src)) (wp_Add dst src) (hasWp_Add dst src)


[@qattr]
let codes_Triple : list code = [Ins (Mov64 (OReg Rbx) (OReg Rax)); Ins (Add64 (OReg Rax) (OReg Rbx)); Ins (Add64 (OReg Rbx) (OReg Rax))]
[@qattr]
let qcodes_Triple : quickCodes unit codes_Triple =
  QSeq (quick_Move (OReg Rbx) (OReg Rax)) (
  QSeq (quick_Add (OReg Rax) (OReg Rbx)) (
  QSeq (quick_Add (OReg Rbx) (OReg Rax)) (
  QEmpty ())))



(*
procedure Triple()
    modifies rax; rbx;
    requires rax < 100;
    ensures rbx == 3 * old(rax);
{
    Mov(rbx, rax);
    Add(rax, rbx);
    Add(rbx, rax);
}
*)

[@qattr]
let state_eq (s0 s1:state) : Ghost Type0
  (requires True)
  (ensures fun b -> b ==> s0 == s1)
  =
  let b = s0 Rax == s1 Rax /\ s0 Rbx == s1 Rbx /\ s0 Rcx == s1 Rcx /\ s0 Rdx == s1 Rdx in
  assert (b ==> FStar.FunctionalExtensionality.feq s0 s1);
  b

#reset-options "--debug QuickRegs2 --debug_level SMTQuery --print_full_names"
let lemma_Triple (s0:state) : Ghost (unit * state * fuel)
  (requires s0 Rax < 100)
  (ensures fun (_, sM, f0) ->
    eval_code (Block codes_Triple) f0 s0 == Some sM /\
    sM Rbx == 3 `op_Multiply` s0 Rax /\
    sM == update_state Rax sM (update_state Rbx sM s0)
    )
  =
  vc_sound_norm codes_Triple qcodes_Triple
    (fun _ sM -> sM Rbx == 3 `op_Multiply` s0 Rax /\ state_eq sM (update_state Rax sM (update_state Rbx sM s0)))
    s0

