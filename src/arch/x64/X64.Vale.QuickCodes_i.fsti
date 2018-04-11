// Optimized weakest precondition generation for 'quick' procedures

module X64.Vale.QuickCodes_i
open X64.Machine_s
open X64.Vale.State_i
open X64.Vale.Decls_i
open X64.Vale.QuickCode_i

unfold let code = va_code
unfold let codes = va_codes
unfold let fuel = va_fuel
unfold let eval = eval_code

[@va_qattr "opaque_to_smt"]
let labeled_wrap (r:range) (msg:string) (p:Type0) = labeled r msg p

// REVIEW: when used inside a function definition, 'labeled' can show up in an SMT query
// as an uninterpreted function.  Make a wrapper around labeled that is interpreted:
[@va_qattr "opaque_to_smt"]
let label (r:range) (msg:string) (p:Type0) : Pure Type (requires True) (ensures fun q -> q <==> p) =
  assert_norm (labeled_wrap r msg p <==> p);
  labeled_wrap r msg p

val lemma_label_bool (r:range) (msg:string) (b:bool) : Lemma
  (requires label r msg b)
  (ensures b)
  [SMTPat (label r msg b)]

// wrap "precedes" and LexCons to avoid issues with label (precedes ...)
let precedes_wrap (a:lex_t) (b:lex_t) = precedes a b
let lexCons (#a:Type) (h:a) (t:lex_t) : lex_t = LexCons h t

[@va_qattr]
let if_code (b:bool) (c1:code) (c2:code) : code = if b then c1 else c2

noeq type quickCodes (a:Type0) : codes -> Type =
| QEmpty: a -> quickCodes a []
| QSeq: #b:Type -> #c:code -> #cs:codes -> r:range -> msg:string -> quickCode b c -> quickCodes a cs -> quickCodes a (c::cs)
| QBind: #b:Type -> #c:code -> #cs:codes -> r:range -> msg:string -> quickCode b c -> (state -> b -> GTot (quickCodes a cs)) -> quickCodes a (c::cs)
| QGetState: #cs:codes -> (state -> GTot (quickCodes a cs)) -> quickCodes a ((Block [])::cs)
| QPURE: #cs:codes -> r:range -> msg:string -> pre:((unit -> GTot Type0) -> GTot Type0) -> (unit -> PURE unit pre) -> quickCodes a cs -> quickCodes a cs
| QLemma: #cs:codes -> r:range -> msg:string -> pre:Type0 -> post:Type0 -> (unit -> Lemma (requires pre) (ensures post)) -> quickCodes a cs -> quickCodes a cs

[@va_qattr]
let qPURE (#cs:codes) (#pre:(unit -> GTot Type0) -> GTot Type0) (#a:Type0) (r:range) (msg:string) ($l:unit -> PURE unit pre) (qcs:quickCodes a cs) : quickCodes a cs =
  QPURE r msg pre l qcs

[@va_qattr]
let wp_proc (#a:Type0) (c:code) (qc:quickCode a c) (s0:state) (k:state -> a -> Type0) : Type0 =
  match qc with
  | QProc _ wp _ _ _ -> wp s0 k

let wp_Seq_t (a:Type0) = state -> a -> Type0
let wp_Bind_t (a:Type0) = state -> a -> Type0

[@va_qattr]
let range1 = mk_range "" 0 0 0 0

let guard_false = False

[@va_qattr]
let rec wp (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (k:state -> a -> Type0) (s0:state) :
  Tot Type0 (decreases %[cs; 0; qcs])
  =
  match qcs with
  | QEmpty g -> k s0 g
  | QSeq r msg qc qcs ->
      let c::cs = cs in
      label r msg (wp_proc c qc s0 (wp_Seq cs qcs k))
  | QBind r msg qc qcs ->
      let c::cs = cs in
      label r msg (wp_proc c qc s0 (wp_Bind cs qcs k))
  | QGetState f ->
      let c::cs = cs in
      wp cs (f s0) k s0
  | QPURE r msg pre l qcs ->
      // REVIEW: rather than just applying 'pre' directly to k,
      // we define this in a roundabout way so that:
      // - it works even if 'pre' isn't known to be monotonic
      // - F*'s error reporting uses 'guard_free' and 'guard_False <==>' to process labels inside (wp cs qcs k s0)
      (forall (p:unit -> GTot Type0).//{:pattern (pre p)}
        (forall (u:unit).{:pattern (guard_free (p u))} guard_false <==> (wp cs qcs k s0) /\ ~(p ()))
        ==>
        label r msg (pre p))
  | QLemma r msg pre post l qcs ->
      label r msg pre /\ (post ==> wp cs qcs k s0)
// Hoist lambdas out of main definition to avoid issues with function equality 
and wp_Seq (#a:Type0) (#b:Type0) (cs:codes) (qcs:quickCodes b cs) (k:state -> b -> Type0) :
  Tot (wp_Seq_t a) (decreases %[cs; 1; qcs])
  =
  let f s0 _ = wp cs qcs k s0 in f
and wp_Bind (#a:Type0) (#b:Type0) (cs:codes) (qcs:state -> a -> GTot (quickCodes b cs)) (k:state -> b -> Type0) :
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

///// Block

unfold let block = va_Block

[@va_qattr]
let wp_block (#a:Type) (#cs:codes) (qcs:state -> GTot (quickCodes a cs)) (s0:state) (k:state -> a -> Type0) : Type0 =
  wp cs (qcs s0) k s0

val qblock_monotone (#a:Type) (#cs:codes) (qcs:state -> GTot (quickCodes a cs)) (s0:state) (k1:state -> a -> Type0) (k2:state -> a -> Type0) : Lemma
  (requires (forall (s:state) (g:a). k1 s g ==> k2 s g))
  (ensures wp_block qcs s0 k1 ==> wp_block qcs s0 k2)

val qblock_compute (#a:Type) (#cs:codes) (qcs:state -> GTot (quickCodes a cs)) (s0:state) : Ghost (state * fuel * a)
  (requires wp_block qcs s0 k_true)
  (ensures fun _ -> True)

val qblock_proof (#a:Type) (#cs:codes) (qcs:state -> GTot (quickCodes a cs)) (s0:state) (k:state -> a -> Type0) : Lemma
  (requires wp_block qcs s0 k)
  (ensures (qblock_monotone qcs s0 k k_true; let (sM, f0, g) = qblock_compute qcs s0 in eval_code (block cs) s0 f0 sM /\ k sM g))

[@"opaque_to_smt" va_qattr]
let qblock (#a:Type) (#cs:codes) (qcs:state -> GTot (quickCodes a cs)) : quickCode a (block cs) =
  QProc (block cs) (wp_block qcs) (qblock_monotone qcs) (qblock_compute qcs) (qblock_proof qcs)

///// If, InlineIf

[@va_qattr]
let wp_InlineIf (#a:Type) (#c1:code) (#c2:code) (b:bool) (qc1:quickCode a c1) (qc2:quickCode a c2) (s0:state) (k:state -> a -> Type0) : Type0 =
  // REVIEW: this duplicates k
  (b ==> QProc?.wp qc1 s0 k) /\ (not b ==> QProc?.wp qc2 s0 k)

val qInlineIf_monotone (#a:Type) (#c1:code) (#c2:code) (b:bool) (qc1:quickCode a c1) (qc2:quickCode a c2) (s0:state) (k1:state -> a -> Type0) (k2:state -> a -> Type0) : Lemma
  (requires (forall (s:state) (g:a). k1 s g ==> k2 s g))
  (ensures wp_InlineIf b qc1 qc2 s0 k1 ==> wp_InlineIf b qc1 qc2 s0 k2)

val qInlineIf_compute (#a:Type) (#c1:code) (#c2:code) (b:bool) (qc1:quickCode a c1) (qc2:quickCode a c2) (s0:state) : Ghost (state * fuel * a)
  (requires wp_InlineIf b qc1 qc2 s0 k_true)
  (ensures fun _ -> True)

val qInlineIf_proof (#a:Type) (#c1:code) (#c2:code) (b:bool) (qc1:quickCode a c1) (qc2:quickCode a c2) (s0:state) (k:state -> a -> Type0) : Lemma
  (requires wp_InlineIf b qc1 qc2 s0 k)
  (ensures (qInlineIf_monotone b qc1 qc2 s0 k k_true; let (sM, f0, g) = qInlineIf_compute b qc1 qc2 s0 in eval_code (if_code b c1 c2) s0 f0 sM /\ k sM g))

[@"opaque_to_smt" va_qattr]
let qInlineIf (#a:Type) (#c1:code) (#c2:code) (b:bool) (qc1:quickCode a c1) (qc2:quickCode a c2) : quickCode a (if_code b c1 c2) =
  QProc (if_code b c1 c2) (wp_InlineIf b qc1 qc2) (qInlineIf_monotone b qc1 qc2) (qInlineIf_compute b qc1 qc2) (qInlineIf_proof b qc1 qc2)

type cmp =
| Cmp_eq : operand -> operand -> cmp
| Cmp_ne : operand -> operand -> cmp
| Cmp_le : operand -> operand -> cmp
| Cmp_ge : operand -> operand -> cmp
| Cmp_lt : operand -> operand -> cmp
| Cmp_gt : operand -> operand -> cmp

[@va_qattr]
let cmp_to_ocmp (c:cmp) : ocmp =
  match c with
  | Cmp_eq o1 o2 -> va_cmp_eq o1 o2
  | Cmp_ne o1 o2 -> va_cmp_ne o1 o2
  | Cmp_le o1 o2 -> va_cmp_le o1 o2
  | Cmp_ge o1 o2 -> va_cmp_ge o1 o2
  | Cmp_lt o1 o2 -> va_cmp_lt o1 o2
  | Cmp_gt o1 o2 -> va_cmp_gt o1 o2

[@va_qattr]
let valid_cmp (c:cmp) (s:state) : Type0 =
  match c with
  | Cmp_eq o1 o2 -> valid_operand o1 s /\ valid_operand o2 s
  | Cmp_ne o1 o2 -> valid_operand o1 s /\ valid_operand o2 s
  | Cmp_le o1 o2 -> valid_operand o1 s /\ valid_operand o2 s
  | Cmp_ge o1 o2 -> valid_operand o1 s /\ valid_operand o2 s
  | Cmp_lt o1 o2 -> valid_operand o1 s /\ valid_operand o2 s
  | Cmp_gt o1 o2 -> valid_operand o1 s /\ valid_operand o2 s

[@va_qattr]
let eval_cmp (s:state) (c:cmp) : bool =
  match c with
  | Cmp_eq o1 o2 -> va_eval_opr64 s o1 =  va_eval_opr64 s o2
  | Cmp_ne o1 o2 -> va_eval_opr64 s o1 <> va_eval_opr64 s o2
  | Cmp_le o1 o2 -> va_eval_opr64 s o1 <= va_eval_opr64 s o2
  | Cmp_ge o1 o2 -> va_eval_opr64 s o1 >= va_eval_opr64 s o2
  | Cmp_lt o1 o2 -> va_eval_opr64 s o1 <  va_eval_opr64 s o2
  | Cmp_gt o1 o2 -> va_eval_opr64 s o1 >  va_eval_opr64 s o2

[@va_qattr]
let wp_If (#a:Type) (#c1:code) (#c2:code) (b:cmp) (qc1:quickCode a c1) (qc2:quickCode a c2) (s0:state) (k:state -> a -> Type0) : Type0 =
  // REVIEW: this duplicates k
  valid_cmp b s0 /\ (eval_cmp s0 b ==> QProc?.wp qc1 s0 k) /\ (not (eval_cmp s0 b) ==> QProc?.wp qc2 s0 k)

val qIf_monotone (#a:Type) (#c1:code) (#c2:code) (b:cmp) (qc1:quickCode a c1) (qc2:quickCode a c2) (s0:state) (k1:state -> a -> Type0) (k2:state -> a -> Type0) : Lemma
  (requires (forall (s:state) (g:a). k1 s g ==> k2 s g))
  (ensures wp_If b qc1 qc2 s0 k1 ==> wp_If b qc1 qc2 s0 k2)

val qIf_compute (#a:Type) (#c1:code) (#c2:code) (b:cmp) (qc1:quickCode a c1) (qc2:quickCode a c2) (s0:state) : Ghost (state * fuel * a)
  (requires wp_If b qc1 qc2 s0 k_true)
  (ensures fun _ -> True)

val qIf_proof (#a:Type) (#c1:code) (#c2:code) (b:cmp) (qc1:quickCode a c1) (qc2:quickCode a c2) (s0:state) (k:state -> a -> Type0) : Lemma
  (requires wp_If b qc1 qc2 s0 k)
  (ensures (qIf_monotone b qc1 qc2 s0 k k_true; let (sM, f0, g) = qIf_compute b qc1 qc2 s0 in eval_code (IfElse (cmp_to_ocmp b) c1 c2) s0 f0 sM /\ k sM g))

[@"opaque_to_smt" va_qattr]
let qIf (#a:Type) (#c1:code) (#c2:code) (b:cmp) (qc1:quickCode a c1) (qc2:quickCode a c2) : quickCode a (IfElse (cmp_to_ocmp b) c1 c2) =
  QProc (IfElse (cmp_to_ocmp b) c1 c2) (wp_If b qc1 qc2) (qIf_monotone b qc1 qc2) (qIf_compute b qc1 qc2) (qIf_proof b qc1 qc2)

///// Assert, Assume, AssertBy

let tAssertLemma (p:Type0) = unit -> Lemma (requires p) (ensures p)
val qAssertLemma (p:Type0) : tAssertLemma p

[@va_qattr]
let qAssert (#a:Type) (#cs:codes) (r:range) (msg:string) (e:Type0) (qcs:quickCodes a cs) : quickCodes a cs =
  QLemma r msg e e (qAssertLemma e) qcs

let tAssumeLemma (p:Type0) = unit -> Lemma (requires True) (ensures p)
val qAssumeLemma (p:Type0) : tAssumeLemma p

[@va_qattr]
let qAssume (#a:Type) (#cs:codes) (r:range) (msg:string) (e:Type0) (qcs:quickCodes a cs) : quickCodes a cs =
  QLemma r msg True e (qAssumeLemma e) qcs

let tAssertByLemma (#a:Type) (p:Type0) (qcs:quickCodes a []) (s0:state) =
  unit -> Lemma (requires wp [] qcs (fun _ _ -> p) s0) (ensures p)
val qAssertByLemma (#a:Type) (p:Type0) (qcs:quickCodes a []) (s0:state) : tAssertByLemma p qcs s0

[@va_qattr]
let qAssertBy (#a:Type) (#cs:codes) (r:range) (msg:string) (p:Type0) (qcsBy:quickCodes unit []) (s0:state) (qcsTail:quickCodes a cs) : quickCodes a cs =
  QLemma r msg (wp [] qcsBy (fun _ _ -> p) s0) p (qAssertByLemma p qcsBy s0) qcsTail

///// Code

val wp_sound_code (#a:Type0) (c:code) (qc:quickCode a c) (k:state -> a -> Type0) (s0:state) :
  Ghost ((sN:state) * (fN:fuel) * (g:a))
  (requires QProc?.wp qc s0 k)
  (ensures fun (sN, fN, gN) -> eval_code c s0 fN sN /\ k sN gN)

[@va_qattr]
let rec regs_match (regs:list reg) (r0:Regs_i.t) (r1:Regs_i.t) : Type0 =
  match regs with
  | [] -> True
  | r::regs -> r0 r == r1 r /\ regs_match regs r0 r1

[@va_qattr]
let all_regs_match (r0:Regs_i.t) (r1:Regs_i.t) : Type0
  =
  let regs = [Rax; Rbx; Rcx; Rdx; Rsi; Rdi; Rbp; Rsp; R8; R9; R10; R11; R12; R13; R14; R15] in
  regs_match regs r0 r1

[@va_qattr]
let rec xmms_match (xmms:list xmm) (r0:Xmms_i.t) (r1:Xmms_i.t) : Type0 =
  match xmms with
  | [] -> True
  | r::xmms -> r0 r == r1 r /\ xmms_match xmms r0 r1

[@va_qattr]
let all_xmms_match (r0:Xmms_i.t) (r1:Xmms_i.t) : Type0
  =
  let xmms = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15] in
  xmms_match xmms r0 r1

[@va_qattr]
let va_state_match (s0:state) (s1:state) : Pure Type0
  (requires True)
  (ensures fun b -> b ==> state_eq s0 s1)
  =
  assert_norm (all_regs_match s0.regs s1.regs ==> Regs_i.equal s0.regs s1.regs);
  assert_norm (all_xmms_match s0.xmms s1.xmms ==> Xmms_i.equal s0.xmms s1.xmms);
  s0.ok == s1.ok /\
  all_regs_match s0.regs s1.regs /\
  all_xmms_match s0.xmms s1.xmms /\
  s0.flags == s1.flags /\
  s0.mem == s1.mem

[@va_qattr]
unfold let wp_sound_pre (#a:Type0) (#cs:codes) (qcs:quickCodes a cs) (s0:state) (k:state -> state -> a -> Type0) : Type0 =
  forall (ok:bool) (regs:Regs_i.t) (xmms:Xmms_i.t) (flags:nat64) (mem:mem).
    let s0' = {ok = ok; regs = regs; xmms = xmms; flags = flags; mem = mem} in
    s0 == s0' ==> wp cs qcs (k s0') s0'

unfold let wp_sound_post (#a:Type0) (#cs:codes) (qcs:quickCodes a cs) (s0:state) (k:state -> state -> a -> Type0) ((sN:state), (fN:fuel), (gN:a)) : Type0 =
  eval (Block cs) s0 fN sN /\
  k s0 sN gN

val wp_sound_wrap (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (s0:state) (k:state -> state -> a -> Type0) :
  Ghost (state * fuel * a)
    (wp_sound_pre qcs s0 k)
    (wp_sound_post qcs s0 k)

[@va_qattr]
unfold let wp_sound_code_pre (#a:Type0) (#c:code) (qc:quickCode a c) (s0:state) (k:state -> state -> a -> Type0) : Type0 =
  forall (ok:bool) (regs:Regs_i.t) (xmms:Xmms_i.t) (flags:nat64) (mem:mem).
    let s0' = {ok = ok; regs = regs; xmms = xmms; flags = flags; mem = mem} in
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
[@va_qattr]
let wp_final_k (#a:Type0) (update:state -> state) (post:state -> state -> Type0) (k:state -> a -> Type0) (sN:state) (g:a) : Type0 =
  va_state_match sN (update sN) /\ post sN sN /\
    (forall (ok':bool) (regs':Regs_i.t) (xmms':Xmms_i.t) (flags':nat64) (mem':mem).
      let sN' = {ok = ok'; regs = regs'; xmms = xmms'; flags = flags'; mem = mem'} in
      post sN sN' ==> k sN' g)

// For efficiency, introduce shorter names (e.g. ok, mem) for components of initial state s0.
[@va_qattr]
let wp_wrap (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (update:state -> state -> state) (post:state -> state -> Type0) (k:state -> a -> Type0) (s0:state) : Type0 =
  forall (ok:bool) (regs:Regs_i.t) (xmms:Xmms_i.t) (flags:nat64) (mem:mem).
    let s0' = {ok = ok; regs = regs; xmms = xmms; flags = flags; mem = mem} in
    s0 == s0' ==> wp cs qcs (wp_final_k (update s0') post k) s0'

[@va_qattr]
let wp_wrap_code (#a:Type0) (c:code) (qc:quickCode a c) (update:state -> state -> state) (post:state -> state -> Type0) (k:state -> a -> Type0) (s0:state) : Type0 =
  forall (ok:bool) (regs:Regs_i.t) (xmms:Xmms_i.t) (flags:nat64) (mem:mem).
    let s0' = {ok = ok; regs = regs; xmms = xmms; flags = flags; mem = mem} in
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
    "X64.Vale.State_i.__proj__Mkstate__item__ok";
    "X64.Vale.State_i.__proj__Mkstate__item__regs";
    "X64.Vale.State_i.__proj__Mkstate__item__xmms";
    "X64.Vale.State_i.__proj__Mkstate__item__flags";
    "X64.Vale.State_i.__proj__Mkstate__item__mem";

    "X64.Vale.QuickCode_i.__proj__QProc__item__wp";
  ]

unfold let normal (x:Type0) : Type0 = norm [iota; zeta; simplify; primops; delta_attr va_qattr; delta_only normal_steps] x

val wp_sound_norm (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (s0:state) (k:state -> state -> a -> Type0) :
  Ghost (state * fuel * a)
    (normal (wp_sound_pre qcs s0 k))
    (wp_sound_post qcs s0 k)

val wp_sound_code_norm (#a:Type0) (c:code) (qc:quickCode a c) (s0:state) (k:state -> state -> a -> Type0) :
  Ghost (state * fuel * a)
    (normal (wp_sound_code_pre qc s0 k))
    (wp_sound_code_post qc s0 k)

val wp_run_norm (#a:Type0) (cs:codes) (qcs:quickCodes a cs) (s0:state) (update:state -> state -> state) (post:state -> state -> Type0) :
  GHOST (state * fuel * a) (wp_GHOST (Block cs) s0 update (fun k -> normal (wp_wrap cs qcs update post k s0)))

