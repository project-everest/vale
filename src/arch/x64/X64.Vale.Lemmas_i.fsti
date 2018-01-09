module X64.Vale.Lemmas_i
open X64.Machine_s
open X64.Vale.State_i
open X64.Vale.StateLemmas_i
open FStar.UInt
module S = X64.Semantics_s

unfold let code = S.code
unfold let codes = S.codes
unfold let ocmp = S.ocmp
unfold let fuel = nat

let cf (flags:int) : bool = S.cf (int_to_nat64 flags)

let eval_code (c:code) (s0:state) (f0:fuel) (s1:state) : Type0 =
  Some (state_to_S s1) == S.eval_code c f0 (state_to_S s0)

let eval_ins (c:code) (s0:state) : Ghost ((sM:state) * (f0:fuel))
  (requires Ins? c)
  (ensures fun (sM, f0) ->
    eval_code c s0 f0 sM
  ) =
  let f0 = 0 in
  let (Some sM) = S.eval_code c f0 (state_to_S s0) in
  (state_of_S sM, f0)

let eval_ocmp (s:state) (c:ocmp) : bool = S.eval_ocmp (state_to_S s) c

let valid_ocmp (c:ocmp) (s:state) : bool = S.valid_ocmp c (state_to_S s)

let ensure_valid_ocmp (c:ocmp) (s:state) : state = state_of_S (S.run (S.check (S.valid_ocmp c)) (state_to_S s))

val lemma_cmp_eq : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.OEq o1 o2) <==> eval_operand o1 s == eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.OEq o1 o2))]

val lemma_cmp_ne : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.ONe o1 o2) <==> eval_operand o1 s <> eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.ONe o1 o2))]

val lemma_cmp_le : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.OLe o1 o2) <==> eval_operand o1 s <= eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.OLe o1 o2))]

val lemma_cmp_ge : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.OGe o1 o2) <==> eval_operand o1 s >= eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.OGe o1 o2))]

val lemma_cmp_lt : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.OLt o1 o2) <==> eval_operand o1 s < eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.OLt o1 o2))]

val lemma_cmp_gt : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures eval_ocmp s (S.OGt o1 o2) <==> eval_operand o1 s > eval_operand o2 s)
  [SMTPat (eval_ocmp s (S.OGt o1 o2))]

val lemma_valid_cmp_eq : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures valid_operand o1 s /\ valid_operand o2 s ==> valid_ocmp (S.OEq o1 o2) s)
  [SMTPat (valid_ocmp (S.OEq o1 o2) s)]

val lemma_valid_cmp_ne : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures valid_operand o1 s /\ valid_operand o2 s ==> valid_ocmp (S.ONe o1 o2) s)
  [SMTPat (valid_ocmp (S.ONe o1 o2) s)]

val lemma_valid_cmp_le : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures valid_operand o1 s /\ valid_operand o2 s ==> valid_ocmp (S.OLe o1 o2) s)
  [SMTPat (valid_ocmp (S.OLe o1 o2) s)]

val lemma_valid_cmp_ge : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures valid_operand o1 s /\ valid_operand o2 s ==> valid_ocmp (S.OGe o1 o2) s)
  [SMTPat (valid_ocmp (S.OGe o1 o2) s)]

val lemma_valid_cmp_lt : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures valid_operand o1 s /\ valid_operand o2 s ==> valid_ocmp (S.OLt o1 o2) s)
  [SMTPat (valid_ocmp (S.OLt o1 o2) s)]

val lemma_valid_cmp_gt : s:state -> o1:operand -> o2:operand -> Lemma
  (ensures valid_operand o1 s /\ valid_operand o2 s ==> valid_ocmp (S.OGt o1 o2) s)
  [SMTPat (valid_ocmp (S.OGt o1 o2) s)]

val compute_merge_total (f0:fuel) (fM:fuel) : fuel

val lemma_merge_total (b0:codes) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) : Lemma
  (requires
    Cons? b0 /\
    eval_code (Cons?.hd b0) s0 f0 sM /\
    eval_code (Block (Cons?.tl b0)) sM fM sN
  )
  (ensures eval_code (Block b0) s0 (compute_merge_total f0 fM) sN)

val lemma_empty_total (s0:state) (bN:codes) : Ghost ((sM:state) * (fM:fuel))
  (requires True)
  (ensures (fun (sM, fM) ->
    s0 == sM /\
    eval_code (Block []) s0 fM sM
  ))

val lemma_ifElse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) : Ghost (bool * state * state * fuel)
  (requires True)
  (ensures  (fun (cond, sM, sN, f0) ->
    cond == eval_ocmp s0 ifb /\
    sM == s0
  ))

val lemma_ifElseTrue_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) : Lemma
  (requires
    valid_ocmp ifb s0 /\
    eval_ocmp s0 ifb /\
    eval_code ct s0 f0 sM
  )
  (ensures
    eval_code (IfElse ifb ct cf) s0 f0 sM
  )

val lemma_ifElseFalse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) : Lemma
  (requires
    valid_ocmp ifb s0 /\
    not (eval_ocmp s0 ifb) /\
    eval_code cf s0 f0 sM
  )
  (ensures
    eval_code (IfElse ifb ct cf) s0 f0 sM
  )

val eval_while_inv (c:code) (s0:state) (fW:fuel) (sW:state) : Type0

val lemma_while_total (b:ocmp) (c:code) (s0:state) : Ghost ((s1:state) * (f1:fuel))
  (requires True)
  (ensures fun (s1, f1) ->
    s1 == s0 /\
    eval_while_inv (While b c) s1 f1 s1
  )

val lemma_whileTrue_total (b:ocmp) (c:code) (s0:state) (sW:state) (fW:fuel) : Ghost ((s1:state) * (f1:fuel))
  (requires eval_ocmp sW b)
  (ensures fun (s1, f1) -> s1 == sW /\ f1 == fW)

val lemma_whileFalse_total (b:ocmp) (c:code) (s0:state) (sW:state) (fW:fuel) : Ghost ((s1:state) * (f1:fuel))
  (requires
    valid_ocmp b sW /\
    not (eval_ocmp sW b) /\
    eval_while_inv (While b c) s0 fW sW
  )
  (ensures fun (s1, f1) ->
    s1 == sW /\
    eval_code (While b c) s0 f1 s1
  )

val lemma_whileMerge_total (c:code) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) : Ghost (fN:fuel)
  (requires
    While? c /\
    sN.ok /\
    valid_ocmp (While?.whileCond c) sM /\
    eval_ocmp sM (While?.whileCond c) /\
    eval_while_inv c s0 f0 sM /\
    eval_code (While?.whileBody c) sM fM sN
  )
  (ensures (fun fN ->
    eval_while_inv c s0 fN sN
  ))

