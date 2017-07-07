module X64.Vale.Lemmas_i
open X64.Machine_s
open X64.Vale.State_i
open X64.Vale.StateLemmas_i
open FStar.UInt
module S = X64.Semantics_s

unfold let code = S.code
unfold let codes = S.codes

let cf (flags:int) : bool = S.cf (S.u (int_to_nat64 flags))
let zf (flags:int) : bool = S.zf (S.u (int_to_nat64 flags))

let eval_code (c:code) (s:state) : option state =
  match S.eval_code c (state_to_S s) with
  | None -> None
  | Some s -> Some (state_of_S s)

let eval_ocmp (s:state) (c:S.ocmp) : bool = S.eval_ocmp (state_to_S s) c

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

val lemma_block : (b0:codes) -> (s0:state) -> (sN:state) ->
  Ghost (state * code * codes)
  (requires (Cons? b0 /\ Some sN == eval_code (Block b0) s0))
  (ensures  (fun (s1, c1, b1) ->
    b0 == c1::b1 /\
    Some s1 == eval_code c1 s0 /\
    Some sN == eval_code (Block b1) s1))

val lemma_empty : (s0:state) -> (sN:state) -> Ghost state
  (requires (Some sN == eval_code (Block []) s0))
  (ensures  (fun sM -> sM == s0 /\ sM == sN))

val lemma_ifElse : ifb:S.ocmp -> ct:code -> cf:code -> s0:state -> sN:state -> Ghost (bool * state)
  (requires (Some sN == eval_code (IfElse ifb ct cf) s0))
  (ensures  (fun (cond, sM) ->
    cond == eval_ocmp s0 ifb /\
    sM == s0 /\
    Some sN == (if cond then eval_code ct sM else eval_code cf sM)))
