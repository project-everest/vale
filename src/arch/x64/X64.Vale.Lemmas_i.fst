module X64.Vale.Lemmas_i
open X64.Machine_s
open X64.Vale.State_i
open X64.Vale.StateLemmas_i
open FStar.UInt
open FStar.FunctionalExtensionality
open FStar.Tactics
module S = X64.Semantics_s
module TS = X64.Taint_Semantics_s

#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 20"

val increase_fuel (c:code) (s0:state) (f0:fuel) (sN:state) (fN:fuel) : Lemma
  (requires eval_code c s0 f0 sN /\ f0 <= fN)
  (ensures eval_code c s0 fN sN)
  (decreases %[f0; c])

val increase_fuels (c:codes) (s0:state) (f0:fuel) (sN:state) (fN:fuel) : Lemma
  (requires eval_code (Block c) s0 f0 sN /\ f0 <= fN)
  (ensures eval_code (Block c) s0 fN sN)
  (decreases %[f0; c])

let rec increase_fuel (c:code) (s0:state) (f0:fuel) (sN:state) (fN:fuel) =
  match c with
  | Ins ins -> ()
  | Block l -> increase_fuels l s0 f0 sN fN
  | IfElse b t f ->
      let s1 = ensure_valid_ocmp b s0 in
      let b0 = eval_ocmp s1 b in
      let s2 = {s1 with trace = BranchPredicate(b0)::s1.trace} in
      assert (feq ((state_to_S ({s1 with trace = BranchPredicate(b0)::s1.trace})).TS.state.S.regs)
	({(state_to_S s1) with TS.trace = BranchPredicate(b0)::(state_to_S s1).TS.trace}).TS.state.S.regs);
      if b0 then increase_fuel t s2 f0 sN fN else increase_fuel f s2 f0 sN fN
  | While b c ->
      let s0 = ensure_valid_ocmp b s0 in
      let b0 = eval_ocmp s0 b in
      if not b0 then ()
      else
      (
	let s1 = {s0 with trace = BranchPredicate(true)::s0.trace} in
	assert (feq ((state_to_S ({s0 with trace = BranchPredicate(true)::s0.trace})).TS.state.S.regs)
	({(state_to_S s0) with TS.trace = BranchPredicate(b0)::(state_to_S s0).TS.trace}).TS.state.S.regs);
        match TS.taint_eval_code c (f0 - 1) (state_to_S s1) with
        | None -> ()
        | Some s2 ->
            let s2 = state_of_S s2 in
            increase_fuel c s1 (f0 - 1) s2 (fN - 1);
            if s2.ok then increase_fuel (While b c) s2 (f0 - 1) sN (fN - 1)
            else ()
      ) 
and increase_fuels (c:codes) (s0:state) (f0:fuel) (sN:state) (fN:fuel) =
  match c with
  | [] -> ()
  | h::t ->
    (
      let Some s1 = TS.taint_eval_code h f0 (state_to_S s0) in
      let s1 = state_of_S s1 in
      increase_fuel h s0 f0 s1 fN;
      increase_fuels t s1 f0 sN fN
    )

let lemma_cmp_eq s o1 o2 t = ()
let lemma_cmp_ne s o1 o2 t = ()
let lemma_cmp_le s o1 o2 t = ()
let lemma_cmp_ge s o1 o2 t = ()
let lemma_cmp_lt s o1 o2 t = ()
let lemma_cmp_gt s o1 o2 t = ()

let lemma_valid_cmp_eq s o1 o2 t = ()
let lemma_valid_cmp_ne s o1 o2 t = ()
let lemma_valid_cmp_le s o1 o2 t = ()
let lemma_valid_cmp_ge s o1 o2 t = ()
let lemma_valid_cmp_lt s o1 o2 t = ()
let lemma_valid_cmp_gt s o1 o2 t = ()

let lemma_merge_total (b0:codes) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) =
  let f = if f0 > fM then f0 else fM in
  increase_fuel (Cons?.hd b0) s0 f0 sM f;
  increase_fuel (Block (Cons?.tl b0)) sM fM sN f;
  f

let lemma_empty_total (s0:state) (bN:codes) =
  (s0, 0)

let lemma_ifElse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) =
  let cond = eval_ocmp s0 ifb in
  (cond, {s0 with trace = BranchPredicate(cond)::s0.trace}, s0, 0)

let lemma_ifElseTrue_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) =
  assert (feq ((state_to_S ({s0 with trace = BranchPredicate(true)::s0.trace})).TS.state.S.regs)
    ({(state_to_S s0) with TS.trace = BranchPredicate(true)::(state_to_S s0).TS.trace}).TS.state.S.regs);
  ()

let lemma_ifElseFalse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) =
  assert (feq ((state_to_S ({s0 with trace = BranchPredicate(false)::s0.trace})).TS.state.S.regs)
    ({(state_to_S s0) with TS.trace = BranchPredicate(false)::(state_to_S s0).TS.trace}).TS.state.S.regs);
  ()

let eval_while_inv_temp (c:code) (s0:state) (fW:fuel) (sW:state) : Type0 =
  forall (f:nat).{:pattern TS.taint_eval_code c f (state_to_S sW)}
    Some? (TS.taint_eval_code c f (state_to_S sW)) ==>
    TS.taint_eval_code c (f + fW) (state_to_S s0) == TS.taint_eval_code c f (state_to_S sW)

let eval_while_inv (c:code) (s0:state) (fW:fuel) (sW:state) : Type0 =
  eval_while_inv_temp c s0 fW sW

let lemma_while_total (b:ocmp) (c:code) (s0:state) =
  (s0, 0)

let lemma_whileTrue_total (b:ocmp) (c:code) (s0:state) (sW:state) (fW:fuel) =
  (sW, fW)

let lemma_whileFalse_total (b:ocmp) (c:code) (s0:state) (sW:state) (fW:fuel) =
  let f1 = fW + 1 in
  assert (TS.taint_eval_code (While b c) f1 (state_to_S s0) == TS.taint_eval_code (While b c) 1 (state_to_S sW));
  assert (feq ((state_to_S ({sW with trace = BranchPredicate(false)::sW.trace})).TS.state.S.regs)
    ({(state_to_S sW) with TS.trace = BranchPredicate(false)::(state_to_S sW).TS.trace}).TS.state.S.regs);
  assert (eval_code (While b c) s0 f1 ({sW with trace = BranchPredicate(false)::sW.trace}));
  ({sW with trace = BranchPredicate(false)::sW.trace}, f1)
  
#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 30"
let lemma_whileMerge_total (c:code) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) =
  let fN:nat = f0 + fM + 1 in
  let fForall (f:nat) : Lemma
    (requires Some? (TS.taint_eval_code c f (state_to_S sN)))
    (ensures TS.taint_eval_code c (f + fN) (state_to_S s0) == TS.taint_eval_code c f (state_to_S sN)) =
    let Some sZ = TS.taint_eval_code c f (state_to_S sN) in
    let fZ = if f > fM then f else fM in
    increase_fuel (While?.whileBody c) ({sM with trace = BranchPredicate(true)::sM.trace}) fM sN fZ;
    increase_fuel c sN f (state_of_S sZ) fZ;
    assert (feq ((state_to_S ({sM with trace = BranchPredicate(true)::sM.trace})).TS.state.S.regs) ({(state_to_S sM) with TS.trace = BranchPredicate(true)::(state_to_S sM).TS.trace}).TS.state.S.regs);
    assert (TS.taint_eval_code c (fZ + 1) (state_to_S sM) == Some sZ);
    assert (TS.taint_eval_code c (fZ + 1) (state_to_S sM) == TS.taint_eval_code c (fZ + 1 + f0) (state_to_S s0));
    assert (TS.taint_eval_code c (fZ + 1 + f0) (state_to_S s0) == Some sZ);
    increase_fuel c s0 (fZ + 1 + f0) (state_of_S sZ) (f + fN);
    assert (TS.taint_eval_code c (f + fN) (state_to_S s0) == Some sZ);
    ()
    in
  Classical.ghost_lemma fForall;
  fN
