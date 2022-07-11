module PPC64LE.Vale.Lemmas
open PPC64LE.Machine_s
open PPC64LE.Vale.State
module S = PPC64LE.Semantics_s

#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 20"

let rec increase_fuel (c:code) (s0:state) (f0:fuel) (sN:state) (fN:fuel) : Lemma
  (requires eval_code c s0 f0 sN /\ f0 <= fN)
  (ensures eval_code c s0 fN sN)
  (decreases %[f0; c])
  =
  match c with
  | Ins ins -> ()
  | Block l -> increase_fuels l s0 f0 sN fN
  | IfElse cond t f ->
      let (s0, b) = S.run_ocmp s0 cond in
      if b then increase_fuel t s0 f0 sN fN else increase_fuel f s0 f0 sN fN
  | While cond c ->
      let (s0, b) = S.run_ocmp s0 cond in
      if not b then ()
      else
      (
        match S.eval_code c (f0 - 1) s0 with
        | None -> ()
        | Some s1 ->
            increase_fuel c s0 (f0 - 1) s1 (fN - 1);
            if s1.ok then increase_fuel (While cond c) s1 (f0 - 1) sN (fN - 1)
            else ()
      )
and increase_fuels (c:codes) (s0:state) (f0:fuel) (sN:state) (fN:fuel) : Lemma
  (requires eval_code (Block c) s0 f0 sN /\ f0 <= fN)
  (ensures eval_code (Block c) s0 fN sN)
  (decreases %[f0; c])
  =
  match c with
  | [] -> ()
  | h::t ->
    (
      let Some s1 = S.eval_code h f0 s0 in
      increase_fuel h s0 f0 s1 fN;
      increase_fuels t s1 f0 sN fN
    )

let lemma_cmp_eq s o1 o2 = ()
let lemma_cmp_ne s o1 o2 = ()
let lemma_cmp_le s o1 o2 = ()
let lemma_cmp_ge s o1 o2 = ()
let lemma_cmp_lt s o1 o2 = ()
let lemma_cmp_gt s o1 o2 = ()

let lemma_valid_cmp_eq s o1 o2 = ()
let lemma_valid_cmp_ne s o1 o2 = ()
let lemma_valid_cmp_le s o1 o2 = ()
let lemma_valid_cmp_ge s o1 o2 = ()
let lemma_valid_cmp_lt s o1 o2 = ()
let lemma_valid_cmp_gt s o1 o2 = ()

let compute_merge_total (f0:fuel) (fM:fuel) =
  if f0 > fM then f0 else fM

let lemma_merge_total (b0:codes) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) =
  let f = if f0 > fM then f0 else fM in
  increase_fuel (Cons?.hd b0) s0 f0 sM f;
  increase_fuel (Block (Cons?.tl b0)) sM fM sN f

let lemma_empty_total (s0:state) (bN:codes) =
  (s0, 0)

let lemma_ifElse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) =
  (eval_ocmp s0 ifb, ({s0 with cr0 = S.eval_cmp_cr0 s0 ifb}), s0, 0)

let lemma_ifElseTrue_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) =
  ()

let lemma_ifElseFalse_total (ifb:ocmp) (ct:code) (cf:code) (s0:state) (f0:fuel) (sM:state) =
  ()

let eval_while_inv_temp (c:code) (s0:state) (fW:fuel) (sW:state) : Type0 =
  forall (f:nat).{:pattern S.eval_code c f sW}
    Some? (S.eval_code c f sW) ==>
    S.eval_code c (f + fW) s0 == S.eval_code c f sW

let eval_while_inv (c:code) (s0:state) (fW:fuel) (sW:state) : Type0 =
  eval_while_inv_temp c s0 fW sW

let lemma_while_total (b:ocmp) (c:code) (s0:state) =
  (s0, 0)

let lemma_whileTrue_total (b:ocmp) (c:code) (s0:state) (sW:state) (fW:fuel) =
  ({sW with cr0 = S.eval_cmp_cr0 sW b}, fW)

let lemma_whileFalse_total (b:ocmp) (c:code) (s0:state) (sW:state) (fW:fuel) =
  let f1 = fW + 1 in
  let (s1, _) = S.run_ocmp sW b in
  assert (S.eval_code (While b c) f1 s0 == S.eval_code (While b c) 1 sW);
  assert (eval_code (While b c) s0 f1 s1);
  (s1, f1)

#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 30"
let lemma_whileMerge_total (c:code) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) =
  let cond = While?.whileCond c in
  let fN:nat = f0 + fM + 1 in
  let fForall (f:nat) : Lemma
    (requires Some? (S.eval_code c f sN))
    (ensures S.eval_code c (f + fN) s0 == S.eval_code c f sN) =
    let Some sZ = S.eval_code c f sN in
    let fZ = if f > fM then f else fM in
    let sM' = {sM with cr0 = S.eval_cmp_cr0 sM cond} in
    increase_fuel (While?.whileBody c) sM' fM sN fZ;
    increase_fuel c sN f sZ fZ;
    assert (S.eval_code c (fZ + 1) sM == Some sZ);
    assert (S.eval_code c (fZ + 1) sM == S.eval_code c (fZ + 1 + f0) s0);
    assert (S.eval_code c (fZ + 1 + f0) s0 == Some sZ);
    increase_fuel c s0 (fZ + 1 + f0) sZ (f + fN);
    assert (S.eval_code c (f + fN) s0 == Some sZ);
    ()
    in
  Classical.ghost_lemma fForall;
  fN
