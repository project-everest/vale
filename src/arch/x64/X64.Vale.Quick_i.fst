module X64.Vale.Quick_i

let rec wp_sound #a cs fcs p s0 =
  match fcs with
  | QEmpty g ->
      let (sN, fN) = va_lemma_empty_total s0 [] in (sN, fN, g)
  | QSeq fc fcs ->
      let QProc _ wp1' proof = fc in
      let c::cs = cs in
      let wp_continue = wp_Seq cs fcs p in
      let qs (sM:state) ((sN:state), (fN:fuel), (gN:a)) : Type0 = eval (Block cs) sM fN sN /\ p sN gN in
      let (|sM, fM, g1, pp|) = proof a qs s0 wp_continue in
      let q = qs sM in
      let proof_continue () : Ghost ((sN:state) * (fN:fuel) * (gN:a))
        (requires wp_continue sM g1)
        (ensures q) =
        //assert (wp_continue sM g1);
        //assert (wp cs fcs p sM);
        wp_sound cs fcs p sM
        in
      let (sN, fN, gN) = pp proof_continue in
      let fN' = va_lemma_merge_total (c::cs) s0 fM sM fN sN in
      (sN, fN', gN)
  | QBind fc fcs ->
      let QProc c' wp1' proof = fc in
      let c::cs = cs in
      let wp_continue = wp_Bind cs fcs p in
      let qs (sM:state) ((sN:state), (fN:fuel), (gN:a)) : Type0 = eval (Block cs) sM fN sN /\ p sN gN in
      let (|sM, fM, g1, pp|) = proof a qs s0 wp_continue in
      let q = qs sM in
      let proof_continue () : Ghost ((sN:state) * (fN:fuel) * (gN:a))
        (requires wp_continue sM g1)
        (ensures q) =
        //assert (wp_continue sM g1);
        //assert (wp cs (fcs g1) p sM);
        wp_sound cs (fcs g1) p sM
        in
      let (sN, fN, gN) = pp proof_continue in
      let fN' = va_lemma_merge_total (c::cs) s0 fM sM fN sN in
      (sN, fN', gN)
  | QGetState f ->
      let c::cs = cs in
      let (sM, fM) = va_lemma_empty_total s0 [] in
      let (sN, fN, gN) = wp_sound cs (f sM) p sM in
      let fN' = va_lemma_merge_total (c::cs) s0 fM sM fN sN in
      (sN, fN', gN)
  | QLemma pre post l fcs' ->
      let _ = FStar.Classical.arrow_to_impl #pre #post l in
      wp_sound cs fcs' p s0

