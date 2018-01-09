module X64.Vale.Quick_i

let rec wp_monotone #a cs qcs k1 k2 s0 =
  match qcs with
  | QEmpty g -> ()
  | QSeq qc qcs ->
      let QProc _ wp1' monotone _ _ = qc in
      let c::cs = cs in
      let k1' = wp_Seq cs qcs k1 in
      let k2' = wp_Seq cs qcs k2 in
      let f s g : Lemma (k1' s g ==> k2' s g) =
        wp_monotone cs qcs k1 k2 s
        in
      FStar.Classical.forall_intro_2 f;
      assert (forall s g. k1' s g ==> k2' s g);
      monotone s0 k1' k2'
  | QBind qc qcs ->
      let QProc c' wp1' monotone _ _ = qc in
      let c::cs = cs in
      let k1' = wp_Bind cs qcs k1 in
      let k2' = wp_Bind cs qcs k2 in
      let f s g : Lemma (k1' s g ==> k2' s g) =
        wp_monotone cs (qcs g) k1 k2 s
        in
      FStar.Classical.forall_intro_2 f;
      monotone s0 k1' k2'
  | QGetState f ->
      let c::cs = cs in
      wp_monotone cs (f s0) k1 k2 s0
  | QLemma pre post l qcs' ->
      wp_monotone cs qcs' k1 k2 s0

let rec wp_compute #a cs qcs s0 =
  match qcs with
  | QEmpty g ->
      let (sN, fN) = va_lemma_empty_total s0 [] in (sN, fN, g)
  | QSeq qc qcs ->
      let QProc _ wp1' monotone compute proof = qc in
      let c::cs = cs in
      let k' = wp_Seq cs qcs k_true in
      monotone s0 k' k_true;
      let (sM, fM, gM) = compute s0 in
      proof s0 k';
      let (sN, fN, gN) = wp_compute cs qcs sM in
      let fN' = va_compute_merge_total fM fN in
      (sN, fN', gN)
  | QBind qc qcs ->
      let QProc c' wp1' monotone compute proof = qc in
      let c::cs = cs in
      let k' = wp_Bind cs qcs k_true in
      monotone s0 k' k_true;
      let (sM, fM, gM) = compute s0 in
      proof s0 k';
      let (sN, fN, gN) = wp_compute cs (qcs gM) sM in
      let fN' = va_compute_merge_total fM fN in
      (sN, fN', gN)
  | QGetState f ->
      let c::cs = cs in
      let (sM, fM) = va_lemma_empty_total s0 [] in
      let (sN, fN, gN) = wp_compute cs (f sM) sM in
      let fN' = va_compute_merge_total fM fN in
      (sN, fN', gN)
  | QLemma pre post l qcs' ->
      l ();
      wp_compute cs qcs' s0

let rec wp_sound #a cs qcs k s0 =
  match qcs with
  | QEmpty g ->
      let (sN, fN) = va_lemma_empty_total s0 [] in ()
  | QSeq qc qcs ->
      let QProc _ wp1' monotone compute proof = qc in
      let c::cs = cs in
      let k' = wp_Seq cs qcs k in
      monotone s0 k' k_true;
      let (sM, fM, gM) = compute s0 in
      proof s0 k';
      wp_monotone cs qcs k k_true sM;
      let (sN, fN, gN) = wp_compute cs qcs sM in
      wp_sound cs qcs k sM;
      let fN' = va_lemma_merge_total (c::cs) s0 fM sM fN sN in
      ()
  | QBind qc qcs ->
      let QProc c' wp1' monotone compute proof = qc in
      let c::cs = cs in
      let k' = wp_Bind cs qcs k in
      monotone s0 k' k_true;
      let (sM, fM, gM) = compute s0 in
      proof s0 k';
      wp_monotone cs (qcs gM) k k_true sM;
      let (sN, fN, gN) = wp_compute cs (qcs gM) sM in
      wp_sound cs (qcs gM) k sM;
      let fN' = va_lemma_merge_total (c::cs) s0 fM sM fN sN in
      ()
  | QGetState f ->
      let c::cs = cs in
      let (sM, fM) = va_lemma_empty_total s0 [] in
      wp_sound cs (f sM) k sM;
      wp_monotone cs (f sM) k k_true sM;
      let (sN, fN, gN) = wp_compute cs (f sM) sM in
      let fN' = va_lemma_merge_total (c::cs) s0 fM sM fN sN in
      ()
  | QLemma pre post l qcs' ->
      l ();
      wp_sound cs qcs' k s0

let qblock_monotone #a #cs qcs s0 k1 k2 =
  wp_monotone cs qcs k1 k2 s0

let qblock_compute #a #cs qcs s0 =
  wp_compute cs qcs s0

let qblock_proof #a #cs qcs s0 k =
  wp_monotone cs qcs k k_true s0;
  let (sM, f0, g) = wp_compute cs qcs s0 in
  wp_sound cs qcs k s0

let wp_sound_code #a c qc k s0 =
  let QProc c wp monotone compute proof = qc in
  monotone s0 k k_true;
  let (sM, f0, g) = compute s0 in
  proof s0 k;
  (sM, f0, g)

let wp_sound_wrap #a cs qcs s0 k = wp_sound cs qcs (k s0) s0; wp_monotone cs qcs (k s0) k_true s0; wp_compute cs qcs s0
let wp_sound_code_wrap #a c qc s0 k = wp_sound_code c qc (k s0) s0

