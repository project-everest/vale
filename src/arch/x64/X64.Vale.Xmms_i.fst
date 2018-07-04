module X64.Vale.Xmms_i
open X64.Machine_s
open FStar.FunctionalExtensionality

let equal xmms1 xmms2 = xmms1 == xmms2
let lemma_equal_intro xmms1 xmms2 = Map16_i.lemma_equal xmms1 xmms2
let lemma_equal_elim xmms1 xmms2 = ()

