module AES_s

open Types_s

assume val mix_columns (q:quad32) : quad32
assume val inv_mix_columns (q:quad32) : quad32
assume val sub_bytes (q:quad32) : quad32
assume val inv_sub_bytes (q:quad32) : quad32
assume val shift_rows (q:quad32) : quad32
assume val inv_shift_rows (q:quad32) : quad32
assume val rot_word (w:nat32) : nat32
assume val sub_word (w:nat32) : nat32
