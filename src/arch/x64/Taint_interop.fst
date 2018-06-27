module Taint_interop

module B = LowStar.Buffer
module MT = X64.Vale.Memtaint_i
open X64.Machine_s
open Interop
open X64.Memory_i_s


// TODO
assume val correct_down_taint:(memTaint:MT.t) -> 
                       (mem:mem) ->
		       (bytesTaint:memTaint_t) ->
		       Type0

assume val down_taint: (memTaint:MT.t) -> 
		       (mem:mem) ->
		       GTot (bytesTaint:memTaint_t{correct_down_taint memTaint mem bytesTaint})

assume val up_taint: (bytesTaint:memTaint_t) ->
                     (mem:mem) ->
		     GTot (memTaint:MT.t)

assume val up_down_identity: (memTaint:MT.t) ->
			     (mem:mem) ->
			     Lemma (up_taint (down_taint memTaint mem) mem == memTaint)

assume val down_up_identity: (bytesTaint:memTaint_t) ->
			     (mem:mem) ->
			     Lemma (down_taint (up_taint bytesTaint mem) mem == bytesTaint)
