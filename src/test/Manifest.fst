module Manifest
open FStar.UInt64

type uint64 = FStar.UInt64.t

type argtype =
  | AInt : argtype
  | AChar: argtype
  
type calltable_entry =
  |Mkcalltable_entry : fname:string -> fstart_address : int -> fsize:int -> args: (list argtype) -> calltable_entry

type calltable = 
  | MkCalltable : calltable_start:int -> calltable_size: uint64 -> entries: (list calltable_entry) -> calltable

type umemlayout =
 | MkUmemlayout : bitmap_address:int -> bitmap_size:uint64 ->
		   ctable: calltable ->
		   code_start:int -> code_size: uint64 ->
		   heap_start: int -> heap_and_stack_size:uint64 ->
		   stack_start:int -> umemlayout


let get_bitmap_start (m:umemlayout) = m.bitmap_address
let get_calltable_start (m:umemlayout) = m.ctable.calltable_start
let get_code_start (m:umemlayout) = m.code_start
let get_heap_start (m:umemlayout) = m.heap_start
let get_stack_start (m:umemlayout) = m.stack_start

let address_within_procedure (fname:string) (dst:int) (env:umemlayout) = true
 
