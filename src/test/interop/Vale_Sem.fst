module Vale_Sem

open FStar.BaseTypes
open FStar.Map
open Machine_int
open FStar.UInt
open FStar.UInt8

type heap = (m:Map.t int uint8{Map.domain m == Set.complement Set.empty})
let op_String_Access = Map.sel
let op_String_Assignment = Map.upd

noeq type state = {
  ok: bool;
  regs: reg -> nat64;
  mem: heap;
}

let eval_reg (r:reg) (s:state) : nat64 = s.regs r

let eval_maddr (m:maddr) (s:state) : int =
  match m with 
  | MConst n -> n
  | MReg r offset -> (eval_reg r s) + offset

let get_heap_val (ptr:int) (mem:heap) : nat64 =
    UInt8.v (mem.[ptr]) + 
    UInt8.v (mem.[ptr+1]) `op_Multiply` 0x100 + 
    UInt8.v (mem.[ptr+2]) `op_Multiply` 0x10000 +
    UInt8.v (mem.[ptr+3]) `op_Multiply` 0x1000000 + 
    UInt8.v (mem.[ptr+4]) `op_Multiply` 0x100000000 +
    UInt8.v (mem.[ptr+5]) `op_Multiply` 0x10000000000 +
    UInt8.v (mem.[ptr+6]) `op_Multiply` 0x1000000000000 +
    UInt8.v (mem.[ptr+7]) `op_Multiply` 0x100000000000000

let get_heap_value (ptr:int) (s:state) : nat64 =
    let mem = s.mem in
    get_heap_val ptr mem

val mod_8: (n:nat64) -> uint8

let mod_8 n =
  UInt8.uint_to_t (n % 0x100)

#set-options "--z3rlimit 20"

private let aux0 (ptr:int) (mem:heap) : Lemma (mod_8 (get_heap_val ptr mem) == mem.[ptr]) = ()
private let aux1 (ptr:int) (mem:heap) : Lemma 
    (mod_8 ((get_heap_val ptr mem) `op_Division` 0x100) == mem.[ptr + 1]) = ()
private let aux2 (ptr:int) (mem:heap) : Lemma 
    (mod_8 ((get_heap_val ptr mem) `op_Division` 0x10000) == mem.[ptr + 2]) = ()

#set-options "--z3rlimit 40"

private let aux3 (ptr:int) (mem:heap) : Lemma 
    (mod_8 ((get_heap_val ptr mem) `op_Division` 0x1000000) == mem.[ptr + 3]) = ()

#set-options "--z3rlimit 200"

private let aux4 (ptr:int) (mem:heap) : Lemma 
    (mod_8 ((get_heap_val ptr mem) `op_Division` 0x100000000) == mem.[ptr + 4]) = ()
    
private let aux5 (ptr:int) (mem:heap) : Lemma 
    (mod_8 ((get_heap_val ptr mem) `op_Division` 0x10000000000) == mem.[ptr + 5]) = ()

private let aux6 (ptr:int) (mem:heap) : Lemma 
    (mod_8 ((get_heap_val ptr mem) `op_Division` 0x1000000000000) == mem.[ptr + 6]) = ()    

private let aux7 (ptr:int) (mem:heap) : Lemma 
    (mod_8 ((get_heap_val ptr mem) `op_Division` 0x100000000000000) == mem.[ptr + 7]) = ()

let same_mem_get_heap_val (ptr:int) (mem1 mem2:heap) : Lemma
  (requires get_heap_val ptr mem1 == get_heap_val ptr mem2)
  (ensures forall i. i >= ptr /\ i < ptr + 8 ==> mem1.[i] == mem2.[i]) =
  aux0 ptr mem1;
  aux0 ptr mem2;
  aux1 ptr mem1;
  aux1 ptr mem2;
  aux2 ptr mem1;
  aux2 ptr mem2;
  aux3 ptr mem1;
  aux3 ptr mem2;
  aux4 ptr mem1;
  aux4 ptr mem2;
  aux5 ptr mem1;
  aux5 ptr mem2;
  aux6 ptr mem1;
  aux6 ptr mem2;
  aux7 ptr mem1;
  aux7 ptr mem2;
  ()

let eval_operand (o:operand) (s:state) : nat64 = match o with
  | OConst n -> n
  | OReg r -> eval_reg r s
  | OMem m -> get_heap_value (eval_maddr m s) s

let valid_maddr (m:maddr) (s:state) : bool = 0 <= eval_maddr m s && eval_maddr m s < nat64_max

let valid_operand (o:operand) (s:state) : bool =
  match o with
  | OConst _ | OReg _ -> true
  | OMem m -> valid_maddr m s

let update_reg (r:reg) (v:nat64) (s:state) : state =
  { s with regs = fun r' -> if r' = r then v else s.regs r' }

let update_heap (ptr:int) (v:nat64) (mem:heap) : heap =
  let mem = mem.[ptr] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+1] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+2] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+3] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+4] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+5] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+6] <- (mod_8 v) in
  let v = v `op_Division` 0x100 in
  let mem = mem.[ptr+7] <- (mod_8 v) in
  assert (Set.equal (Map.domain mem) (Set.complement Set.empty));
  mem

let frame_update_heap (ptr:int) (v:nat64) (mem:heap) : Lemma (
  let new_mem = update_heap ptr v mem in
  forall j. {:pattern (new_mem.[j]); (mem.[j])} j < ptr \/ j >= ptr + 8 ==> mem.[j] == new_mem.[j]) = ()

let update_mem (ptr:int) (v:nat64) (s:state) : state =
  let mem = s.mem in
  let mem = update_heap ptr v mem in
  {s with mem = mem}

let correct_update_get (ptr:int) (v:nat64) (mem:heap) : Lemma (
  get_heap_val ptr (update_heap ptr v mem) == v)
  [SMTPat (get_heap_val ptr (update_heap ptr v mem))] = ()

let update_dst (dst:dst_op) (v:nat64) (s:state) : state = match dst with
  | OReg r -> update_reg r v s
  | OMem m -> update_mem (eval_maddr m s) v s

let eval_ins (ins:code) (s:state) : state =
  match ins with 
  | Mov dst src -> if not (valid_operand dst s && valid_operand src s) then {s with ok = false}
	else 
	let v = eval_operand src s in
	update_dst dst v s
  | Add dst src -> if not (valid_operand dst s && valid_operand src s) then {s with ok = false}
    else
    let v = (eval_operand src s + eval_operand dst s) % nat64_max in
    // Flags ignored
    update_dst dst v s
