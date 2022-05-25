module PPC64LE.Semantics_s

open FStar.Mul
open Defs_s
open PPC64LE.Machine_s
open Words_s
open Words.Two_s
open Words.Four_s
open Types_s

let (.[]) = Map.sel
let (.[]<-) = Map.upd

type ins =
  | Move         : dst:reg -> src:reg -> ins
  | Load64       : dst:reg -> src:maddr -> ins
  | Store64      : src:reg -> dst:maddr -> ins
  | LoadImm64    : dst:reg -> src:simm16 -> ins
  | AddLa        : dst:reg -> src1:reg -> src2:simm16 -> ins
  | Add          : dst:reg -> src1:reg -> src2:reg -> ins
  | AddImm       : dst:reg -> src1:reg -> src2:simm16 -> ins
  | AddExtended  : dst:reg -> src1:reg -> src2:reg -> ins
  | AddExtendedOV: dst:reg -> src1:reg -> src2:reg -> ins
  | Sub          : dst:reg -> src1:reg -> src2:reg -> ins
  | SubImm       : dst:reg -> src1:reg -> src2:nsimm16 -> ins
  | MulLow64     : dst:reg -> src1:reg -> src2:reg -> ins
  | MulHigh64U   : dst:reg -> src1:reg -> src2:reg -> ins
  | Xor          : dst:reg -> src1:reg -> src2:reg -> ins
  | And          : dst:reg -> src1:reg -> src2:reg -> ins
  | Sr64Imm      : dst:reg -> src1:reg -> src2:bits64 -> ins
  | Sl64Imm      : dst:reg -> src1:reg -> src2:bits64 -> ins
  | Mfvsrd       : dst:reg -> src:vec -> ins
  | Mfvsrld      : dst:reg -> src:vec -> ins
  | Mtvsrdd      : dst:vec -> src1:reg -> src2:reg -> ins
  | Vxor         : dst:vec -> src1:vec -> src2:vec -> ins
  | Vslw         : dst:vec -> src1:vec -> src2:vec -> ins
  | Vsrw         : dst:vec -> src1:vec -> src2:vec -> ins
  | Vcmpequw     : dst:vec -> src1:vec -> src2:vec -> ins
  | Vsldoi       : dst:vec -> src1:vec -> src2:vec -> count:quad32bytes -> ins

type ocmp =
  | OEq: o1:cmp_opr -> o2:cmp_opr -> ocmp
  | ONe: o1:cmp_opr -> o2:cmp_opr -> ocmp
  | OLe: o1:cmp_opr -> o2:cmp_opr -> ocmp
  | OGe: o1:cmp_opr -> o2:cmp_opr -> ocmp
  | OLt: o1:cmp_opr -> o2:cmp_opr -> ocmp
  | OGt: o1:cmp_opr -> o2:cmp_opr -> ocmp

type code = precode ins ocmp
type codes = list code

unfold let eval_reg (r:reg) (s:state) : nat64 = s.regs r
unfold let eval_vec (v:vec) (s:state) : quad32 = s.vecs v
unfold let eval_mem64 (ptr:int) (s:state) : nat64 = load_mem64 ptr s.mem

[@va_qattr]
let eval_maddr (m:maddr) (s:state) : int =
  eval_reg m.address s + m.offset

let eval_cmp_opr (o:cmp_opr) (s:state) : nat64 =
  match o with
  | CReg r -> eval_reg r s
  | CImm n -> int_to_nat64 n

let eval_ocmp (s:state) (c:ocmp) :bool =
  match c with
  | OEq o1 o2 -> eval_cmp_opr o1 s = eval_cmp_opr o2 s
  | ONe o1 o2 -> eval_cmp_opr o1 s <> eval_cmp_opr o2 s
  | OLe o1 o2 -> eval_cmp_opr o1 s <= eval_cmp_opr o2 s
  | OGe o1 o2 -> eval_cmp_opr o1 s >= eval_cmp_opr o2 s
  | OLt o1 o2 -> eval_cmp_opr o1 s < eval_cmp_opr o2 s
  | OGt o1 o2 -> eval_cmp_opr o1 s > eval_cmp_opr o2 s

let eval_cmp_cr0 (s:state) (c:ocmp) : cr0_t =
  match c with
  | OEq o1 o2 -> get_cr0 ((eval_cmp_opr o1 s - eval_cmp_opr o2 s) % pow2_64)
  | ONe o1 o2 -> get_cr0 ((eval_cmp_opr o1 s - eval_cmp_opr o2 s) % pow2_64)
  | OLe o1 o2 -> get_cr0 ((eval_cmp_opr o1 s - eval_cmp_opr o2 s) % pow2_64)
  | OGe o1 o2 -> get_cr0 ((eval_cmp_opr o1 s - eval_cmp_opr o2 s) % pow2_64)
  | OLt o1 o2 -> get_cr0 ((eval_cmp_opr o1 s - eval_cmp_opr o2 s) % pow2_64)
  | OGt o1 o2 -> get_cr0 ((eval_cmp_opr o1 s - eval_cmp_opr o2 s) % pow2_64)

let update_reg' (r:reg) (v:nat64) (s:state) : state =
  { s with regs = regs_make (fun (r':reg) -> if r' = r then v else s.regs r') }

let update_vec' (vr:vec) (v:quad32) (s:state) : state =
  { s with vecs = vecs_make (fun (vr':vec) -> if vr' = vr then v else s.vecs vr') }

let update_mem64' (ptr:int) (v:nat64) (s:state) : state =
  { s with mem = store_mem64 ptr v s.mem }

let valid_maddr64 (m:maddr) (s:state) : bool =
  valid_maddr_offset64 m.offset && valid_mem64 (eval_maddr m s) s.mem

let valid_ocmp (c:ocmp) (s:state) : bool =
  match c with
  | OEq o1 _ -> valid_first_cmp_opr o1
  | ONe o1 _ -> valid_first_cmp_opr o1
  | OLe o1 _ -> valid_first_cmp_opr o1
  | OGe o1 _ -> valid_first_cmp_opr o1
  | OLt o1 _ -> valid_first_cmp_opr o1
  | OGt o1 _ -> valid_first_cmp_opr o1

let xer_ov (xer:xer_t) : bool =
  xer.ov

let xer_ca (xer:xer_t) : bool =
  xer.ca

let update_xer_ov (xer:xer_t) (new_xer_ov:bool) : (new_xer:xer_t{xer_ov new_xer == new_xer_ov}) =
  { xer with ov = new_xer_ov }

let update_xer_ca (xer:xer_t) (new_xer_ca:bool) : (new_xer:xer_t{xer_ca new_xer == new_xer_ca}) =
  { xer with ca = new_xer_ca }

// Define a stateful monad to simplify defining the instruction semantics
let st (a:Type) = state -> a & state

unfold
let return (#a:Type) (x:a) :st a =
  fun s -> x, s

unfold
let bind (#a:Type) (#b:Type) (m:st a) (f:a -> st b) :st b =
fun s0 ->
  let x, s1 = m s0 in
  let y, s2 = f x s1 in
  y, {s2 with ok=s0.ok && s1.ok && s2.ok}

unfold
let get :st state =
  fun s -> s, s

unfold
let set (s:state) :st unit =
  fun _ -> (), s

unfold
let fail :st unit =
  fun s -> (), {s with ok=false}

unfold
let check (valid: state -> bool) : st unit =
  s <-- get;
  if valid s then
    return ()
  else
    fail

unfold
let run (f:st unit) (s:state) : state = snd (f s)

let update_reg (r:reg) (v:nat64) :st unit =
  s <-- get;
  set (update_reg' r v s)

let update_vec (vr:vec) (v:quad32) :st unit =
  s <-- get;
  set (update_vec' vr v s)

let update_mem64 (ptr:int) (v:nat64) :st unit =
  s <-- get;
  set (update_mem64' ptr v s)

let update_xer (new_xer:xer_t) :st unit =
  s <-- get;
  set ( { s with xer = new_xer } )

let update_cr0 (new_cr0:cr0_t) :st unit =
  s <-- get;
  set ( { s with cr0 = new_cr0 } )

// Core definition of instruction semantics
let eval_ins (ins:ins) : st unit =
  s <-- get;
  match ins with
  | Move dst src ->
    update_reg dst (eval_reg src s)

  | Load64 dst src ->
    check (valid_maddr64 src);;
    update_reg dst (eval_mem64 (eval_maddr src s) s)

  | Store64 src dst ->
    check (valid_maddr64 dst);;
    update_mem64 (eval_maddr dst s) (eval_reg src s)

  | LoadImm64 dst src ->
    update_reg dst (int_to_nat64 src)

  | AddLa dst src1 src2 ->
    update_reg dst ((eval_reg src1 s + src2) % pow2_64)

  | Add dst src1 src2 ->
    update_reg dst ((eval_reg src1 s + eval_reg src2 s) % pow2_64)

  | AddImm dst src1 src2 ->
    update_reg dst ((eval_reg src1 s + int_to_nat64 src2) % pow2_64)

  | AddExtended dst src1 src2 ->
    let old_carry = if xer_ca(s.xer) then 1 else 0 in
    let sum = (eval_reg src1 s) + (eval_reg src2 s) + old_carry in
    let new_carry = sum >= pow2_64 in
    update_reg dst (sum % pow2_64);;
    update_xer (update_xer_ca s.xer new_carry)

  | AddExtendedOV dst src1 src2 ->
    let old_carry = if xer_ov(s.xer) then 1 else 0 in
    let sum = (eval_reg src1 s) + (eval_reg src2 s) + old_carry in
    let new_carry = sum >= pow2_64 in
    update_reg dst (sum % pow2_64);;
    update_xer (update_xer_ov s.xer new_carry)

  | Sub dst src1 src2 ->
    update_reg dst ((eval_reg src1 s - eval_reg src2 s) % pow2_64)

  | SubImm dst src1 src2 ->
    update_reg dst ((eval_reg src1 s - int_to_nat64 src2) % pow2_64)
  
  | MulLow64 dst src1 src2 ->
    update_reg dst ((eval_reg src1 s * eval_reg src2 s) % pow2_64)

  | MulHigh64U dst src1 src2 ->
    update_reg dst (FStar.UInt.mul_div #64 (eval_reg src1 s) (eval_reg src2 s))
  
  | Xor dst src1 src2 ->
    update_reg dst (Types_s.ixor (eval_reg src1 s) (eval_reg src2 s))
  
  | And dst src1 src2 ->
    update_reg dst (Types_s.iand (eval_reg src1 s) (eval_reg src2 s))
  
  | Sr64Imm dst src1 src2 ->
    update_reg dst (Types_s.ishr (eval_reg src1 s) src2)
  
  | Sl64Imm dst src1 src2 ->
    update_reg dst (Types_s.ishl (eval_reg src1 s) src2)
  
  | Mfvsrd dst src ->
    let src_q = eval_vec src s in
    let src_two = four_to_two_two src_q in
    let extracted_nat64 = two_to_nat 32 (two_select src_two 1) in
    update_reg dst extracted_nat64
  
  | Mfvsrld dst src ->
    let src_q = eval_vec src s in
    let src_two = four_to_two_two src_q in
    let extracted_nat64 = two_to_nat 32 (two_select src_two 0) in
    update_reg dst extracted_nat64

  | Mtvsrdd dst src1 src2 ->
    let val_src1 = eval_reg src1 s in
    let val_src2 = eval_reg src2 s in
    update_vec dst (Mkfour
      (val_src2 % pow2_32)
      (val_src2 / pow2_32)
      (val_src1 % pow2_32)
      (val_src1 / pow2_32))
  
  | Vxor dst src1 src2 ->
    update_vec dst (quad32_xor (eval_vec src1 s) (eval_vec src2 s))
  
  | Vslw dst src1 src2 ->
    let src1_q = eval_vec src1 s in
    let src2_q = eval_vec src2 s in
    update_vec dst (Mkfour
      (Types_s.ishl src1_q.lo0 (src2_q.lo0 % 32))
      (Types_s.ishl src1_q.lo1 (src2_q.lo1 % 32))
      (Types_s.ishl src1_q.hi2 (src2_q.hi2 % 32))
      (Types_s.ishl src1_q.hi3 (src2_q.hi3 % 32)))

  | Vsrw dst src1 src2 ->
    let src1_q = eval_vec src1 s in
    let src2_q = eval_vec src2 s in
    update_vec dst (Mkfour
      (Types_s.ishr src1_q.lo0 (src2_q.lo0 % 32))
      (Types_s.ishr src1_q.lo1 (src2_q.lo1 % 32))
      (Types_s.ishr src1_q.hi2 (src2_q.hi2 % 32))
      (Types_s.ishr src1_q.hi3 (src2_q.hi3 % 32)))

  | Vcmpequw dst src1 src2 ->
    let src1_q = eval_vec src1 s in
    let src2_q = eval_vec src2 s in
    let eq_result (b:bool):nat32 = if b then 0xFFFFFFFF else 0 in
    let eq_val = Mkfour
      (eq_result (src1_q.lo0 = src2_q.lo0))
      (eq_result (src1_q.lo1 = src2_q.lo1))
      (eq_result (src1_q.hi2 = src2_q.hi2))
      (eq_result (src1_q.hi3 = src2_q.hi3))
    in
    update_vec dst eq_val
  
  | Vsldoi dst src1 src2 count ->
    check (fun s -> count = 4);;  // We only spec the one very special case we need
    let src1_q = eval_vec src1 s in
    let src2_q = eval_vec src2 s in
    let shifted_vec = Mkfour src2_q.hi3 src1_q.lo0 src1_q.lo1 src1_q.hi2 in
    update_vec dst shifted_vec

let run_ocmp (s:state) (c:ocmp) : state & bool =
  let s = run (check (valid_ocmp c)) s in
  ({s with cr0 = eval_cmp_cr0 s c}, eval_ocmp s c)

(*
 * These functions return an option state
 * None case arises when the while loop runs out of fuel
 *)
let rec eval_code (c:code) (fuel:nat) (s:state) : Tot (option state) (decreases %[fuel; c]) =
  match c with
  | Ins ins ->
    Some (run (eval_ins ins) s)
  | Block l ->
    eval_codes l fuel s
  | IfElse cond ifTrue ifFalse  ->
    let (s, b) = run_ocmp s cond in
    if b then eval_code ifTrue fuel s else eval_code ifFalse fuel s
  | While b c ->
    eval_while b c fuel s
and eval_codes (l:codes) (fuel:nat) (s:state) : Tot (option state) (decreases %[fuel; l]) =
  match l with
  | []   -> Some s
  | c::tl ->
    let s_opt = eval_code c fuel s in
    if None? s_opt then None else eval_codes tl fuel (Some?.v s_opt)
and eval_while (cond:ocmp) (c:code) (fuel:nat) (s0:state) : Tot (option state) (decreases %[fuel; c]) =
  if fuel = 0 then None else
  let (s0, b) = run_ocmp s0 cond in
  if not b then Some s0
  else
    match eval_code c (fuel - 1) s0 with
    | None -> None
    | Some s1 ->
      if s1.ok then eval_while cond c (fuel - 1) s1  // success: continue to next iteration
      else Some s1  // failure: propagate failure immediately
