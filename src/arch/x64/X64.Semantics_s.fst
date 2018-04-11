module X64.Semantics_s

open FStar.BaseTypes
open X64.Machine_s
open Words_s
open Words.Four_s
open Types_s
module M = Memory_i_s

type uint64 = UInt64.t

type ins =
  | Mov64      : dst:operand -> src:operand -> ins
  | Add64      : dst:operand -> src:operand -> ins
  | AddLea64   : dst:operand -> src1:operand -> src2:operand -> ins
  | AddCarry64 : dst:operand -> src:operand -> ins
  | Adcx64     : dst:operand -> src:operand -> ins
  | Adox64     : dst:operand -> src:operand -> ins
  | Sub64      : dst:operand -> src:operand -> ins
  | Mul64      : src:operand -> ins
  | Mulx64     : dst_hi:operand -> dst_lo:operand -> src:operand -> ins
  | IMul64     : dst:operand -> src:operand -> ins
  | Xor64      : dst:operand -> src:operand -> ins
  | And64      : dst:operand -> src:operand -> ins
  | Shr64      : dst:operand -> amt:operand -> ins
  | Shl64      : dst:operand -> amt:operand -> ins
  | Push       : src:operand -> ins
  | Pop        : dst:operand -> ins
  | Paddd      : dst:xmm -> src:xmm -> ins
  | Pxor       : dst:xmm -> src:xmm -> ins
  | Pslld      : dst:xmm -> amt:int -> ins
  | Psrld      : dst:xmm -> amt:int -> ins
  | Pshufb     : dst:xmm -> src:xmm -> ins  
  | Pshufd     : dst:xmm -> src:xmm -> permutation:imm8 -> ins  
  | Pinsrd     : dst:xmm -> src:operand -> index:imm8 -> ins
  | VPSLLDQ    : dst:xmm -> src:xmm -> count:imm8 -> ins
  | MOVDQU     : dst:mov128_op -> src:mov128_op -> ins  // We let the assembler complain about attempts to use two memory ops
  | Pclmulqdq  : dst:xmm -> src:xmm -> imm:int -> ins
  | AESNI_enc           : dst:xmm -> src:xmm -> ins
  | AESNI_enc_last      : dst:xmm -> src:xmm -> ins
  | AESNI_dec           : dst:xmm -> src:xmm -> ins
  | AESNI_dec_last      : dst:xmm -> src:xmm -> ins
  | AESNI_imc           : dst:xmm -> src:xmm -> ins
  | AESNI_keygen_assist : dst:xmm -> src:xmm -> imm8 -> ins

type ocmp =
  | OEq: o1:operand -> o2:operand -> ocmp
  | ONe: o1:operand -> o2:operand -> ocmp
  | OLe: o1:operand -> o2:operand -> ocmp
  | OGe: o1:operand -> o2:operand -> ocmp
  | OLt: o1:operand -> o2:operand -> ocmp
  | OGt: o1:operand -> o2:operand -> ocmp

type code = precode ins ocmp
type codes = list code

noeq type state = {
  ok: bool;
  regs: reg -> nat64;
  xmms: xmm -> quad32;
  flags: nat64;
  mem: mem;
}

//let u (i:int{FStar.UInt.fits i 64}) : uint64 = FStar.UInt64.uint_to_t i
//let v (u:uint64) : nat64 = FStar.UInt64.v u

assume val havoc : state -> ins -> nat64

// TODO: Need to be sure that load/store_mem does an appropriate little-endian load

unfold let eval_reg (r:reg) (s:state) : nat64 = s.regs r
unfold let eval_xmm (i:xmm) (s:state) : quad32 = s.xmms i
unfold let eval_mem (ptr:int) (s:state) : nat64 = load_mem64 ptr s.mem
unfold let eval_mem128 (ptr:int) (s:state) : quad32 = load_mem128 ptr s.mem

[@va_qattr]
let eval_maddr (m:maddr) (s:state) : int =
  let open FStar.Mul in
    match m with
    | MConst n -> n
    | MReg reg offset -> (eval_reg reg s) + offset
    | MIndex base scale index offset -> (eval_reg base s) + scale * (eval_reg index s) + offset

let eval_operand (o:operand) (s:state) : nat64 =
  match o with
  | OConst n -> int_to_nat64 n
  | OReg r -> eval_reg r s
  | OMem m -> eval_mem (eval_maddr m s) s

let eval_mov128_op (o:mov128_op) (s:state) : quad32 =
  match o with 
  | Mov128Xmm i -> eval_xmm i s
  | Mov128Mem m -> eval_mem128 (eval_maddr m s) s

let eval_ocmp (s:state) (c:ocmp) :bool =
  match c with
  | OEq o1 o2 -> eval_operand o1 s = eval_operand o2 s
  | ONe o1 o2 -> eval_operand o1 s <> eval_operand o2 s
  | OLe o1 o2 -> eval_operand o1 s <= eval_operand o2 s
  | OGe o1 o2 -> eval_operand o1 s >= eval_operand o2 s
  | OLt o1 o2 -> eval_operand o1 s < eval_operand o2 s
  | OGt o1 o2 -> eval_operand o1 s > eval_operand o2 s

let update_reg' (r:reg) (v:nat64) (s:state) : state =
  { s with regs = fun r' -> if r' = r then v else s.regs r' }

let update_xmm' (x:xmm) (v:quad32) (s:state) : state =
  { s with xmms = fun x' -> if x' = x then v else s.xmms x' }

let update_mem (ptr:int) (v:nat64) (s:state) : state =
  { s with mem = store_mem64 ptr v s.mem }

let update_mem128 (ptr:int) (v:quad32) (s:state) : state =
  { s with mem = store_mem128 ptr v s.mem }

let valid_maddr (m:maddr) (s:state) : bool =
  valid_mem64 (eval_maddr m s) s.mem

let valid_maddr128 (m:maddr) (s:state) : bool =
  valid_mem128 (eval_maddr m s) s.mem

let valid_operand (o:operand) (s:state) : bool =
  match o with
  | OConst n -> true
  | OReg r -> true
  | OMem m -> valid_maddr m s

let valid_mov128_op (o:mov128_op) (s:state) : bool =
  match o with
  | Mov128Xmm i -> true (* We leave it to the printer/assembler to object to invalid XMM indices *)
  | Mov128Mem m -> valid_maddr128 m s

let valid_shift_operand (o:operand) (s:state) : bool =
  valid_operand o s && (eval_operand o s) < 64
  
let valid_ocmp (c:ocmp) (s:state) :bool =
  match c with
  | OEq o1 o2 -> valid_operand o1 s && valid_operand o2 s
  | ONe o1 o2 -> valid_operand o1 s && valid_operand o2 s
  | OLe o1 o2 -> valid_operand o1 s && valid_operand o2 s
  | OGe o1 o2 -> valid_operand o1 s && valid_operand o2 s
  | OLt o1 o2 -> valid_operand o1 s && valid_operand o2 s
  | OGt o1 o2 -> valid_operand o1 s && valid_operand o2 s

let valid_dst_operand (o:operand) (s:state) : bool =
  valid_operand o s && valid_dst o

let update_operand_preserve_flags' (o:operand) (v:nat64) (s:state) : state =
  match o with
  | OConst _ -> {s with ok = false}
  | OReg r -> update_reg' r v s
  | OMem m -> update_mem (eval_maddr m s) v s // see valid_maddr for how eval_maddr connects to b and i

let update_mov128_op_preserve_flags' (o:mov128_op) (v:quad32) (s:state) : state =
  match o with
  | Mov128Xmm i -> update_xmm' i v s
  | Mov128Mem m -> update_mem128 (eval_maddr m s) v s

// Default version havocs flags 
let update_operand' (o:operand) (ins:ins) (v:nat64) (s:state) : state =
  { (update_operand_preserve_flags' o v s) with flags = havoc s ins }

(* REVIEW: Will we regret exposing a mod here?  Should flags be something with more structure? *)
let cf (flags:nat64) : bool =
  flags % 2 = 1

//unfold let bit11 = normalize_term (pow2 11)
let _ = assert (2048 == normalize_term (pow2 11))

let overflow(flags:nat64) : bool =
  (flags / 2048) % 2 = 1  // OF is the 12th bit, so dividing by 2^11 shifts right 11 bits

let update_cf (flags:nat64) (new_cf:bool) : (new_flags:nat64{cf new_flags == new_cf}) =
  if new_cf then
    if not (cf flags) then
      flags + 1
    else
      flags
  else
    if (cf flags) then
      flags - 1
    else
      flags

let update_of (flags:nat64) (new_of:bool) : (new_flags:nat64{overflow new_flags == new_of}) =
  if new_of then
    if not (overflow flags) then
      flags + 2048
    else
      flags
  else
    if (overflow flags) then
      flags - 2048
    else
      flags

(* Define a stateful monad to simplify defining the instruction semantics *)
let st (a:Type) = state -> a * state

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
let check_imm (valid:bool) : st unit =
  if valid then
    return ()
  else
    fail

unfold
let check (valid: state -> bool) : st unit =
  s <-- get;
  if valid s then
    return ()
  else
    fail

unfold
let run (f:st unit) (s:state) : state = snd (f s)

(* Monadic update operations *)
unfold
let update_operand_preserve_flags (dst:operand) (v:nat64) :st unit =
  check (valid_dst_operand dst);;
  s <-- get;
  set (update_operand_preserve_flags' dst v s)

unfold
let update_mov128_op_preserve_flags (dst:mov128_op) (v:quad32) :st unit =
  check (valid_mov128_op dst);;
  s <-- get;
  set (update_mov128_op_preserve_flags' dst v s)

// Default version havocs flags
unfold
let update_operand (dst:operand) (ins:ins) (v:nat64) :st unit =
  check (valid_dst_operand dst);;
  s <-- get;
  set (update_operand' dst ins v s)

let update_reg (r:reg) (v:nat64) :st unit =
  s <-- get;
  set (update_reg' r v s)

let update_xmm (x:xmm)  (ins:ins) (v:quad32) :st unit =
  s <-- get;
  set (  { (update_xmm' x v s) with flags = havoc s ins } )

let update_flags (new_flags:nat64) :st unit =
  s <-- get;
  set ( { s with flags = new_flags } )

let update_cf_of (new_cf new_of:bool) :st unit =
  s <-- get;
  set ( { s with flags = update_cf (update_of s.flags new_of) new_cf } )

(* Core definition of instruction semantics *)
let eval_ins (ins:ins) : st unit =
  s <-- get;
  match ins with
  | Mov64 dst src ->
    check (valid_operand src);;
    update_operand_preserve_flags dst (eval_operand src s)

  | Add64 dst src ->
    check (valid_operand src);;
    let sum = (eval_operand dst s) + (eval_operand src s) in
    let new_carry = sum >= pow2_64 in    
    update_operand dst ins ((eval_operand dst s + eval_operand src s) % pow2_64);;
    update_flags (update_cf s.flags new_carry)

  | AddLea64 dst src1 src2 ->
    check (valid_operand src1);;
    check (valid_operand src2);;
    update_operand_preserve_flags dst ((eval_operand src1 s + eval_operand src2 s) % pow2_64)

  | AddCarry64 dst src ->
    check (valid_operand src);;
    let old_carry = if cf(s.flags) then 1 else 0 in
    let sum = (eval_operand dst s) + (eval_operand src s) + old_carry in
    let new_carry = sum >= pow2_64 in
    update_operand dst ins (sum % pow2_64);;
    update_flags (havoc s ins);;
    update_flags (update_cf s.flags new_carry)  // We specify cf, but underspecify everything else

  | Adcx64 dst src ->
    check (valid_operand src);;
    let old_carry = if cf(s.flags) then 1 else 0 in
    let sum = (eval_operand dst s) + (eval_operand src s) + old_carry in
    let new_carry = sum >= pow2_64 in
    update_operand dst ins (sum % pow2_64);;
    update_flags (update_cf s.flags new_carry)  // Explicitly touches only CF

  | Adox64 dst src ->
    check (valid_operand src);;
    let old_carry = if overflow(s.flags) then 1 else 0 in
    let sum = (eval_operand dst s) + (eval_operand src s) + old_carry in
    let new_carry = sum >= pow2_64 in
    update_operand dst ins (sum % pow2_64);;
    update_flags (update_of s.flags new_carry)  // Explicitly touches only OF

  | Sub64 dst src ->
    check (valid_operand src);;
    update_operand dst ins ((eval_operand dst s - eval_operand src s) % pow2_64)

  | Mul64 src ->
    check (valid_operand src);;
    let hi = FStar.UInt.mul_div #64 (eval_reg Rax s) (eval_operand src s) in
    let lo = FStar.UInt.mul_mod #64 (eval_reg Rax s) (eval_operand src s) in
    update_reg Rax lo;;
    update_reg Rdx hi;;
    update_flags (havoc s ins)

  | Mulx64 dst_hi dst_lo src ->
    check (valid_operand src);;
    let hi = FStar.UInt.mul_div #64 (eval_reg Rdx s) (eval_operand src s) in
    let lo = FStar.UInt.mul_mod #64 (eval_reg Rdx s) (eval_operand src s) in
    update_operand_preserve_flags dst_lo lo;;
    update_operand_preserve_flags dst_hi hi

  | IMul64 dst src ->
    check (valid_operand src);;
    update_operand dst ins (FStar.UInt.mul_mod #64 (eval_operand dst s) (eval_operand src s))

  | Xor64 dst src ->
    check (valid_operand src);;
    update_operand dst ins (Types_s.ixor (eval_operand dst s) (eval_operand src s));;
    update_cf_of false false
    
  | And64 dst src ->
    check (valid_operand src);;
    update_operand dst ins (Types_s.iand (eval_operand dst s) (eval_operand src s))

  | Shr64 dst amt ->
    check (valid_shift_operand amt);;
    update_operand dst ins (Types_s.ishr (eval_operand dst s) (eval_operand amt s))

  | Shl64 dst amt ->
    check (valid_shift_operand amt);;
    update_operand dst ins (Types_s.ishl (eval_operand dst s) (eval_operand amt s))

  | Push src ->
    check (valid_operand src);;
    let new_rsp = ((eval_reg Rsp s) - 8) % pow2_64 in
    update_operand_preserve_flags (OMem (MConst new_rsp)) (eval_operand src s);;
    update_reg Rsp new_rsp

  | Pop dst ->
    let stack_val = OMem (MReg Rsp 0) in
    check (valid_operand stack_val);;    
    let new_dst = eval_operand stack_val s in
    let new_rsp = ((eval_reg Rsp s) + 8) % pow2_64 in
    update_operand_preserve_flags dst new_dst;;
    update_reg Rsp new_rsp

// In the XMM-related instructions below, we generally don't need to check for validity of the operands,
// since all possibilities are valid, thanks to dependent types 

  | Paddd dst src ->
    let src_q = eval_xmm src s in
    let dst_q = eval_xmm dst s in
    update_xmm dst ins (Mkfour ((dst_q.lo0 + src_q.lo0) % pow2_32)
			       ((dst_q.lo1 + src_q.lo1) % pow2_32)
			       ((dst_q.hi2 + src_q.hi2) % pow2_32)
			       ((dst_q.hi3 + src_q.hi3) % pow2_32))

  | Pxor dst src ->
    update_xmm dst ins (quad32_xor (eval_xmm dst s) (eval_xmm src s))

  | Pslld dst amt ->
    check_imm (0 <= amt && amt < 32);;
    update_xmm dst ins (four_map (fun i -> ishl i amt) (eval_xmm dst s))

  | Psrld dst amt ->
    check_imm (0 <= amt && amt < 32);;
    update_xmm dst ins (four_map (fun i -> ishr i amt) (eval_xmm dst s))
 
  | Pshufb dst src ->
    let src_q = eval_xmm src s in
    let dst_q = eval_xmm dst s in
    // We only spec a restricted version sufficient for doing a byte reversal
    check_imm (src_q.lo0     = 0x0C0D0E0F &&
	       src_q.lo1 = 0x08090A0B &&
	       src_q.hi2 = 0x04050607 &&
	       src_q.hi3     = 0x00010203);;
    update_xmm dst ins (reverse_bytes_quad32 dst_q)
    
  | Pshufd dst src permutation ->  
    let bits:bits_of_byte = byte_to_twobits permutation in
    let src_val = eval_xmm src s in
    let permuted_xmm = Mkfour
         (select_word src_val bits.lo0)
         (select_word src_val bits.lo1)
         (select_word src_val bits.hi2)
         (select_word src_val bits.hi3)
    in
    update_xmm dst ins permuted_xmm

  | Pinsrd dst src index ->
    check (valid_operand src);;
    let dst_q = eval_xmm dst s in
    update_xmm dst ins (insert_nat32 dst_q ((eval_operand src s) % pow2_32) (index % 4))

  | VPSLLDQ dst src count ->
    check (fun s -> count = 4);;  // We only spec the one very special case we need
    let src_q = eval_xmm src s in
    let shifted_xmm = Mkfour 0 src_q.lo0 src_q.lo1 src_q.hi2 in
    update_xmm dst ins shifted_xmm

  | MOVDQU dst src ->
    check (valid_mov128_op src);; 
    update_mov128_op_preserve_flags dst (eval_mov128_op src s)

  | Pclmulqdq dst src imm ->
    (
      let Mkfour a0 a1 a2 a3 = eval_xmm dst s in
      let Mkfour b0 b1 b2 b3 = eval_xmm src s in
      let f x0 x1 y0 y1 =
        let x = Math.Poly2.Bits_s.of_double32 (Mktwo x0 x1) in
        let y = Math.Poly2.Bits_s.of_double32 (Mktwo y0 y1) in
        update_xmm dst ins (Math.Poly2.Bits_s.to_quad32 (Math.Poly2_s.mul x y))
        in
      match imm with
      | 0 -> f a0 a1 b0 b1
      | 1 -> f a2 a3 b0 b1
      | 16 -> f a0 a1 b2 b3
      | 17 -> f a2 a3 b2 b3
      | _ -> fail
    )

  | AESNI_enc dst src ->
    let dst_q = eval_xmm dst s in
    let src_q = eval_xmm src s in
    update_xmm dst ins (quad32_xor (AES_s.mix_columns (AES_s.sub_bytes (AES_s.shift_rows dst_q))) src_q)

  | AESNI_enc_last dst src ->
    let dst_q = eval_xmm dst s in
    let src_q = eval_xmm src s in
    update_xmm dst ins (quad32_xor (AES_s.sub_bytes (AES_s.shift_rows dst_q)) src_q)

  | AESNI_dec dst src ->
    let dst_q = eval_xmm dst s in
    let src_q = eval_xmm src s in
    update_xmm dst ins (quad32_xor (AES_s.inv_mix_columns (AES_s.inv_sub_bytes (AES_s.inv_shift_rows dst_q))) src_q)

  | AESNI_dec_last dst src ->
    let dst_q = eval_xmm dst s in
    let src_q = eval_xmm src s in
    update_xmm dst ins (quad32_xor (AES_s.inv_sub_bytes (AES_s.inv_shift_rows dst_q)) src_q)

  | AESNI_imc dst src ->
    let src_q = eval_xmm src s in
    update_xmm dst ins (AES_s.inv_mix_columns src_q)

  | AESNI_keygen_assist dst src imm ->
    let src_q = eval_xmm src s in
    update_xmm dst ins (Mkfour (AES_s.sub_word src_q.lo1) 
			       (ixor (AES_s.rot_word (AES_s.sub_word src_q.lo1)) imm)
			       (AES_s.sub_word src_q.hi3)
			       (ixor (AES_s.rot_word (AES_s.sub_word src_q.hi3)) imm))
 
 
(*
 * These functions return an option state
 * None case arises when the while loop runs out of fuel
 *)
// TODO: IfElse and While should havoc the flags
val eval_code:  c:code           -> fuel:nat -> s:state -> Tot (option state) (decreases %[fuel; c])
val eval_codes: l:codes          -> fuel:nat -> s:state -> Tot (option state) (decreases %[fuel; l])
val eval_while: b:ocmp -> c:code -> fuel:nat -> s:state -> Tot (option state) (decreases %[fuel; c])

let rec eval_code c fuel s =
  match c with
  | Ins ins                       -> Some (run (eval_ins ins) s)
  | Block l                       -> eval_codes l fuel s
  | IfElse ifCond ifTrue ifFalse  -> let s = run (check (valid_ocmp ifCond)) s in
	   if eval_ocmp s ifCond then eval_code ifTrue fuel s else eval_code ifFalse fuel s
  | While b c                     -> eval_while b c fuel s

and eval_codes l fuel s =
  match l with
  | []   -> Some s
  | c::tl ->
    let s_opt = eval_code c fuel s in
    if None? s_opt then None else eval_codes tl fuel (Some?.v s_opt)

and eval_while b c fuel s0 =
  if fuel = 0 then None else
  let s0 = run (check (valid_ocmp b)) s0 in
  if not (eval_ocmp s0 b) then Some s0
  else
    match eval_code c (fuel - 1) s0 with
    | None -> None
    | Some s1 ->
      if s1.ok then eval_while b c (fuel - 1) s1  // success: continue to next iteration
      else Some s1  // failure: propagate failure immediately
