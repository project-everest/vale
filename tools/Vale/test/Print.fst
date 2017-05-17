module Print

// Trusted code for producing assembly code

open Semantics
open FStar.IO

noeq type printer = {
  reg_prefix : unit -> string;
  maddr      : maddr -> string -> string;
  const      : int -> string;
  ins_name   : string -> list operand -> string;
  op_order   : #a:Type -> a -> a -> a*a;
}

let print_reg (r:reg) (p:printer) =
  p.reg_prefix() ^
  (match r with
  | Rax -> "rax"
  | Rbx -> "rbx"
  | Rcx -> "rcx"
  | Rdx -> "rdx"
  | Rsi -> "rsi"
  | Rdi -> "rdi"
  | Rbp -> "rbp"
  | Rsp -> "rsp"
  | R8  -> "r8"
  | R9  -> "r9"
  | R10 -> "r10"
  | R11 -> "r11"
  | R12 -> "r12"
  | R13 -> "r13"
  | R14 -> "r14"
  | R15 -> "r15"
  )
  
let print_small_reg (r:reg) (p:printer) =
  p.reg_prefix() ^
  (match r with
  | Rax -> "al"
  | Rbx -> "bl"
  | Rcx -> "cl"
  | Rdx -> "dl"
  | _ -> " !!! INVALID small operand !!!  Expected al, bl, cl, or dl."
  )

let print_operand (o:operand) (p:printer) =
  match o with
  | OConst n -> if 0 <= n && n < nat64_max then
		  p.const n
	       else
		 "!!! INVALID constant: " ^ string_of_int n ^ " !!!"
  | OReg r -> print_reg r p
  | OMem m -> p.maddr m "qword"

let print_small_operand (o:operand) (p:printer) =
  match o with
  | OConst n -> if 0 <= n && n < 64 then
		  p.const n
	       else
		 "!!! INVALID constant: " ^ string_of_int n ^ " !!!!"
  | OReg r -> print_small_reg r p
  | _ -> "!!! INVALID small operand !!! Expected al, bl, cl, or dl."

assume val print_any: 'a -> string

let print_shift_operand (o:operand) (p:printer) =
  match o with
  | OConst n -> if 0 <= n && n < 64 then
		  p.const n
	       else
		 "!!! INVALID shift operand: " ^ print_any n ^ " is too large !!!"
  | OReg Rcx -> print_small_reg (OReg?.r o) p
  | _ -> "!!! INVALID shift operand !!! Expected constant or cl."

let cmp_not(o:ocmp) : ocmp =
  match o with
  | OEq o1 o2 -> ONe o1 o2
  | ONe o1 o2 -> OEq o1 o2
  | OLe o1 o2 -> OGt o1 o2
  | OGe o1 o2 -> OLt o1 o2
  | OLt o1 o2 -> OGe o1 o2
  | OGt o1 o2 -> OLe o1 o2

// Sanity check
let _ = assert (forall o . o == cmp_not (cmp_not o))

let print_ins (ins:ins) (p:printer) =
  let print_pair (dst:operand) (src:operand) (print_dst:operand->printer->string) (print_src:operand->printer-> string) =
    let first, second = p.op_order (print_dst dst p) (print_src src p) in
      first ^ ", " ^ second ^ "\n"
  in
  let print_ops (dst:operand) (src:operand) =
    print_pair dst src print_operand print_operand
  in
  let print_shift (dst:operand) (amount:operand) =
    print_pair dst amount print_operand print_shift_operand
  in
  match ins with 
  | Mov64 dst src -> p.ins_name "  mov" [dst; src] ^ print_ops dst src
  | Add64 dst src -> p.ins_name "  add" [dst; src] ^ print_ops dst src
  | AddLea64 dst src1 src2 -> let name = p.ins_name "  lea" [dst; src1; src2] in
			     if OReg? src1 && OConst? src2 then
			       name ^ p.maddr (MReg (OReg?.r src1) (OConst?.n src2)) "qword"
			     else if OReg? src1 && OReg? src2 then
			       name ^ p.maddr (MIndex (OReg?.r src1) 1 (OReg?.r src2) 0) "qword"
			     else
			       "!!! INVALID AddLea64 operands: " ^ print_any src1 ^ ", " ^ print_any src2 ^ "!!!"			      
  | AddCarry64 dst src -> p.ins_name "  adc" [dst; src] ^ print_ops dst src
  | Sub64 dst src -> p.ins_name "  sub" [dst; src] ^ print_ops dst src
  | Mul64 src -> p.ins_name "  mul" [src] ^ (print_operand src p)
  | IMul64 dst src -> p.ins_name "  imul" [dst; src] ^ print_ops dst src
  | Xor64 dst src -> p.ins_name "  xor" [dst; src] ^ print_ops dst src	 
  | And64 dst src -> p.ins_name "  and" [dst; src] ^ print_ops dst src	 
  | Shr64 dst amt -> p.ins_name "  shr" [dst; amt] ^ print_shift dst amt
  | Shl64 dst amt -> p.ins_name "  shl" [dst; amt] ^ print_shift dst amt
