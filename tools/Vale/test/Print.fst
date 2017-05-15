module Print

// Trusted code for producing assembly code

open Semantics
open FStar.IO

noeq type printer = {
  reg_prefix : unit -> string;
  maddr      : maddr -> string -> string;
  const      : int -> string;
  ins_name   : string -> list operand -> string;
  op_order   : (#a:Type) -> a -> a -> a*a;
}

let print_reg (r:reg) (p:printer) =
  print_string (p.reg_prefix());
  match r with
  | Rax -> print_string "rax"
  | Rbx -> print_string "rbx"
  | Rcx -> print_string "rcx"
  | Rdx -> print_string "rdx"
  | Rsi -> print_string "rsi"
  | Rdi -> print_string "rdi"
  | Rbp -> print_string "rbp"
  | Rsp -> print_string "rsp"
  | R8  -> print_string "r8"
  | R9  -> print_string "r9"
  | R10 -> print_string "r10"
  | R11 -> print_string "r11"
  | R12 -> print_string "r12"
  | R13 -> print_string "r13"
  | R14 -> print_string "r14"
  | R15 -> print_string "r15"

let print_small_reg (r:reg) (p:printer) =
  print_string (p.reg_prefix());
  match r with
  | Rax -> print_string "al"
  | Rbx -> print_string "bl"
  | Rcx -> print_string "cl"
  | Rdx -> print_string "dl"
  | _ -> print_string(" !!! INVALID small operand !!!  Expected al, bl, cl, or dl.")

let print_operand (o:operand) (p:printer) =
  match o with
  | OConst n -> if 0 <= n && n < nat64_max then
		  print_string (p.const n)
	       else
		 print_string "!!! INVALID constant: ";
		 print_any n;
		 print_string " !!!"
  | OReg r -> print_reg r p
  | OMem m -> print_string (p.maddr m "qword")

let print_small_operand (o:operand) (p:printer) =
  match o with
  | OConst n -> if 0 <= n && n < 64 then
		  print_string (p.const n)
	       else
		 print_string "!!! INVALID constant: ";
		 print_any n;
		 print_string " !!!"
  | OReg r -> print_small_reg r p
  | _ -> print_string "!!! INVALID small operand !!! Expected al, bl, cl, or dl."

let print_shift_operand (o:operand) (p:printer) =
  match o with
  | OConst n -> if 0 <= n && n < 64 then
		  print_string (p.const n)
	       else
		 print_string "!!! INVALID shift operand: ";
		 print_any n;
		 print_string " is too large !!!"
  | OReg Rcx -> print_small_reg (OReg?.r o) p
  | _ -> print_string "!!! INVALID shift operand !!! Expected constant or cl."

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
  let print_pair (dst:operand) (src:operand) (print_dst:operand->printer->ML unit) (print_src:operand->printer-> ML unit) =
    let o1,o2 = p.op_order dst src in
    let p1,p2 = p.op_order print_dst print_src in
      p1 o1 p;
      print_string ", ";
      p2 o2 p;
      print_newline
  in
  let print_ops (dst:operand) (src:operand) =
    print_pair dst src print_operand print_operand
  in
  let print_shift (dst:operand) (amount:operand) =
    print_pair dst amount print_operand print_shift_operand
  in
  match ins with 
  | Mov64 dst src -> print_string (p.ins_name "  mov" [dst, src]); print_ops dst src
  | Add64 dst src -> print_string (p.ins_name "  add" [dst, src]); print_ops dst src
  | AddLea64 dst src1 src2 -> print_string ("TODO") 
  | AddCarry64 dst src -> print_string (p.ins_name "  adc" [dst, src]); print_ops dst src
  | Sub64 dst src -> print_string (p.ins_name "  sub" [dst, src]); print_ops dst src
  | Mul64 src -> print_string (p.ins_name "  mul", [src]); print_operand src
  | IMul64 dst src -> print_string (p.ins_name "  imul" [dst, src]); print_ops dst src
  | Xor64 dst src -> print_string (p.ins_name "  xor", [dst, src]); print_ops dst src	 
  | And64 dst src -> print_string (p.ins_name "  and", [dst, src]); print_ops dst src	 
  | Shr64 dst amt -> print_string (p.ins_name "  shr", [dst, amt]); print_shift dst amt
  | Shl64 dst amt -> print_string (p.ins_name "  shl", [dst, amt]); print_shift dst amt

