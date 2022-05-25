module PPC64LE.Print_s

// Trusted code for producing assembly code

open PPC64LE.Machine_s
open PPC64LE.Semantics_s
open FStar.IO

noeq type printer = {
  reg_prefix : unit -> string;
  vec_prefix : unit -> string;
  vsr_prefix : unit -> string;
  maddr      : string -> string -> string;
  const      : int -> string;
  align      : unit -> string;
  header     : unit -> string;
  footer     : unit -> string;
  proc_name  : string -> string;
  ret        : string -> string;
}

let print_reg_name (r:reg) =
  match r with
  | R0 -> "0"
  | R1 -> "1"
  | R2 -> "2"
  | R3 -> "3"
  | R4 -> "4"
  | R5 -> "5"
  | R6 -> "6"
  | R7 -> "7"
  | R8 -> "8"
  | R9 -> "9"
  | R10 -> "10"
  | R11 -> "11"
  | R12 -> "12"
  | R13 -> "13"
  | R14 -> "14"
  | R15 -> "15"
  | R16 -> "16"
  | R17 -> "17"
  | R18 -> "18"
  | R19 -> "19"
  | R20 -> "20"
  | R21 -> "21"
  | R22 -> "22"
  | R23 -> "23"
  | R24 -> "24"
  | R25 -> "25"
  | R26 -> "26"
  | R27 -> "27"
  | R28 -> "28"
  | R29 -> "29"
  | R30 -> "30"
  | R31 -> "31"

let print_vec_name (v:vec) =
  match v with
  | V0 -> "0"
  | V1 -> "1"
  | V2 -> "2"
  | V3 -> "3"
  | V4 -> "4"
  | V5 -> "5"
  | V6 -> "6"
  | V7 -> "7"
  | V8 -> "8"
  | V9 -> "9"
  | V10 -> "10"
  | V11 -> "11"
  | V12 -> "12"
  | V13 -> "13"
  | V14 -> "14"
  | V15 -> "15"
  | V16 -> "16"
  | V17 -> "17"
  | V18 -> "18"
  | V19 -> "19"
  | V20 -> "20"
  | V21 -> "21"
  | V22 -> "22"
  | V23 -> "23"
  | V24 -> "24"
  | V25 -> "25"
  | V26 -> "26"
  | V27 -> "27"
  | V28 -> "28"
  | V29 -> "29"
  | V30 -> "30"
  | V31 -> "31"

let print_reg (r:reg) (p:printer) =
  p.reg_prefix() ^ print_reg_name r

let print_vec (v:vec) (vsr:bool) (p:printer) =
  if vsr then p.vsr_prefix() ^ "32+" ^ print_vec_name v
  else p.vec_prefix() ^ print_vec_name v

let print_maddr (m:maddr) (p:printer) =
  p.maddr (string_of_int m.offset) (print_reg m.address p)

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

let print_first_cmp_opr (o:cmp_opr) (p:printer) =
  match o with
  | CReg r -> print_reg r p
  | _ -> "!!! INVALID first compare operand !!! Expected general purpose register."

let print_ins (ins:ins) (p:printer) =
  let print_pair (o1 o2:string) =
    o1 ^ ", " ^ o2
  in
  let print_triple (o1 o2 o3:string) =
    o1 ^ ", " ^ o2 ^ ", " ^ o3
  in
  let print_quadruple (o1 o2 o3 o4:string) =
    o1 ^ ", " ^ o2 ^ ", " ^ o3 ^ ", " ^ o4
  in
  let print_reg_pair (dst src:reg) =
    print_pair (print_reg dst p) (print_reg src p)
  in
  let print_reg_mem (o1:reg) (o2:maddr) =
    print_pair (print_reg o1 p) (print_maddr o2 p)
  in
  let print_reg_triple (dst src1 src2:reg) =
    print_triple (print_reg dst p) (print_reg src1 p) (print_reg src2 p)
  in
  let print_reg_imm (dst:reg) (src:int) =
    print_pair (print_reg dst p) (p.const src)
  in
  let print_reg_pair_imm (dst src1:reg) (src2:int) =
    print_triple (print_reg dst p) (print_reg src1 p) (p.const src2)
  in
  let print_reg_vec (dst:reg) (src:vec) (vsr:bool) =
    print_pair (print_reg dst p) (print_vec src vsr p)
  in
  let print_vec_reg_pair (dst:vec) (src1 src2:reg) (vsr:bool) =
    print_triple (print_vec dst vsr p) (print_reg src1 p) (print_reg src2 p)
  in
  let print_vec_triple (dst src1 src2:vec) (vsr:bool) =
    print_triple (print_vec dst vsr p) (print_vec src1 vsr p) (print_vec src2 vsr p)
  in
  let print_vec_triple_imm (dst src1 src2:vec) (count:int) (vsr:bool) =
    print_quadruple (print_vec dst vsr p) (print_vec src1 vsr p) (print_vec src2 vsr p) (p.const count)
  in
  match ins with
  | Move dst src -> "  mr " ^ print_reg_pair dst src
  | Load64 dst src -> "  ld " ^ print_reg_mem dst src
  | Store64 src dst -> "  std " ^ print_reg_mem src dst
  | LoadImm64 dst src -> "  li " ^ print_reg_imm dst src
  | AddLa dst src1 src2 -> "  la " ^ print_reg_mem dst ({ address = src1; offset = src2 })
  | Add dst src1 src2 -> "  add " ^ print_reg_triple dst src1 src2
  | AddImm dst src1 src2 -> "  addi " ^ print_reg_pair_imm dst src1 src2
  | AddExtended dst src1 src2 -> "  adde " ^ print_reg_triple dst src1 src2
  | AddExtendedOV dst src1 src2 -> "  addex " ^ print_reg_triple dst src1 src2
  | Sub dst src1 src2 -> "  sub " ^ print_reg_triple dst src1 src2
  | SubImm dst src1 src2 -> "  subi " ^ print_reg_pair_imm dst src1 src2
  | MulLow64 dst src1 src2 -> "  mulld " ^ print_reg_triple dst src1 src2
  | MulHigh64U dst src1 src2 -> "  mulhdu " ^ print_reg_triple dst src1 src2
  | Xor dst src1 src2 -> "  xor " ^ print_reg_triple dst src1 src2
  | And dst src1 src2 -> "  and " ^ print_reg_triple dst src1 src2
  | Sr64Imm dst src1 src2 -> "  srdi " ^ print_reg_pair_imm dst src1 src2
  | Sl64Imm dst src1 src2 -> "  sldi " ^ print_reg_pair_imm dst src1 src2
  | Mfvsrd dst src -> "  mfvsrd " ^ print_reg_vec dst src true
  | Mfvsrld dst src -> "  mfvsrld " ^ print_reg_vec dst src true
  | Mtvsrdd dst src1 src2 -> "  mtvsrdd " ^ print_vec_reg_pair dst src1 src2 true
  | Vxor dst src1 src2 -> "  vxor " ^ print_vec_triple dst src1 src2 false
  | Vslw dst src1 src2 -> "  vslw " ^ print_vec_triple dst src1 src2 false
  | Vsrw dst src1 src2 -> "  vsrw " ^ print_vec_triple dst src1 src2 false
  | Vcmpequw dst src1 src2 -> "  vcmpequw " ^ print_vec_triple dst src1 src2 false
  | Vsldoi dst src1 src2 count -> "  vsldoi " ^ print_vec_triple_imm dst src1 src2 count false
let print_cmp (c:ocmp) (counter:int) (p:printer) : string =
  let print_cmp_ops (o1:cmp_opr) (o2:cmp_opr) : string =
    match o2 with
    | CReg r -> "  cmpld " ^ (print_first_cmp_opr o1 p) ^ ", " ^ (print_reg r p) ^ "\n"
    | CImm n -> "  cmpldi " ^ (print_first_cmp_opr o1 p) ^ ", " ^ (string_of_int n) ^ "\n"
  in
  match c with
  | OEq o1 o2 -> print_cmp_ops o1 o2 ^ "  beq " ^ "L" ^ string_of_int counter ^ "\n"
  | ONe o1 o2 -> print_cmp_ops o1 o2 ^ "  bne "^ "L" ^ string_of_int counter ^ "\n"
  | OLe o1 o2 -> print_cmp_ops o1 o2 ^ "  ble "^ "L" ^ string_of_int counter ^ "\n"
  | OGe o1 o2 -> print_cmp_ops o1 o2 ^ "  bge "^ "L" ^ string_of_int counter ^ "\n"
  | OLt o1 o2 -> print_cmp_ops o1 o2 ^ "  blt " ^ "L" ^ string_of_int counter ^ "\n"
  | OGt o1 o2 -> print_cmp_ops o1 o2 ^ "  bgt " ^ "L" ^ string_of_int counter ^ "\n"

let rec print_block (b:codes) (n:int) (p:printer) : string & int =
  match b with
  | Nil -> ("", n)
  | head :: tail ->
    let (head_str, n') = print_code head n p in
    let (rest, n'') = print_block tail n' p in
    (head_str ^ rest, n'')
and print_code (c:code) (n:int) (p:printer) : string & int =
  match c with
  | Ins ins -> (print_ins ins p ^ "\n", n)
  | Block b -> print_block b n p
  | IfElse cond true_code false_code ->
    let n1 = n in
    let n2 = n + 1 in
    let cmp = print_cmp (cmp_not cond) n1 p in
    let (true_str, n') = print_code true_code (n + 2) p in
    let branch = "  b L" ^ string_of_int n2 ^ "\n" in
    let label1 = "L" ^ string_of_int n1 ^ ":\n" in
    let (false_str, n') = print_code false_code n' p in
    let label2 = "L" ^ string_of_int n2 ^ ":\n" in
    (cmp ^ true_str ^ branch ^ label1 ^ false_str ^ label2, n')
  | While cond body ->
    let n1 = n in
    let n2 = n + 1 in
    let branch = "  b L" ^ string_of_int n2 ^ "\n" in
    let label1 = p.align() ^ " 4\nL" ^ string_of_int n1 ^ ":\n" in
    let (body_str, n') = print_code body (n + 2) p in
    let label2 = p.align() ^ " 4\nL" ^ string_of_int n2 ^ ":\n" in
    let cmp = print_cmp cond n1 p in
    (branch ^ label1 ^ body_str ^ label2 ^ cmp, n')

let print_header (p:printer) =
  print_string (p.header())

let print_proc (name:string) (code:code) (label:int) (p:printer) : FStar.All.ML int =
  let proc = p.proc_name name in
  let (code_str, final_label) = print_code code label p in
  let ret = p.ret name in
  print_string (proc ^ code_str ^ ret);
  final_label

let print_footer (p:printer) =
  print_string (p.footer())

// Concrete printers for GCC syntax
let gcc : printer =
  let reg_prefix unit = "" in
  let vec_prefix unit = "" in
  let vsr_prefix unit = "" in
  let maddr (offset:string) (address:string) =
    offset ^ "(" ^ address ^ ")"
  in
  let const (n:int) = string_of_int n in
  let align() = ".align" in
  let header() = ".text\n" in
  let footer() = "\n" in
  let proc_name (name:string) = ".global " ^ name ^ "\n" ^ name ^ ":\n" in
  let branch_link (name:string) = "  blr\n\n" in
  {
    reg_prefix = reg_prefix;
    vec_prefix = vec_prefix;
    vsr_prefix = vsr_prefix;
    maddr      = maddr;
    const      = const;
    align      = align;
    header     = header;
    footer     = footer;
    proc_name  = proc_name;
    ret        = branch_link;
  }
