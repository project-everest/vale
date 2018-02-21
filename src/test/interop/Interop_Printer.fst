module Interop_Printer

type base_type = 
  | TUInt8

type ty =
  | TBuffer of base_type
  | TBase of base_type

type arg = string * ty
type func_ty = string * list arg

type os = | Windows | Linux
type target = | X86

let calling_registers os target = match target with
  | X86 -> begin match os with
    | Windows -> ["rcx"; "rdx"; "r8"; "r9"]
    | Linux -> ["rdi"; "rsi"; "rdx"; "rcx"; "r8"; "r9"]
  end

let print_low_basety = function
  | TUInt8 -> "UInt8.t"

let print_low_ty = function
  | TBuffer ty -> "buffer " ^ print_low_basety ty
  | TBase ty -> print_low_basety ty

let print_explicit_basety = function
  | TUInt8 -> "#UInt8.t "

let rec print_low_args = function
  | [] -> "STL unit"
  | (a, ty)::q -> a ^ ":" ^ print_low_ty ty ^ " -> " ^ print_low_args q

let is_buffer arg =
  let _, ty = arg in TBuffer? ty

let rec liveness heap args =
  let args = List.Tot.Base.filter is_buffer args in
  let rec aux heap = function
  | [] -> "True"
  | [(a,TBuffer ty)] -> "live " ^ print_explicit_basety ty ^ heap ^ " " ^ a 
  | [(a, TBase ty)] -> "" // Should not happen
  | (a, TBuffer ty)::q -> "live " ^ print_explicit_basety ty ^ heap ^ " " ^ a ^ " /\\ " ^ aux heap q
  | (a, TBase ty)::q -> aux heap q // Should not happen
  in aux heap args

let rec disjoint args =
  let args = List.Tot.Base.filter is_buffer args in
  let rec disjoint_aux = function
  | [] | [_] -> ""
  | (a, _)::q -> begin
    let rec aux = function
      | [] -> ""
      | [(b, _)] -> "disjoint " ^ a ^ " " ^ b
      | (b, _)::r -> "disjoint " ^ a ^ " " ^ b ^ " /\\" ^ aux r
  in aux q ^ disjoint_aux q
  end in disjoint_aux args

let translate_lowstar (func:func_ty) =
  let name, args = func in
  let separator1 = if (List.Tot.Base.length (List.Tot.Base.filter is_buffer args) <= 1) then "" else " /\\ " in
  "module " ^ name ^
  "\n\nopen FStar.Buffer\nopen FStar.HyperStack.ST\n\n" ^
  "assume val " ^ name ^ ": " ^ (print_low_args args) ^
  "\n\t(requires (fun h -> " ^ (liveness "h" args) ^ separator1 ^ (disjoint args) ^ "))\n\t" ^
  "(ensures (fun h0 _ h1 -> " ^ (liveness "h0" args) ^ " /\\ " ^ (liveness "h1" args) ^ "))\n"
  
let print_vale_bufferty = function
  | TUInt8 -> "buffer8"

let print_vale_ty = function
  | TUInt8 -> "uint8"

let rec print_vale_args = function
  | [] -> ""
  | (a, TBuffer ty)::q -> ", ghost " ^ a ^ ":" ^ print_vale_bufferty ty ^ print_vale_args q
  | (a, TBase ty)::q -> ", " ^a^ ":" ^ print_vale_ty ty ^ print_vale_args q

let rec print_vale_loc_buff = function
  | [] -> ""
  | [(a, _)] -> "loc_buffer("^a^")"
  | (a, _)::q -> "loc_buffer("^a^"), " ^ print_vale_loc_buff q

let rec print_buff_readable = function
  | [] -> ""
  | (a, _)::q -> "        buffer_readable(mem, "^a^");\n" ^ print_buff_readable q

let supported os target args = 
  List.Tot.Base.length args <= List.Tot.Base.length (calling_registers os target)

let supported_func os target func =
  let _, args = func in
  supported os target args

let print_calling_args os target (args:list arg{supported os target args}) =
  let rec aux regs (args:list arg{List.Tot.Base.length args <= List.Tot.Base.length regs}) =
  match regs, args with
    | _, [] -> ""
    | r1::rn, (a, _)::q -> "        " ^ r1 ^ " == buffer_addr(" ^ a ^ ");\n" ^ aux rn q
  in aux (calling_registers os target) args

let print_vale_reads os target (args: list arg{supported os target args}) =
  let rec aux regs (args:list arg{List.Tot.Base.length args <= List.Tot.Base.length regs}) = 
  match regs, args with
    | _, [] -> "\n"
    | a::q, _::r -> a ^ "; " ^ aux q r
  in aux (calling_registers os target) args

let translate_vale os target (func:func_ty{supported_func os target func}) =
  let name, args = func in
  "#verbatim interface implementation\nmodule "^ name ^
  "\nmodule M = Memory_i_s\nopen X64.Machine_s\nopen X64.Vale.State_i\nopen X64.Vale.Decls\n#set-options \"--z3rlimit 20\"\n#end verbatim\n\n" ^
  "procedure " ^ name ^ "(inline t:taint" ^ print_vale_args args ^")\n" ^
  "    requires/ensures\n" ^
  "        locs_disjoint(list(" ^ print_vale_loc_buff args ^ "));\n" ^
  print_buff_readable args ^
  print_calling_args os target args ^
  "    reads\n" ^
  "        " ^ print_vale_reads os target args ^
  "    modifies\n" ^
  "        rax; rbx; rcx; rdx; rsi; rdi; rbp; rsp; r8; r9; r10; r11; r12; r13; r14; r15;\n" ^
  "        mem; memTaint; trace;\n"^
  "{\n\n}\n"


let memcpy = ("memcpy", [("src", TBuffer TUInt8); ("dest", TBuffer TUInt8)])

let _ = translate_lowstar memcpy
let _ = translate_vale Linux X86 memcpy
