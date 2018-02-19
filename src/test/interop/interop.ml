type base_type = 
  | TUInt8

type arg = string * base_type
type func_ty = string * arg list

type os = | Windows | Linux
type target = | X86

let print_low_basety = function
  | TUInt8 -> "buffer UInt8.t"

let print_explicit_basety = function
  | TUInt8 -> "#UInt8.t "

let rec print_low_args = function
  | [] -> "STL unit"
  | (a, ty)::q -> a ^ ":" ^ print_low_basety ty ^ " -> " ^ print_low_args q

let rec liveness heap = function
  | [] -> ""
  | [(a,ty)] -> "live " ^ print_explicit_basety ty ^ heap ^ " " ^ a 
  | (a, ty)::q -> "live " ^ print_explicit_basety ty ^ heap ^ " " ^ a ^ " /\\ " ^ liveness heap q

let rec disjoint = function
  | [] | [_] -> ""
  | (a, _)::q -> begin
    let rec aux = function
      | [] -> ""
      | [(b, _)] -> "disjoint " ^ a ^ " " ^ b
      | (b, _)::r -> "disjoint " ^ a ^ " " ^ b ^ " /\\" ^ aux r
  in aux q ^ disjoint q
  end

let translate_lowstar func =
  let name, args = func in
  let separator = if List.length args == 0 then " " else " /\\ " in
  "module " ^ (String.capitalize_ascii name) ^
  "\n\nopen FStar.Buffer\nopen FStar.HyperStack.ST\n\n" ^
  "assume val " ^ name ^ ": " ^ (print_low_args args) ^
  "\n\t(requires (fun h -> " ^ (liveness "h" args) ^ separator ^ (disjoint args) ^ "))\n\t" ^
  "(ensures (fun h0 _ h1 -> " ^ (liveness "h0" args) ^ separator ^ (liveness "h1" args) ^ "))\n"
  
let print_vale_bufferty = function
  | TUInt8 -> "buffer8"

let rec print_vale_args = function
  | [] -> ""
  | (a, ty)::q -> ", ghost " ^ a ^ ":" ^ print_vale_bufferty ty ^ print_vale_args q

let rec print_vale_loc_buff = function
  | [] -> ""
  | [(a, _)] -> "loc_buffer("^a^")"
  | (a, _)::q -> "loc_buffer("^a^"), " ^ print_vale_loc_buff q

let rec print_buff_readable = function
  | [] -> ""
  | (a, _)::q -> "        buffer_readable(mem, "^a^");\n" ^ print_buff_readable q

let print_calling_args os target args =
  match target with
  | X86 -> begin match os with
    | Windows -> failwith "windows calling convention not supported"
    | Linux -> begin match args with
      | [] -> ""
      | [(a, _)] -> "        rsi == buffer_addr("^a^");\n"
      | [(a, _); (b, _)] -> 
        "        rsi == buffer_addr("^a^");\n        rdi == buffer_addr("^b^");\n"
      | [(a, _); (b, _); (c, _)] -> 
        "        rsi == buffer_addr("^a^");\n        rdi == buffer_addr("^b^");\n" ^
        "        rdx == buffer_addr("^c^");\n"
      | [(a, _); (b, _); (c, _); (d, _)] -> 
        "        rsi == buffer_addr("^a^");\n        rdi == buffer_addr("^b^");\n" ^
        "        rdx == buffer_addr("^c^");\n        rcx == buffer_addr("^d^");\n"
      | [(a, _); (b, _); (c, _); (d, _); (e, _)] -> 
        "        rsi == buffer_addr("^a^");\n        rdi == buffer_addr("^b^");\n" ^
        "        rdx == buffer_addr("^c^");\n        rcx == buffer_addr("^d^");\n" ^
        "        r8 == buffer_addr("^e^");\n"
      | [(a, _); (b, _); (c, _); (d, _); (e, _); (f, _)] ->
        "        rsi == buffer_addr("^a^");\n        rdi == buffer_addr("^b^");\n" ^
        "        rdx == buffer_addr("^c^");\n        rcx == buffer_addr("^d^");\n" ^
        "        r8 == buffer_addr("^e^");\n        r9 == buffer_addr("^f^");\n"
      | _ -> failwith "Linux x86 supports only up to 6 arguments in registers"
    end
  end  

let print_vale_reads os target args =
  match target with
  | X86 -> begin match os with
    | Windows -> failwith "windows calling convention not supported"
    | Linux -> begin match args with
      | [] -> failwith "no arguments passed"
      | [_] -> "rsi;\n"
      | [_; _] -> "rsi; rdi;\n"
      | [_; _; _] -> "rsi; rdi; rdx;\n"
      | [_; _; _; _] -> "rsi; rdi; rdx; rcx;\n"
      | [_; _; _; _; _] -> "rsi; rdi; rdx; rcx; r8;\n"
      | [_; _; _; _; _; _] -> "rsi; rdi; rdx; rcx; r8; r9;\n"
      | _ -> failwith "Linux x86 only supports up to 6 arguments in registers"
    end
  end

let translate_vale os target func =
  let name, args = func in
  "#verbatim interface implementation\nmodule "^(String.capitalize_ascii name) ^
  "\nmodule M = Memory_i_s\nopen X64.Machine_s\nopen X64.Vale.State_i\nopen X64.Vale.Decls\n#set-options \"--z3rlimit 20\"\n#end verbatim\n\n" ^
  "procedure " ^ (String.capitalize_ascii name) ^ "(inline t:taint" ^ print_vale_args args ^")\n" ^
  "    requires/ensures\n" ^
  "        locs_disjoint(list(" ^ print_vale_loc_buff args ^ "));\n" ^
  print_buff_readable args ^
  print_calling_args os target args ^
  "    reads\n" ^
  "        " ^ print_vale_reads os target args ^
  "    modifies\n" ^
  "        mem; memTaint; trace;\n"^
  "{\n\n}\n"

let () = 
  let func = ("memcpy", [("src", TUInt8); ("dest", TUInt8)]) in
print_string (translate_lowstar func); print_newline(); print_newline(); print_string (translate_vale Linux X86 func);;
