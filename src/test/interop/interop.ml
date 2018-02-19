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
  
let translate_vale os target func =
  match target with
  | X86 -> begin match os with
    | Windows -> ""
    | Linux -> ""
  end

let () = print_string (translate_lowstar ("memcpy", [("src", TUInt8); ("dest", TUInt8)]));;
