type base_type = 
  | TUInt8

type arg = string * base_type
type func_ty = string * arg list

type os = | Windows | Linux
type target = | X86

let translate_lowstar func =
  let name, args = func in
  ""
  


let translate_vale os target func =
  match target with
  | X86 -> begin match os with
    | Windows -> ""
    | Linux -> ""
  end

