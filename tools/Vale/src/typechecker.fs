module TypeChecker

open Ast
open Ast_util
open Parse
open Microsoft.FSharp.Math
open System.Collections.Generic
open System.IO
open System
open Microsoft.FSharp.Text.Lexing

let exportsDir = ref "."

type name_info =
| Info of id_info
| Func_decl of fun_decl
| Proc_decl of (proc_decl * proc_decl option) // second proc_decl is for raw_proc
| Name of string

type export_ids_map = System.Collections.Generic.Dictionary<string, list<string>>
type scope_mod =
| Open_module of string
| Module_abbrev of (string * string)
| Local of (id * id_info)
| Func of (id * fun_decl)
| Proc of (id * proc_decl * proc_decl option)
| Symbol of string

type env = {
  curmodule: option<string>; (* name of the module being typechecked *)
  modules: list<string>; (* previously defined modules *)
  scope_mods: list<scope_mod>; (* a STACK of scope modifiers *)
  exported_ids: export_ids_map; (* identifiers reachable in a module *)
}

let default_type_module = "Vale.DefaultType"
let default_types = ["reg"; "reg32"; "opr32"; "opr"; "opr64"; "opr_quad"; "opr_imm8";
                     "opr_reg"; "mem_opr"; "mem"; "mem32"; "mem64"; "dst_opr64";
                     "reg_opr64"; "shift_amt64"; "reg_MyModule__MyType"; "opr_MyRecord"
                     "tuple"; "list"; "False"; "True"]
let init_export_ids = 
  let exported_ids = new Dictionary<string, list<string>>(10) in
  exported_ids.Add(default_type_module, default_types); exported_ids

let empty_env:env= {curmodule=None; modules=[]; scope_mods=[];
                   exported_ids = init_export_ids}

let load_exports (filename:string): string list =
  if not (File.Exists(filename)) then []
  else 
    let lines = File.ReadAllLines filename |> Array.toList in
    let rec aux (ids:list<string>) (l:list<string>) = 
      match l with
        | [] -> ids
        | line::tl -> 
          let es = line.Split ([|' '|]) |> Array.toList in
          List.append ids es in
    aux [] lines in

let load_module (env:env) (m:string):env =
  let f1 = Path.Combine (!exportsDir, m ^ ".fst.exported") in
  let f2 = Path.Combine (!exportsDir, m ^ ".fsti.exported") in
  let exports = List.append (load_exports f1) (load_exports f2) in
  let () = env.exported_ids.Add(m, exports) in
  env

let get_exported_ids (m:export_ids_map) k =
  match m.TryGetValue(k) with
  | true, v -> Some v
  | _ -> None

let load_module_exports (env:env) (m:string):env =
  match get_exported_ids env.exported_ids m with
  | Some v -> env
  | _ -> load_module env m

let find_in_module_exports (env:env) (m:string) (x:string) =
  match get_exported_ids env.exported_ids m with
  | Some l -> 
    match List.tryFind (fun elem -> elem = x) l with
    | Some n -> Some (Name n)
    | _ -> None
  | _ -> None

let name_of_id x =
  let s = match x with Id s | Reserved s | Operator s -> s in
  let es = s.Split ([|'.'|])  |> Array.toList in
  let rec aux s l = 
    match l with
    | hd::[] -> (s, hd)
    | hd :: tl -> aux (if (s = "") then hd else (s ^ "." ^ hd)) tl
    | _ -> failwith "Empty list." in
  aux "" es in

let lookup_name (env:env) (x:id) (nameOnly:bool) =
  let (mn, sn) = name_of_id x in
  let find = function
    | Open_module m when (mn = "" || m = mn) -> if nameOnly then find_in_module_exports env m sn else None
    | Module_abbrev (m, l) when (m = mn) -> if nameOnly then find_in_module_exports env l sn else None
    | Local (s, info) when s=x -> Some (Info info)
    | Func (s, decl) when s=x -> Some (Func_decl decl)
    | Proc (s, decl, raw_decl) when s=x -> Some (Proc_decl (decl,raw_decl))
    | Symbol s when (mn = "" && sn = s) -> Some (Name s)
    | _ -> None
  let rec aux = function
    | a :: q -> 
      match (find a) with
      | Some r -> Some r
      | None -> aux q
    | [] -> 
      // find in the default type module.
      find_in_module_exports env "Vale.DefaultType" sn
  aux env.scope_mods

let lookup_id env (id:id) = 
  match lookup_name env id false with
  | Some (Info info) -> Some info
  | _ -> None

let contains_id env id =
  match lookup_id env id with
  | Some _ -> true
  | _ -> false

let lookup_func (env:env) (id:id) = 
  match lookup_name env id false with
  | Some (Func_decl decl) -> Some decl
  | _ -> None

let lookup_proc env (id:id) =
  match lookup_name env id false with
  | Some (Proc_decl (decl, raw_decl)) -> Some decl
  | _ -> None

let lookup_raw_proc env (id:id) =
  match lookup_name env id false with
  | Some (Proc_decl (decl, raw_decl)) -> 
    match raw_decl with 
    | Some d -> Some d
    | _ -> None
  | _ -> None

let contains_proc env id =
  match lookup_proc env id with
  | Some _ -> true
  | _ -> false

let contains_raw_proc env id =
  match lookup_raw_proc env id with
  | Some _ -> true
  | _ -> false

let push_scope_mod env scope_mod =
 {env with scope_mods = scope_mod :: env.scope_mods}

let push_module (env:env) m =
  let env = push_scope_mod env (Open_module m) in
  load_module_exports env m

let push_module_abbrev (env:env) x l =
  let env = push_scope_mod env (Module_abbrev (x,l)) in
  load_module_exports env l

let push_id env id info =
  push_scope_mod env (Local (id, info))
  
let push_func env id func =
  push_scope_mod env (Func (id, func))
  
let push_proc env id proc raw_proc =
  push_scope_mod env (Proc (id, proc, raw_proc))

let param_info isRet (x, t, g, io, a) =
  match g with
  | (XAlias (AliasThread, e)) -> ThreadLocal {local_in_param = (io = In && (not isRet)); local_exp = e; local_typ = Some t}
  | (XAlias (AliasLocal, e)) -> ProcLocal {local_in_param = (io = In && (not isRet)); local_exp = e; local_typ = Some t}
  | XInline -> InlineLocal (Some t)
  | XOperand -> OperandLocal (io, t)
  | XPhysical | XState _ -> err ("variable must be declared ghost, operand, {:local ...}, or {:register ...} " + (err_id x))
  | XGhost -> GhostLocal ((if isRet then Mutable else Immutable), Some t)
    
let push_rets (env:env) (rets:pformal list):env =
  {env with scope_mods = List.fold (fun s (x, t, g, io, a) -> Local(x, (param_info true (x, t, g, io, a))):: s) env.scope_mods rets}

let push_params_without_rets (env:env) (args:pformal list) (rets:pformal list):env =
  let arg_in_rets arg l = List.exists (fun elem -> elem = arg) l in
  let rec aux s l = 
    match l with
    | [] -> s
    | a::q ->
    let (x, _, _, _, _) = a in
    let s = if arg_in_rets a rets then s else Local(x, (param_info false a)):: s in
    aux s q in
  {env with scope_mods = aux env.scope_mods args}

let push_lhss (env:env) (lhss:lhs list):env =
  {env with scope_mods = List.fold (fun s (x, dOpt) -> match dOpt with None -> s | Some (t, _) -> Local(x, (GhostLocal (Mutable, t)))::s) env.scope_mods lhss }    
  
let push_formals (env:env) (formals:formal list):env =
  {env with scope_mods = List.fold (fun s (x, t) -> Local(x, (GhostLocal (Immutable, t))):: s) env.scope_mods formals}

let resolve_id env id:unit =
  match id with
  | Reserved _ -> ()
  | _ ->
    match lookup_name env id true with
    | None -> err ("Identifier not found " + (err_id id))
    | Some r -> ()

let rec resolve_type env t:unit =
  let resolve_name id = 
    match lookup_name env id true with
    | Some _ -> ()
    | None -> err ("type not found " + (err_id id))
  match t with 
  | TName id -> resolve_name id
  | TApp (t, ts) -> resolve_type env t; resolve_types env ts
and resolve_types env ts = List.iter (resolve_type env) ts;

let resolve_formal (env:env) (x:id, t:typ option):unit =
  resolve_id env x;
  match t with | Some t -> resolve_type env t | None -> ();

let resolve_formals (env:env) (fs: formal list):unit = 
  List.iter (resolve_formal env) fs
  
let rec resolve_exp (env:env) (e:exp):unit= 
  match e with  
  | ELoc (loc, e) -> resolve_exp env e
  | EVar x -> resolve_id env x;
  | EInt _ | EReal _ | EBitVector _ | EBool _ | EString _ -> ()
  | EBind (b, es, fs, ts, e) -> 
    resolve_exps env es; resolve_formals env fs; resolve_triggers env ts; resolve_exp env e
  | EOp (op, es) -> resolve_exps env es;
  | EApply (x, es) ->  resolve_id env x; resolve_exps env es
and resolve_exps (env:env) (es: exp list):unit = List.iter (resolve_exp env) es
and resolve_triggers (env:env) (ts: triggers):unit = 
  List.iter (resolve_exps env) ts

let make_operand_alias (x:id) (env:env) =
  let info = 
    match lookup_id env x with
    | Some info -> info
    | None -> err ("cannot find declaration of '" + (err_id x) + "'") in
  match info with
  | OperandLocal _ | StateInfo _ | OperandAlias _ -> OperandAlias (x, info)
  | GhostLocal _ | ProcLocal _ | ThreadLocal _ | InlineLocal _ ->
      err ("'" + (err_id x) + "' must be an operand or state member")

let rec update_env_stmt (env:env) (s:stmt): env =
  match s with
  | SLoc (loc, s) -> update_env_stmt env s
  | SLabel _ | SGoto _ | SReturn | SAssume _ | SAssert _ | SCalc _ -> env
  | SVar (x, t, m, g, a, eOpt) ->
    (
      let info =
        match g with
        | XAlias (AliasThread, e) -> ThreadLocal {local_in_param = false; local_exp = e; local_typ = t}
        | XAlias (AliasLocal, e) -> ProcLocal {local_in_param = false; local_exp = e; local_typ = t}
        | XGhost -> GhostLocal (m, t)
        | XInline -> InlineLocal t
        | (XOperand | XPhysical | XState _) -> err ("variable must be declared ghost, {:local ...}, or {:register ...} " + (err_id x))
        in
      push_id env x info
    )
  | SAlias (x, y) ->
      push_id env x (make_operand_alias y env)
  | SAssign (xs, e) ->
      push_lhss env xs
  | SLetUpdates _ | SBlock _ | SQuickBlock _ | SIfElse _ | SWhile _ -> env
  | SForall (xs, ts, ex, e, b) ->
      push_formals env xs
  | SExists (xs, ts, e) ->
      push_formals env xs
 
let rec resolve_stmt (env:env) (s:stmt):env =
  let resolve env s =
    match s with
    | SLoc (loc, s) -> resolve_stmt env s
    | SLabel x -> resolve_id env x; env
    | SGoto x -> resolve_id env x; env
    | SReturn -> env
    | SAssume e -> resolve_exp env e; env
    | SAssert (attrs, e) -> resolve_exp env e; env
    | SCalc (oop, contents) -> resolve_calc_contents env contents
    | SVar (x, t, m, g, a, eOpt) -> 
      match t with | Some t -> resolve_type env t | None -> ();
      match eOpt with | Some e -> resolve_exp env e | None -> ();
      env
    | SAlias (x, y) ->  resolve_id env y; env
    | SAssign (xs, e) -> resolve_exp env e; env
    | SLetUpdates _ -> internalErr "SLetUpdates"
    | SBlock b -> resolve_stmts env b
    | SQuickBlock (x, b) -> resolve_stmts env b
    | SIfElse (g, e, b1, b2) -> 
      resolve_exp env e; let env = resolve_stmts env b1 in resolve_stmts env b2;
    | SWhile (e, invs, ed, b) ->
      resolve_exp env e; resolve_stmts env b
    | SForall (xs, ts, ex, e, b) ->
      resolve_formals env xs; resolve_triggers env ts; resolve_exp env ex; 
      resolve_exp env e; resolve_stmts env b
    | SExists (xs, ts, e) ->
      resolve_formals env xs; resolve_triggers env ts; resolve_exp env e; env in
  match s with
  | SForall (xs, ts, ex, e, b) -> 
    let env = update_env_stmt env s in
    resolve env s
  | _ ->
    let env = resolve env s in
    update_env_stmt env s
and resolve_stmts (env:env) (ss:stmt list):env = List.fold resolve_stmt env ss
and resolve_calc_content (env:env) (cc:calcContents):env =
  let {calc_exp = e; calc_op = oop; calc_hints = hints} = cc in
  resolve_exp env e; List.fold resolve_stmts env hints
and resolve_calc_contents (env:env) (contents:calcContents list):env = List.fold resolve_calc_content env contents

let process_verbatim (env:env)(d:verbatim_decl):env =
  match d with
  | VOpen m ->
    push_module env m
  | VModuleAbbrev (x, l) ->
    push_module_abbrev env x l
  | VLet l ->
    push_scope_mod env (Symbol l)
  | VType l ->
    let push_type env t = push_scope_mod env (Symbol t)
    List.fold push_type env l

let parse_verbatim (env:env) (attrs:attrs) (lines:string list):env = 
  let s = lines |> String.concat "\n " in
  let bytes = System.Text.Encoding.ASCII.GetBytes s in
  let lexbuf = LexBuffer<byte>.FromBytes bytes in
  let vdecls = Parse.verbatim_start Lex.verbatimToken lexbuf in
  List.fold process_verbatim env vdecls

let init_tcenv env:env = 
  push_module env "prims"
