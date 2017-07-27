module X64.Vale.StrongPost_i
open X64.Machine_s
open X64.Vale.State_i
open X64.Vale.Decls

#reset-options "--z3rlimit 20"

val mem_contains : m:mem -> i:int -> bool
val mem_sel : m:mem -> i:int -> nat64
val mem_upd : m:mem -> i:int -> n:nat64 -> mem

val lemma_mem_contains : m:mem -> i:int -> Lemma
  (ensures mem_contains m i == Map.contains m i)
  [SMTPat (mem_contains m i)]

val lemma_mem_sel : m:mem -> i:int -> Lemma
  (ensures mem_sel m i == Map.sel m i)
  [SMTPat (mem_sel m i)]

val lemma_mem_upd : m:mem -> i:int -> n:nat64 -> Lemma
  (ensures mem_upd m i n == Map.upd m i n)
  [SMTPat (mem_upd m i n)]

type ins =
  | Mov64 : dst:va_operand -> src:va_operand -> ins
  | Load64 : dst:va_operand -> src:va_operand -> offset:int -> ins
  | Store64 : dst:va_operand -> src:va_operand -> offset:int -> ins
  | Add64Wrap : dst:va_operand -> src:va_operand -> ins
  | Adc64Wrap : dst:va_operand -> src:va_operand -> ins
  | Mul64Wrap : src:va_operand -> ins
  | IMul64 : dst:va_operand -> src:va_operand -> ins
  | And64 : dst:va_operand -> amt:va_operand -> ins
  | Shr64 : dst:va_operand -> amt:va_operand -> ins
  | Sub64 : dst:va_operand -> src:va_operand -> ins
 
unfold let va_fast_ins_Mov64 = Mov64
unfold let va_fast_ins_Load64 = Load64
unfold let va_fast_ins_Store64 = Store64
unfold let va_fast_ins_Add64Wrap = Add64Wrap
unfold let va_fast_ins_Adc64Wrap = Adc64Wrap
unfold let va_fast_ins_Mul64Wrap = Mul64Wrap
unfold let va_fast_ins_IMul64 = IMul64
unfold let va_fast_ins_And64 = And64
unfold let va_fast_ins_Shr64 = Shr64
unfold let va_fast_ins_Sub64 = Sub64

unfold let va_inss = list ins

let valid_maddr_norm (m:maddr) (s:state) : bool =
  mem_contains s.mem (eval_maddr m s)

let valid_operand_norm (o:operand) (s:state) : bool =
  match o with
  | OConst n -> 0 <= n && n < nat64_max
  | OReg r -> true
  | OMem m -> valid_maddr_norm m s

let eval_operand_norm (o:operand) (s:state) : nat64 =
  match o with
  | OConst n -> if 0 <= n && n < nat64_max then n else 0
  | OReg r -> s.regs r
  | OMem m -> mem_sel s.mem (eval_maddr m s)

let rec regs_match (regs:list reg) (s0:state) (s1:state) =
  match regs with
  | [] -> True
  | r::regs -> s0.regs r == s1.regs r /\ regs_match regs s0 s1

let all_regs_match (s0:state) (s1:state) =
  let regs = [Rax; Rbx; Rcx; Rdx; Rsi; Rdi; Rbp; Rsp; R8; R9; R10; R11; R12; R13; R14; R15] in
  regs_match regs s0 s1

[@"opaque_to_smt"] // because of exists-interp axiom, avoid giving this to SMT
let rec strong_post (inss:list ins) (s0:state) (sN:state) : Type0 =
  match inss with
  | [] ->
      sN.ok /\
      sN.flags == s0.flags /\
      sN.mem == s0.mem /\
      all_regs_match s0 sN // for efficiency, we apply s0.regs to all registers and then discard s0.regs
  | (Mov64 (OReg Rsp) _)::_ -> True
  | (Mov64 (OReg dst) src)::inss ->
      not (valid_operand_norm src s0) \/
      (exists x.
        x == eval_operand_norm src s0 /\
        strong_post inss (update_reg dst x s0) sN)
  | (Load64 (OReg Rsp) _ _)::_ -> True
  | (Load64 (OReg dst) (OReg src) offset)::inss ->
      not (mem_contains s0.mem (s0.regs src + offset)) \/
      (exists x.
        x == mem_sel s0.mem (s0.regs src + offset) /\
        strong_post inss (update_reg dst x s0) sN)
  | (Store64 (OReg dst) src offset)::inss ->
      not (valid_operand_norm src s0) \/
      not (mem_contains s0.mem (s0.regs dst + offset)) \/
      (exists x.
        x == mem_upd s0.mem (s0.regs dst + offset) (eval_operand_norm src s0) /\
        strong_post inss ({s0 with mem = x}) sN)
  | (Add64Wrap (OReg Rsp) _)::_ -> True
  | (Add64Wrap (OReg dst) src)::inss ->
      not (valid_operand_norm src s0) \/
      (exists a x (f:nat64).
        a == s0.regs dst + eval_operand_norm src s0 /\
        x == (if a < nat64_max then a else a - nat64_max) /\
        cf f == (a >= nat64_max) /\
        strong_post inss ({update_reg dst x s0 with flags = f}) sN)
  | (Adc64Wrap (OReg Rsp) _)::_ -> True
  | (Adc64Wrap (OReg dst) src)::inss ->
      not (valid_operand_norm src s0) \/
      (exists a x (f:nat64).
        a == s0.regs dst + eval_operand_norm src s0 + (if cf s0.flags then 1 else 0) /\
        x == (if a < nat64_max then a else a - nat64_max) /\
        cf f == (a >= nat64_max) /\
        strong_post inss ({update_reg dst x s0 with flags = f}) sN)
  | (Mul64Wrap src)::inss ->
      not (valid_operand_norm src s0) \/
      (exists (rax:nat64) (rdx:nat64) (f:nat64).
        nat64_max `op_Multiply` rdx + rax == s0.regs Rax `op_Multiply` eval_operand_norm src s0 /\
        strong_post inss (update_reg Rdx rdx (update_reg Rax rax ({s0 with flags = f}))) sN)
  | (IMul64 (OReg Rsp) _)::_ -> True
  | (IMul64 (OReg dst) src)::inss ->
      let a = s0.regs dst `op_Multiply` eval_operand_norm src s0 in
      not (valid_operand_norm src s0) \/
      not (a < nat64_max) \/
      (exists (x:nat64) (f:nat64).
        x == a /\
        strong_post inss ({update_reg dst x s0 with flags = f}) sN)
  | (And64 (OReg Rsp) _)::_ -> True
  | (And64 (OReg dst) src)::inss ->
    let a = logand64 (s0.regs dst) (eval_operand_norm src s0) in
    not (valid_operand_norm src s0) \/
    (exists (x:nat64) (f:nat64).
      x == a /\
      strong_post inss ({update_reg dst x s0 with flags = f}) sN)
  | (Shr64 (OReg Rsp) _)::_ -> True
  | (Shr64 (OReg dst) src)::inss ->
    let a = shift_right64 (s0.regs dst) (eval_operand_norm src s0) in
    not (valid_operand_norm src s0) \/
    (exists (x:nat64) (f:nat64).
      x == a /\
      strong_post inss ({update_reg dst x s0 with flags = f}) sN)
  | (Sub64 (OReg Rsp) _)::_ -> True
  | (Sub64 (OReg dst) src)::inss ->
      not (valid_operand_norm src s0) \/
      not (0 <= s0.regs dst - eval_operand_norm src s0) \/
      (exists a x (f:nat64).
        a == s0.regs dst - eval_operand_norm src s0 /\
        x == a /\
        strong_post inss ({update_reg dst x s0 with flags = f}) sN)  
  | _ -> True

let rec inss_to_codes (inss:list ins) : list va_code =
  match inss with
  | (Mov64 (OReg Rsp) _)::inss -> []
  | (Mov64 (OReg dst) src)::inss -> (va_code_Mov64 (OReg dst) src)::(inss_to_codes inss)
  | (Load64 (OReg Rsp) _ _)::inss -> []
  | (Load64 (OReg dst) (OReg src) offset)::inss -> (va_code_Load64 (OReg dst) (OReg src) offset)::(inss_to_codes inss)
  | (Store64 (OReg dst) src offset)::inss -> (va_code_Store64 (OReg dst) src offset)::(inss_to_codes inss)
  | (Add64Wrap (OReg Rsp) _)::inss -> []
  | (Add64Wrap (OReg dst) src)::inss -> (va_code_Add64Wrap (OReg dst) src)::(inss_to_codes inss)
  | (Adc64Wrap (OReg Rsp) _)::inss -> []
  | (Adc64Wrap (OReg dst) src)::inss -> (va_code_Adc64Wrap (OReg dst) src)::(inss_to_codes inss)
  | (Mul64Wrap src)::inss -> (va_code_Mul64Wrap src)::(inss_to_codes inss)
  | (IMul64 (OReg Rsp) _)::inss -> []
  | (IMul64 (OReg dst) src)::inss -> (va_code_IMul64 (OReg dst) src)::(inss_to_codes inss)
  | (And64 (OReg Rsp) _)::inss -> []
  | (And64 (OReg dst) src)::inss -> (va_code_And64 (OReg dst) src)::(inss_to_codes inss)
  | (Shr64 (OReg Rsp) _)::inss -> []
  | (Shr64 (OReg dst) src)::inss -> (va_code_Shr64 (OReg dst) src)::(inss_to_codes inss)
  | (Sub64 (OReg Rsp) _)::inss -> []
  | (Sub64 (OReg dst) src)::inss -> (va_code_Sub64 (OReg dst) src)::(inss_to_codes inss)
  | _ -> []

[@"opaque_to_smt"]
let rec wp_code (inss : list ins) (post: state -> Type0) (s0:state): Type0 = 
  match inss with
  | [] -> 
       (forall okN regsN flagsN memN.
       let sN = {ok=okN; regs=regsN; flags=flagsN; mem=memN} in
       okN == s0.ok /\
       memN == s0.mem /\
       flagsN == s0.flags /\
       all_regs_match s0 sN ==>
       post sN)
  | (Mov64 (OReg Rsp) _) :: _ -> False
  | (Mov64 (OReg dst) src) :: inss ->
    valid_operand_norm src s0 /\
    (forall x. x == eval_operand_norm src s0 ==>
          wp_code inss post (update_reg dst x s0))
  | (Load64 (OReg Rsp) _ _) :: inss -> False
  | (Load64 (OReg dst) (OReg src) offset) :: inss ->
    mem_contains s0.mem (s0.regs src + offset) /\
    (forall x. x == mem_sel s0.mem (s0.regs src + offset) ==>
          wp_code inss post (update_reg dst x s0))
  | (Store64 (OReg dst) src offset) :: inss ->
    (valid_operand_norm src s0) /\
    (mem_contains s0.mem (s0.regs dst + offset)) /\
    (forall x. x == eval_operand_norm src s0 ==>
      wp_code inss post (update_mem (s0.regs dst + offset) x s0)) 
  | _ -> True


val va_lemma_strong_post_norm : inss:list ins -> s0:state -> sN:state -> Lemma
  (requires
    Some sN == va_eval_code (va_Block (normalize_term (inss_to_codes inss))) s0 /\
    s0.ok)
  (ensures
    exists ok0 regs0 flags0 mem0 okN regsN flagsN memN.
      {:pattern ({ok = ok0; regs = regs0; flags = flags0; mem = mem0}); ({ok = okN; regs = regsN; flags = flagsN; mem = memN})}
      ok0 == s0.ok /\ regs0 == s0.regs /\ flags0 == s0.flags /\ mem0 == s0.mem /\
      okN == sN.ok /\ regsN == sN.regs /\ flagsN == sN.flags /\ memN == sN.mem /\
      normalize (strong_post inss
        ({ok = ok0; regs = regs0; flags = flags0; mem = mem0})
        ({ok = okN; regs = regsN; flags = flagsN; mem = memN})))

let wp_code_delta = [
  "X64.Vale.StrongPost_i.wp_code";
  "X64.Vale.StrongPost_i.all_regs_match";
  "X64.Vale.StrongPost_i.regs_match";
  "X64.Vale.StrongPost_i.eval_operand_norm";  
  "X64.Vale.State_i.update_reg'";
  "X64.Vale.State_i.__proj__Mkstate__item__regs";
  "X64.Vale.State_i.__proj__Mkstate__item__ok" ;
  "X64.Vale.State_i.__proj__Mkstate__item__flags"; 
  "X64.Vale.State_i.__proj__Mkstate__item__mem"; 
  ]

val lemma_weakest_pre_norm: inss:list ins -> s0:state -> PURE state
  (fun (post:(state -> Type)) ->
     forall ok0 regs0 flags0 mem0. 
        ok0 == s0.ok /\
        regs0 == s0.regs /\
        flags0 == s0.flags /\
        mem0 == s0.mem ==>
        s0.ok /\
        Prims.norm [delta_only wp_code_delta; zeta; iota; primops]
                   (wp_code inss post ({ok=ok0; regs=regs0; flags=flags0; mem=mem0})))
