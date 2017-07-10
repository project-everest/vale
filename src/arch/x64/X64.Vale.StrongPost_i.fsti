module X64.Vale.StrongPost_i
open X64.Machine_s
open X64.Vale.State_i
open X64.Vale.Decls

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
  | Load64 : dst:va_operand -> src:va_operand -> offset:int -> ins
  | Store64 : dst:va_operand -> src:va_operand -> offset:int -> ins

unfold let va_inss = list ins
unfold let va_fast_ins_Load64 = Load64
unfold let va_fast_ins_Store64 = Store64

let rec regs_match (regs:list reg) (s0:state) (s1:state) =
  match regs with
  | [] -> True
  | r::regs -> s0.regs r == s1.regs r /\ regs_match regs s0 s1

let all_regs_match (s0:state) (s1:state) =
  let regs = [Rax; Rbx; Rcx; Rdx; Rsi; Rdi; Rbp; Rsp; R8; R9; R10; R11; R12; R13; R14; R15] in
  regs_match regs s0 s1

let rec strong_post (inss:list ins) (s0:state) (sN:state) : Type0 =
  match inss with
  | [] ->
      sN.ok /\
      sN.flags == s0.flags /\
      sN.mem == s0.mem /\
      all_regs_match s0 sN // for efficiency, we apply s0.regs to all registers and then discard s0.regs
  | (Load64 (OReg Rsp) (OReg src) offset)::inss -> True
  | (Load64 (OReg dst) (OReg src) offset)::inss ->
      not (mem_contains s0.mem (s0.regs src + offset)) \/
      (exists x.
        x == mem_sel s0.mem (s0.regs src + offset) /\
        strong_post inss (update_reg dst x s0) sN)
  | (Store64 (OReg dst) (OReg src) offset)::inss ->
      not (mem_contains s0.mem (s0.regs dst + offset)) \/
      (exists x.
        x == mem_upd s0.mem (s0.regs dst + offset) (s0.regs src) /\
        strong_post inss ({s0 with mem = x}) sN)
  | _ -> True

let rec inss_to_codes (inss:list ins) : list va_code =
  match inss with
  | (Load64 (OReg Rsp) (OReg src) offset)::inss -> []
  | (Load64 (OReg dst) (OReg src) offset)::inss -> (va_code_Load64 (OReg dst) (OReg src) offset)::(inss_to_codes inss)
  | (Store64 (OReg dst) (OReg src) offset)::inss -> (va_code_Store64 (OReg dst) (OReg src) offset)::(inss_to_codes inss)
  | _ -> []

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

