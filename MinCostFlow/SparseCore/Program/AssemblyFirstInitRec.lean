module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBody
public import MinCostFlow.SparseCore.Program.AssemblyBranchInitIface
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# The record stores at the end of the build (`AssemblyFirstInitRec`)

Step 7 of the body of the build (`asmFirstInitRecStmt`, `AssemblyFirstInitBody.lean`) stores three
words of the record of the branch at `h` and the sixteen words of the record of the bundle side at
`s` (register `15`). Each store writes the value of a register, or a register plus a constant, so
the registers do not change and the values are the registers at the start.

`asmFirstInitRec_runs` runs the nineteen stores and returns `AsmFiRecOut`: the value of each word,
and the memory outside these words unchanged. The two records do not meet, since the record of
the branch ends at `h + ASM_BR_SIZE ≤ s`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM

/-- One store `r + off ← e` of the record, when `r + off` is a word and `e` has the value `v`. -/
theorem runs_asmFiPut {w : ℕ} {p : Program} {ω : ℕ → Bool} {r off : ℕ} {e : Expr} {st : State}
    {v : ℕ} (hoff : st.regs r + off < 2 ^ w) (hv : e.eval w st = some v) :
    Runs w p ω (asmFiPut r off e) st .normal
      { st with mem := Function.update st.mem (st.regs r + off) v } (e.size + 4) := by
  refine runs_store_iff.mpr ⟨_, v, Expr.eval_add (Expr.eval_reg_of_eq rfl)
    (Expr.eval_const (by omega)) hoff, hv, rfl, rfl, ?_⟩
  simp only [Expr.size_bin, Expr.size_reg, Expr.size_const]
  omega

/-- One store of the record followed by the rest of the stores. -/
theorem runs_asmFiPut_seq {w : ℕ} {p : Program} {ω : ℕ → Bool} {r off : ℕ} {e : Expr}
    {rest : Stmt} {st st' : State} {o : Outcome} {v c : ℕ} (hoff : st.regs r + off < 2 ^ w)
    (hv : e.eval w st = some v)
    (hrest : Runs w p ω rest { st with mem := Function.update st.mem (st.regs r + off) v } o st'
      c) :
    Runs w p ω (asmFiPut r off e ;; rest) st o st' (e.size + 4 + c + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨_, _, _, runs_asmFiPut hoff hv, hrest, rfl⟩)

/-- The value of `r + k`, when it is a word. -/
theorem asmFi_eval_reg_add {w r k : ℕ} {st : State} (h : st.regs r + k < 2 ^ w) :
    (Expr.bin .add (.reg r) (.const k)).eval w st = some (st.regs r + k) :=
  Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) h

/-- **The memory after the record stores**, from the registers `regs` and the memory `mem` at the
start: the three words of the record of the branch at `h`, the sixteen words of the record of the
bundle side at `s`, and every other word unchanged. -/
structure AsmFiRecOut (regs mem : ℕ → ℕ) (h s : ℕ) (mem' : ℕ → ℕ) : Prop where
  emb : mem' (h + ASM_BR_EMB) = regs 32
  out : mem' (h + ASM_BR_OUT) = regs 30 + 5
  rest : mem' (h + ASM_BR_REST) = s
  bun : mem' (s + ASM_SD_BUN) = regs 25
  span : mem' (s + ASM_SD_SPAN) = regs 26
  slots : mem' (s + ASM_SD_SLOTS) = regs 23
  nslots : mem' (s + ASM_SD_NSLOTS) = regs 24
  slotCap : mem' (s + ASM_SD_SLOTCAP) = regs 11
  eCap5 : mem' (s + ASM_SD_ECAP5) = regs 11
  cap : mem' (s + ASM_SD_CAP) = regs 11
  spl : mem' (s + ASM_SD_SPL) = regs 12
  split : mem' (s + ASM_SD_SPLIT) = regs 27
  spv : mem' (s + ASM_SD_SPV) = regs 28
  spe : mem' (s + ASM_SD_SPE) = regs 11
  mmax : mem' (s + ASM_SD_MMAX) = regs 6
  cmp : mem' (s + ASM_SD_CMP) = regs 16
  bkt : mem' (s + ASM_SD_BKT) = s + 16
  ct : mem' (s + ASM_SD_CT) = regs 18
  ncomp : mem' (s + ASM_SD_NCOMP) = regs 17
  frame : ∀ a, a ≠ h + ASM_BR_EMB → a ≠ h + ASM_BR_OUT → a ≠ h + ASM_BR_REST →
    (a < s ∨ s + ASM_SD_SIZE ≤ a) → mem' a = mem a

set_option maxHeartbeats 1000000 in
/-- **The run of the record stores.** With the record of the branch at `h` (register `14`) and the
record of the bundle side at `s ≥ h + ASM_BR_SIZE` (register `15`), the nineteen stores run, keep
the registers, cost at most `120`, and leave `AsmFiRecOut`. -/
theorem asmFirstInitRec_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} {h s : ℕ}
    (r14 : st.regs 14 = h) (r15 : st.regs 15 = s) (hhs : h + ASM_BR_SIZE ≤ s)
    (hs : s + ASM_SD_SIZE < 2 ^ w) (h30 : st.regs 30 + 5 < 2 ^ w) :
    ∃ st' c, Runs w p ω asmFirstInitRecStmt st .normal st' c ∧ st'.regs = st.regs ∧
      c ≤ 120 ∧ AsmFiRecOut st.regs st.mem h s st'.mem := by
  simp only [ASM_BR_SIZE, ASM_SD_SIZE] at hhs hs
  have a14 : ∀ k < 16, st.regs 14 + k < 2 ^ w := fun k hk => by omega
  have a15 : ∀ k < 17, st.regs 15 + k < 2 ^ w := fun k hk => by omega
  have hrun := runs_asmFiPut_seq (p := p) (ω := ω) (e := .reg 32) (v := st.regs 32)
    (a14 ASM_BR_EMB (by decide)) rfl <|
    runs_asmFiPut_seq (e := .bin .add (.reg 30) (.const 5)) (v := st.regs 30 + 5)
    (a14 ASM_BR_OUT (by decide)) (asmFi_eval_reg_add h30) <|
    runs_asmFiPut_seq (e := .reg 15) (v := st.regs 15) (a14 ASM_BR_REST (by decide)) rfl <|
    runs_asmFiPut_seq (e := .reg 25) (v := st.regs 25) (a15 ASM_SD_BUN (by decide)) rfl <|
    runs_asmFiPut_seq (e := .reg 26) (v := st.regs 26) (a15 ASM_SD_SPAN (by decide)) rfl <|
    runs_asmFiPut_seq (e := .reg 23) (v := st.regs 23) (a15 ASM_SD_SLOTS (by decide)) rfl <|
    runs_asmFiPut_seq (e := .reg 24) (v := st.regs 24) (a15 ASM_SD_NSLOTS (by decide)) rfl <|
    runs_asmFiPut_seq (e := .reg 11) (v := st.regs 11) (a15 ASM_SD_SLOTCAP (by decide)) rfl <|
    runs_asmFiPut_seq (e := .reg 11) (v := st.regs 11) (a15 ASM_SD_ECAP5 (by decide)) rfl <|
    runs_asmFiPut_seq (e := .reg 11) (v := st.regs 11) (a15 ASM_SD_CAP (by decide)) rfl <|
    runs_asmFiPut_seq (e := .reg 12) (v := st.regs 12) (a15 ASM_SD_SPL (by decide)) rfl <|
    runs_asmFiPut_seq (e := .reg 27) (v := st.regs 27) (a15 ASM_SD_SPLIT (by decide)) rfl <|
    runs_asmFiPut_seq (e := .reg 28) (v := st.regs 28) (a15 ASM_SD_SPV (by decide)) rfl <|
    runs_asmFiPut_seq (e := .reg 11) (v := st.regs 11) (a15 ASM_SD_SPE (by decide)) rfl <|
    runs_asmFiPut_seq (e := .reg 6) (v := st.regs 6) (a15 ASM_SD_MMAX (by decide)) rfl <|
    runs_asmFiPut_seq (e := .reg 16) (v := st.regs 16) (a15 ASM_SD_CMP (by decide)) rfl <|
    runs_asmFiPut_seq (e := .bin .add (.reg 15) (.const 16)) (v := st.regs 15 + 16)
    (a15 ASM_SD_BKT (by decide)) (asmFi_eval_reg_add (a15 16 (by decide))) <|
    runs_asmFiPut_seq (e := .reg 18) (v := st.regs 18) (a15 ASM_SD_CT (by decide)) rfl <|
    runs_asmFiPut (e := .reg 17) (v := st.regs 17) (a15 ASM_SD_NCOMP (by decide)) rfl
  refine ⟨_, _, hrun, rfl, by simp only [Expr.size_bin, Expr.size_reg, Expr.size_const]; omega, ?_⟩
  clear hrun a14 a15
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try intro a h1 h2 h3 h4) <;>
    (try simp only [ASM_BR_EMB, ASM_BR_OUT, ASM_BR_REST, ASM_SD_SIZE] at h1 h2 h3 h4) <;>
    simp (disch := omega) only [Function.update_of_ne, Function.update_self, ASM_BR_EMB,
      ASM_BR_OUT, ASM_BR_REST, ASM_SD_BUN, ASM_SD_SPAN, ASM_SD_SLOTS, ASM_SD_NSLOTS,
      ASM_SD_SLOTCAP, ASM_SD_ECAP5, ASM_SD_CAP, ASM_SD_SPL, ASM_SD_SPLIT, ASM_SD_SPV, ASM_SD_SPE,
      ASM_SD_MMAX, ASM_SD_CMP, ASM_SD_BKT, ASM_SD_CT, ASM_SD_NCOMP, r14, r15]

end MinCostFlow.SparseCore.Program
