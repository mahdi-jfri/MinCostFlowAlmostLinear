module

public import MinCostFlow.SparseCore.Program.AssemblyBranchStepIface

/-!
# The run of the step program of a branch (`AssemblyBranchStepRun`)

The program `asmBrStepStmt` (`AssemblyBranchStepIface.lean`) reads the pointer of P4's change
record, makes three calls (the first phase, the output step of P7, the update of P10), copies six
words and returns. This file proves that, once the three calls run, the whole program runs,
returns the value of the last call, costs at most `150` steps more than the three calls, and ends
with the memory of the last call except at the six copied words (`asmBrStepStmt_runs`). The
arguments of the second and third calls are words that the earlier calls left in memory.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM

/-- The memory after the six copies of the step program: the four words at `h₁` go to
`outSlot`, then the two words at `h + 4` go to `reembSlot`. -/
def asmBrStepCopy (m : ℕ → ℕ) (o r h₁ h : ℕ) : ℕ → ℕ :=
  let m1 := Function.update m o (m h₁)
  let m2 := Function.update m1 (o + 1) (m1 (h₁ + 1))
  let m3 := Function.update m2 (o + 2) (m2 (h₁ + 2))
  let m4 := Function.update m3 (o + 3) (m3 (h₁ + 3))
  let m5 := Function.update m4 r (m4 (h + ASM_ST_REEMB))
  Function.update m5 (r + 1) (m5 (h + ASM_ST_REEMBLEN))

/-- Outside the two target ranges the copies keep the memory. -/
theorem asmBrStepCopy_other {m : ℕ → ℕ} {o r h₁ h a : ℕ} (ha : a < o ∨ o + 4 ≤ a)
    (hb : a < r ∨ r + 2 ≤ a) : asmBrStepCopy m o r h₁ h a = m a := by
  simp (disch := omega) only [asmBrStepCopy, Function.update_of_ne]

/-- The four words at `outSlot` are the four words at `h₁`, when the two target ranges are apart
from each other and from `h₁`. -/
theorem asmBrStepCopy_out {m : ℕ → ℕ} {o r h₁ h : ℕ} (hor : o + 4 ≤ r ∨ r + 2 ≤ o)
    (hoh : o + 4 ≤ h₁ ∨ h₁ + 4 ≤ o) {i : ℕ} (hi : i < 4) :
    asmBrStepCopy m o r h₁ h (o + i) = m (h₁ + i) := by
  interval_cases i <;>
    simp (disch := omega) only [asmBrStepCopy, Function.update_of_ne, Function.update_self,
      add_zero]

/-- The two words at `reembSlot` are the two words at `h + 4`, when the two target ranges are
apart from each other and from these two words. -/
theorem asmBrStepCopy_reemb {m : ℕ → ℕ} {o r h₁ h : ℕ}
    (hrh : r + 2 ≤ h + ASM_ST_REEMB ∨ h + ASM_ST_REEMB + 2 ≤ r)
    (hoh4 : o + 4 ≤ h + ASM_ST_REEMB ∨ h + ASM_ST_REEMB + 2 ≤ o) {i : ℕ} (hi : i < 2) :
    asmBrStepCopy m o r h₁ h (r + i) = m (h + ASM_ST_REEMB + i) := by
  simp only [ASM_ST_REEMB] at hrh hoh4 ⊢
  interval_cases i <;>
    simp (disch := omega) only [asmBrStepCopy, Function.update_of_ne, Function.update_self,
      add_zero, ASM_ST_REEMB, ASM_ST_REEMBLEN]

/-- **The run of the step program.** Let `chg` be the word at `fChgPtr + j`. If the first phase
runs on `[b, batch, words, edits, editWords, chg, h]`, the output step of P7 then runs on the output
graph and the tour of the branch, the four words at `h` and the end `h₁` of the first call, and the
update of P10 then runs on the readout data, the batch, `chg`, the two words at `h₁` and the end
of the second call, then the program runs and returns the end of the third call. Its memory is
that of the third call with the four words at `h₁` copied to `outSlot` and the two words at
`h + 4` copied to `reembSlot` (`asmBrStepCopy`), and it costs at most the three calls and `150`
steps. -/
theorem asmBrStepStmt_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {fCore fOut fRead : ℕ}
    {b cfH j batch words edits editWords fChgPtr outSlot reembSlot h fSplitPtr pos : ℕ} {mem : ℕ → ℕ}
    {bodyC bodyO bodyR : Stmt} {oC oO oR : Outcome} {stC stO stR : State} {cC cO cR : ℕ}
    (hb : b + ASM_BR_SIZE < 2 ^ w) (hchg : fChgPtr + j < 2 ^ w) (hsp : fSplitPtr + j < 2 ^ w)
    (hh : h + ASM_ST_SIZE < 2 ^ w) (ho : oC.value + 4 < 2 ^ w)
    (hos : outSlot + 4 < 2 ^ w) (hrs : reembSlot + 2 < 2 ^ w)
    (hfC : p.procs[fCore]? = some bodyC) (hfO : p.procs[fOut]? = some bodyO)
    (hfR : p.procs[fRead]? = some bodyR)
    (hrunC : Runs w p ω bodyC
      (startState [b, batch, words, edits, editWords, mem (fChgPtr + j), mem (fSplitPtr + j), h]
        mem pos) oC stC cC)
    (hrunO : Runs w p ω bodyO
      (startState [stC.mem (b + ASM_BR_OUT), stC.mem (b + ASM_BR_TOUR),
        stC.mem (h + ASM_ST_DEL), stC.mem (h + ASM_ST_SPLIT), stC.mem (h + ASM_ST_INS),
        stC.mem (h + ASM_ST_ROT), oC.value] stC.mem stC.pos) oO stO cO)
    (hrunR : Runs w p ω bodyR
      (startState [stO.mem (b + ASM_BR_READ), batch, words, mem (fChgPtr + j),
        stO.mem oC.value, stO.mem (oC.value + 1), oO.value] stO.mem stO.pos) oR stR cR) :
    ∃ st' c, Runs w p ω (asmBrStepStmt fCore fOut fRead)
      (startState [b, cfH, j, batch, words, edits, editWords, fChgPtr, outSlot, reembSlot, h,
        fSplitPtr] mem pos) (.returned oR.value) st' c ∧
      st'.mem = asmBrStepCopy stR.mem outSlot reembSlot oC.value h ∧ c ≤ cC + cO + cR + 150 := by
  have hk : ∀ k, k ≤ ASM_BR_SIZE → k < 2 ^ w := fun k hk => by omega
  have hkh : ∀ k, k ≤ ASM_ST_SIZE → k < 2 ^ w := fun k hk => by omega
  have h1w : (1 : ℕ) < 2 ^ w := by omega
  have h2w : (2 : ℕ) < 2 ^ w := by omega
  have h3w : (3 : ℕ) < 2 ^ w := by omega
  set chg := mem (fChgPtr + j) with hchgdef
  set spPtr := mem (fSplitPtr + j) with hspdef
  set st0 := startState [b, cfH, j, batch, words, edits, editWords, fChgPtr, outSlot, reembSlot,
    h, fSplitPtr] mem pos with hst0
  set r1 := Function.update st0.regs 12 chg with hr1
  have e1 : (Expr.load (.bin .add (.reg 7) (.reg 2))).eval w st0 = some chg := by
    simp [Expr.eval, hst0, startState, hchg, BinOp.eval, hchgdef]
  set s1 : State := { st0 with regs := r1 } with hs1
  set r1b := Function.update r1 13 spPtr with hr1b
  have e1b : (Expr.load (.bin .add (.reg 11) (.reg 2))).eval w s1 = some spPtr := by
    simp [Expr.eval, hs1, hr1, hst0, startState, hsp, BinOp.eval, hspdef]
  set s1b : State := { s1 with regs := r1b } with hs1b
  have hargsC : evalArgs w s1b [.reg 0, .reg 3, .reg 4, .reg 5, .reg 6, .reg 12, .reg 13, .reg 10] =
      some [b, batch, words, edits, editWords, chg, spPtr, h] := by
    simp [evalArgs, Expr.eval, hs1b, hr1b, hr1, hst0, startState]
  set s2 : State := { stC with regs := Function.update r1b 14 oC.value } with hs2
  have hcallC : Runs w p ω (.call 14 fCore [.reg 0, .reg 3, .reg 4, .reg 5, .reg 6, .reg 12,
      .reg 13, .reg 10]) s1b .normal s2
      (argsSize [.reg 0, .reg 3, .reg 4, .reg 5, .reg 6, .reg 12, .reg 13, .reg 10] + cC + 1) :=
    runs_call_iff.mpr ⟨_, bodyC, oC, stC, cC, hargsC, hfC, hrunC, rfl, rfl, rfl⟩
  have hargsO : evalArgs w s2 [.load (.bin .add (.reg 0) (.const ASM_BR_OUT)),
      .load (.bin .add (.reg 0) (.const ASM_BR_TOUR)),
      .load (.bin .add (.reg 10) (.const ASM_ST_DEL)),
      .load (.bin .add (.reg 10) (.const ASM_ST_SPLIT)),
      .load (.bin .add (.reg 10) (.const ASM_ST_INS)),
      .load (.bin .add (.reg 10) (.const ASM_ST_ROT)), .reg 14] =
      some [stC.mem (b + ASM_BR_OUT), stC.mem (b + ASM_BR_TOUR), stC.mem (h + ASM_ST_DEL),
        stC.mem (h + ASM_ST_SPLIT), stC.mem (h + ASM_ST_INS), stC.mem (h + ASM_ST_ROT),
        oC.value] := by
    have a1 := hk ASM_BR_OUT (by decide)
    have a2 : b + ASM_BR_OUT < 2 ^ w := by simp only [ASM_BR_OUT, ASM_BR_SIZE] at *; omega
    have a3 := hk ASM_BR_TOUR (by decide)
    have a4 : b + ASM_BR_TOUR < 2 ^ w := by simp only [ASM_BR_TOUR, ASM_BR_SIZE] at *; omega
    have a5 := hkh ASM_ST_DEL (by decide)
    have a6 : h + ASM_ST_DEL < 2 ^ w := by simp only [ASM_ST_DEL, ASM_ST_SIZE] at *; omega
    have a7 := hkh ASM_ST_SPLIT (by decide)
    have a8 : h + ASM_ST_SPLIT < 2 ^ w := by simp only [ASM_ST_SPLIT, ASM_ST_SIZE] at *; omega
    have a9 := hkh ASM_ST_INS (by decide)
    have a10 : h + ASM_ST_INS < 2 ^ w := by simp only [ASM_ST_INS, ASM_ST_SIZE] at *; omega
    have a11 := hkh ASM_ST_ROT (by decide)
    have a12 : h + ASM_ST_ROT < 2 ^ w := by simp only [ASM_ST_ROT, ASM_ST_SIZE] at *; omega
    simp [evalArgs, Expr.eval, hs2, hr1b, hr1, hst0, startState, BinOp.eval, a1, a2, a3, a4, a5,
      a6, a7, a8, a9, a10, a11, a12]
  set s3 : State := { stO with regs := Function.update s2.regs 15 oO.value } with hs3
  have hcallO : Runs w p ω (.call 15 fOut [.load (.bin .add (.reg 0) (.const ASM_BR_OUT)),
      .load (.bin .add (.reg 0) (.const ASM_BR_TOUR)),
      .load (.bin .add (.reg 10) (.const ASM_ST_DEL)),
      .load (.bin .add (.reg 10) (.const ASM_ST_SPLIT)),
      .load (.bin .add (.reg 10) (.const ASM_ST_INS)),
      .load (.bin .add (.reg 10) (.const ASM_ST_ROT)), .reg 14]) s2 .normal s3
      (argsSize [.load (.bin .add (.reg 0) (.const ASM_BR_OUT)),
        .load (.bin .add (.reg 0) (.const ASM_BR_TOUR)),
        .load (.bin .add (.reg 10) (.const ASM_ST_DEL)),
        .load (.bin .add (.reg 10) (.const ASM_ST_SPLIT)),
        .load (.bin .add (.reg 10) (.const ASM_ST_INS)),
        .load (.bin .add (.reg 10) (.const ASM_ST_ROT)), .reg 14] + cO + 1) :=
    runs_call_iff.mpr ⟨_, bodyO, oO, stO, cO, hargsO, hfO, hrunO, rfl, rfl, rfl⟩
  have hargsR : evalArgs w s3 [.load (.bin .add (.reg 0) (.const ASM_BR_READ)), .reg 3, .reg 4,
      .reg 12, .load (.reg 14), .load (.bin .add (.reg 14) (.const 1)), .reg 15] =
      some [stO.mem (b + ASM_BR_READ), batch, words, chg, stO.mem oC.value,
        stO.mem (oC.value + 1), oO.value] := by
    have a1 := hk ASM_BR_READ (by decide)
    have a2 : b + ASM_BR_READ < 2 ^ w := by simp only [ASM_BR_READ, ASM_BR_SIZE] at *; omega
    have a3 : oC.value + 1 < 2 ^ w := by omega
    simp [evalArgs, Expr.eval, hs3, hs2, hr1b, hr1, hst0, startState, BinOp.eval, a1, a2, a3, h1w]
  set s4 : State := { stR with regs := Function.update s3.regs 16 oR.value } with hs4
  have hcallR : Runs w p ω (.call 16 fRead [.load (.bin .add (.reg 0) (.const ASM_BR_READ)),
      .reg 3, .reg 4, .reg 12, .load (.reg 14), .load (.bin .add (.reg 14) (.const 1)), .reg 15])
      s3 .normal s4
      (argsSize [.load (.bin .add (.reg 0) (.const ASM_BR_READ)), .reg 3, .reg 4, .reg 12,
        .load (.reg 14), .load (.bin .add (.reg 14) (.const 1)), .reg 15] + cR + 1) :=
    runs_call_iff.mpr ⟨_, bodyR, oR, stR, cR, hargsR, hfR, hrunR, rfl, rfl, rfl⟩
  -- the six stores
  have hreg8 : s4.regs 8 = outSlot := by simp [hs4, hs3, hs2, hr1b, hr1, hst0, startState]
  have hreg9 : s4.regs 9 = reembSlot := by simp [hs4, hs3, hs2, hr1b, hr1, hst0, startState]
  have hreg10 : s4.regs 10 = h := by simp [hs4, hs3, hs2, hr1b, hr1, hst0, startState]
  have hreg14 : s4.regs 14 = oC.value := by simp [hs4, hs3, hs2]
  have hreg16 : s4.regs 16 = oR.value := by simp [hs4]
  have hh4 : h + ASM_ST_REEMB < 2 ^ w := by simp only [ASM_ST_REEMB, ASM_ST_SIZE] at *; omega
  have hh5 : h + ASM_ST_REEMBLEN < 2 ^ w := by
    simp only [ASM_ST_REEMBLEN, ASM_ST_SIZE] at *; omega
  have hc4 : ASM_ST_REEMB < 2 ^ w := hkh _ (by decide)
  have hc5 : ASM_ST_REEMBLEN < 2 ^ w := hkh _ (by decide)
  set m0 := stR.mem with hm0
  set m1 := Function.update m0 outSlot (m0 oC.value) with hm1
  set m2 := Function.update m1 (outSlot + 1) (m1 (oC.value + 1)) with hm2
  set m3 := Function.update m2 (outSlot + 2) (m2 (oC.value + 2)) with hm3
  set m4 := Function.update m3 (outSlot + 3) (m3 (oC.value + 3)) with hm4
  set m5 := Function.update m4 reembSlot (m4 (h + ASM_ST_REEMB)) with hm5
  set m6 := Function.update m5 (reembSlot + 1) (m5 (h + ASM_ST_REEMBLEN)) with hm6
  have hs4m : s4.mem = m0 := rfl
  have hk1 : (1 : ℕ) < 2 ^ w := h1w
  have q1 : Runs w p ω (.store (.reg 8) (.load (.reg 14))) s4 .normal { s4 with mem := m1 } 4 :=
    runs_store_iff.mpr ⟨outSlot, m0 oC.value, Expr.eval_reg_of_eq hreg8,
      Expr.eval_load (Expr.eval_reg_of_eq hreg14), rfl, rfl, rfl⟩
  have q2 : Runs w p ω (.store (.bin .add (.reg 8) (.const 1))
      (.load (.bin .add (.reg 14) (.const 1)))) { s4 with mem := m1 } .normal
      { s4 with mem := m2 } 8 :=
    runs_store_iff.mpr ⟨outSlot + 1, m1 (oC.value + 1),
      Expr.eval_add (Expr.eval_reg_of_eq hreg8) (Expr.eval_const h1w) (by omega),
      Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hreg14) (Expr.eval_const h1w)
        (by omega)), rfl, rfl, rfl⟩
  have q3 : Runs w p ω (.store (.bin .add (.reg 8) (.const 2))
      (.load (.bin .add (.reg 14) (.const 2)))) { s4 with mem := m2 } .normal
      { s4 with mem := m3 } 8 :=
    runs_store_iff.mpr ⟨outSlot + 2, m2 (oC.value + 2),
      Expr.eval_add (Expr.eval_reg_of_eq hreg8) (Expr.eval_const h2w) (by omega),
      Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hreg14) (Expr.eval_const h2w)
        (by omega)), rfl, rfl, rfl⟩
  have q4 : Runs w p ω (.store (.bin .add (.reg 8) (.const 3))
      (.load (.bin .add (.reg 14) (.const 3)))) { s4 with mem := m3 } .normal
      { s4 with mem := m4 } 8 :=
    runs_store_iff.mpr ⟨outSlot + 3, m3 (oC.value + 3),
      Expr.eval_add (Expr.eval_reg_of_eq hreg8) (Expr.eval_const h3w) (by omega),
      Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hreg14) (Expr.eval_const h3w)
        (by omega)), rfl, rfl, rfl⟩
  have q5 : Runs w p ω (.store (.reg 9) (.load (.bin .add (.reg 10) (.const ASM_ST_REEMB))))
      { s4 with mem := m4 } .normal { s4 with mem := m5 } 6 :=
    runs_store_iff.mpr ⟨reembSlot, m4 (h + ASM_ST_REEMB), Expr.eval_reg_of_eq hreg9,
      Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hreg10) (Expr.eval_const hc4) hh4),
      rfl, rfl, rfl⟩
  have q6 : Runs w p ω (.store (.bin .add (.reg 9) (.const 1))
      (.load (.bin .add (.reg 10) (.const ASM_ST_REEMBLEN)))) { s4 with mem := m5 } .normal
      { s4 with mem := m6 } 8 :=
    runs_store_iff.mpr ⟨reembSlot + 1, m5 (h + ASM_ST_REEMBLEN),
      Expr.eval_add (Expr.eval_reg_of_eq hreg9) (Expr.eval_const h1w) (by omega),
      Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hreg10) (Expr.eval_const hc5) hh5),
      rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.reg 16)) { s4 with mem := m6 } (.returned oR.value)
      { s4 with mem := m6 } 2 :=
    runs_ret_iff.mpr ⟨oR.value, by simp [Expr.eval, hreg16], rfl, rfl, rfl⟩
  have t1 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, q6, hret, rfl⟩)
  have t2 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, q5, t1, rfl⟩)
  have t3 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, q4, t2, rfl⟩)
  have t4 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, q3, t3, rfl⟩)
  have t5 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, q2, t4, rfl⟩)
  have t6 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, q1, t5, rfl⟩)
  have t7 := runs_seq_iff.mpr (Or.inr ⟨s4, _, _, hcallR, t6, rfl⟩)
  have t8 := runs_seq_iff.mpr (Or.inr ⟨s3, _, _, hcallO, t7, rfl⟩)
  have t9 := runs_seq_iff.mpr (Or.inr ⟨s2, _, _, hcallC, t8, rfl⟩)
  have t9b := runs_seq_iff.mpr (Or.inr ⟨s1b, _, _, runs_assign_iff.mpr ⟨_, e1b, rfl, rfl, rfl⟩,
    t9, rfl⟩)
  have t10 := runs_seq_iff.mpr (Or.inr ⟨s1, _, _, runs_assign_iff.mpr ⟨_, e1, rfl, rfl, rfl⟩,
    t9b, rfl⟩)
  refine ⟨{ s4 with mem := m6 }, _, t10, rfl, ?_⟩
  simp only [argsSize, Expr.size]
  omega

end MinCostFlow.SparseCore.Program
