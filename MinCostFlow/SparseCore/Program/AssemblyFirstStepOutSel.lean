module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepOutSeed

import WordRAM.Tactic

/-!
# Phase 4 output-edge selection flags (`AssemblyFirstStepOutSel`)

Implements and verifies two deterministic Word-RAM procedures that populate the exact `O(1)`
selector arrays consumed by `asmFirstBuildDelStmt` and `asmFirstBuildInsStmt`
(`AssemblyFirstOutEdges.lean` / `AssemblyFirstOutIns.lean`):
1. `asmFirstEvalTgtEStmt` (`[outEPres, lastOp, inFDel, inAct, inTgt, e]`): pure read-only `O(1)`
   evaluator returning `1` iff `e ∈ tgtE` (`mem_targetE'_iff_dec`), `0` memory writes, `cost ≤ 30`.
2. `asmFirstMarkOutSelStmt fEvalTgt` (`[delSupPtr, delSupLen, insSupPtr, insSupLen, outEPres,
   lastOp, inDelB, inFDel, inDtot, inAct, inTgt, eCap, h]`): allocates `[h, h + 3 * eCap)` and
   fills:
   * `selDelPtr = h`: `OutSelFlagsAt` for `outDelSet`;
   * `inE'Ptr = h + eCap`: `OutDelFlagsAt` for `E' ∩ outDelSet` (matching `E'` on every leaving
     edge via `mem_applyBatch_E_of_mem_iff`);
   * `selInsPtr = h + 2 * eCap`: `OutSelFlagsAt` for `outInsSet`.
   Runs in `≤ 110 * (delSupLen + insSupLen) + 60` steps with `ZeroFrom` and full frame below `h`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-- **Pure read-only `targetE'` evaluator**, `[outEPres, lastOp, inFDel, inAct, inTgt, e]`.
Returns `1` iff `(inAct[e] ≠ 0 ∧ inTgt[e] ≠ 0) ∨ (inAct[e] = 0 ∧ (lastOp[e] = 1 ∨
(lastOp[e] = 0 ∧ (outEPres[e] ≠ 0 ∨ inFDel[e] ≠ 0))))`, else `0`. -/
def asmFirstEvalTgtEStmt : Stmt :=
  .cond (.load (.bin .add (.reg 3) (.reg 5)))
    (.ret (.load (.bin .add (.reg 4) (.reg 5))))
    (.assign 6 (.load (.bin .add (.reg 1) (.reg 5))) ;;
     .cond (.bin .eq (.reg 6) (.const 1))
       (.ret (.const 1))
       (.cond (.bin .eq (.reg 6) (.const 0))
         (.cond (.load (.bin .add (.reg 0) (.reg 5)))
           (.ret (.const 1))
           (.ret (.load (.bin .add (.reg 2) (.reg 5)))))
         (.ret (.const 0))))

/-- Loop body for `delSup` in `asmFirstMarkOutSelStmt`:
regs `0 = delSupPtr`, `1 = delSupLen`, `4 = outEPres`, `5 = lastOp`, `6 = inDelB`, `7 = inFDel`,
`8 = inDtot`, `9 = inAct`, `10 = inTgt`, `12 = selDelPtr (= h)`, `13 = inE'Ptr (= h + eCap)`,
`16 = i`, `17..22` scratch. -/
def asmFirstMarkDelBody (fEvalTgt : ℕ) : Stmt :=
  .assign 17 (.load (.bin .add (.reg 0) (.reg 16))) ;;
  .assign 18 (.load (.bin .add (.reg 4) (.reg 17))) ;;
  .cond (.reg 18)
    (.call 19 fEvalTgt [.reg 4, .reg 5, .reg 7, .reg 9, .reg 10, .reg 17] ;;
     .assign 20 (.load (.bin .add (.reg 6) (.reg 17))) ;;
     .assign 21 (.load (.bin .add (.reg 8) (.reg 17))) ;;
     .cond (.bin .add (.bin .add (.bin .eq (.reg 19) (.const 0)) (.reg 20)) (.reg 21))
       (.store (.bin .add (.reg 12) (.reg 17)) (.const 1) ;;
        .assign 22 (.load (.bin .add (.reg 5) (.reg 17))) ;;
        .cond (.bin .eq (.reg 22) (.const 2))
          .nop
          (.store (.bin .add (.reg 13) (.reg 17)) (.const 1)))
       .nop)
    .nop

/-- Loop body for `insSup` in `asmFirstMarkOutSelStmt`:
regs `2 = insSupPtr`, `3 = insSupLen`, `4 = outEPres`, `5 = lastOp`, `6 = inDelB`, `7 = inFDel`,
`8 = inDtot`, `9 = inAct`, `10 = inTgt`, `14 = selInsPtr (= h + 2 * eCap)`, `16 = i`, `17..21` scratch. -/
def asmFirstMarkInsBody (fEvalTgt : ℕ) : Stmt :=
  .assign 17 (.load (.bin .add (.reg 2) (.reg 16))) ;;
  .call 19 fEvalTgt [.reg 4, .reg 5, .reg 7, .reg 9, .reg 10, .reg 17] ;;
  .cond (.reg 19)
    (.assign 18 (.load (.bin .add (.reg 4) (.reg 17))) ;;
     .assign 20 (.load (.bin .add (.reg 6) (.reg 17))) ;;
     .assign 21 (.load (.bin .add (.reg 8) (.reg 17))) ;;
     .cond (.bin .add (.bin .add (.bin .eq (.reg 18) (.const 0)) (.reg 20)) (.reg 21))
       (.store (.bin .add (.reg 14) (.reg 17)) (.const 1))
       .nop)
    .nop

/-- **Output-edge selector builder**, `[delSupPtr, delSupLen, insSupPtr, insSupLen, outEPres,
lastOp, inDelB, inFDel, inDtot, inAct, inTgt, eCap, h]`.
Allocates `[h, h + 3 * eCap)` for `selDelPtr`, `inE'Ptr`, `selInsPtr` and returns `h + 3 * eCap`. -/
def asmFirstMarkOutSelStmt (fEvalTgt : ℕ) : Stmt :=
  .assign 13 (.bin .add (.reg 12) (.reg 11)) ;;
  .assign 14 (.bin .add (.reg 13) (.reg 11)) ;;
  .assign 15 (.bin .add (.reg 14) (.reg 11)) ;;
  forRange 16 (.const 0) (.reg 1) (asmFirstMarkDelBody fEvalTgt) ;;
  forRange 16 (.const 0) (.reg 3) (asmFirstMarkInsBody fEvalTgt) ;;
  .ret (.reg 15)

/-- Boolean decision predicate computed by `asmFirstEvalTgtEStmt`. -/
def tgtEDec (inOldS inFDel inAct inTgt : Finset ℕ) (lastOp : ℕ → ℕ) (e : ℕ) : Prop :=
  (e ∈ inAct ∧ e ∈ inTgt) ∨
    (e ∉ inAct ∧ (lastOp e = 1 ∨ (lastOp e = 0 ∧ (e ∈ inOldS ∨ e ∈ inFDel))))

end

public section

theorem asmFirstEvalTgtEStmt_noRand : asmFirstEvalTgtEStmt.NoRand := by
  simp [asmFirstEvalTgtEStmt, Stmt.NoRand]

theorem asmFirstMarkOutSelStmt_noRand (fEvalTgt : ℕ) : (asmFirstMarkOutSelStmt fEvalTgt).NoRand := by
  simp [asmFirstMarkOutSelStmt, asmFirstMarkDelBody, asmFirstMarkInsBody, forRange, forUp, Stmt.NoRand]

/-! ## Verification of `asmFirstEvalTgtEStmt` -/

theorem asmFirstEvalTgtE_runs {w outEPres lastOpPtr inFDelPtr inActPtr inTgtPtr eCap e pos : ℕ}
    {p : Program} {inOldS inFDel inAct inTgt : Finset ℕ} {lastOp : ℕ → ℕ}
    {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (he : e < eCap)
    (hOld : mem₀ (outEPres + e) = if e ∈ inOldS then 1 else 0)
    (hLO : mem₀ (lastOpPtr + e) = lastOp e)
    (hFD : mem₀ (inFDelPtr + e) = if e ∈ inFDel then 1 else 0)
    (hAct : mem₀ (inActPtr + e) = if e ∈ inAct then 1 else 0)
    (hTgt : mem₀ (inTgtPtr + e) = if e ∈ inTgt then 1 else 0)
    (h1w_o : outEPres + eCap < 2 ^ w) (h1w_l : lastOpPtr + eCap < 2 ^ w)
    (h1w_f : inFDelPtr + eCap < 2 ^ w) (h1w_a : inActPtr + eCap < 2 ^ w)
    (h1w_t : inTgtPtr + eCap < 2 ^ w) :
    let res := open Classical in if tgtEDec inOldS inFDel inAct inTgt lastOp e then 1 else 0
    ∃ st' cost,
      Runs w p ω asmFirstEvalTgtEStmt
        (startState [outEPres, lastOpPtr, inFDelPtr, inActPtr, inTgtPtr, e] mem₀ pos)
        (.returned res) st' cost ∧
      st'.mem = mem₀ ∧
      cost ≤ 30 := by
  classical
  intro res
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  set s0 := startState [outEPres, lastOpPtr, inFDelPtr, inActPtr, inTgtPtr, e] mem₀ pos
  have heAct : (Expr.load (.bin .add (.reg 3) (.reg 5))).eval w s0 = some (if e ∈ inAct then 1 else 0) :=
    Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s0, startState]))
      (Expr.eval_reg_of_eq (by simp [s0, startState])) (by omega)) hAct
  by_cases hA : e ∈ inAct
  · have hres : res = if e ∈ inTgt then 1 else 0 := by simp [res, tgtEDec, hA]
    have heTgt : (Expr.load (.bin .add (.reg 4) (.reg 5))).eval w s0 = some (if e ∈ inTgt then 1 else 0) :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s0, startState]))
        (Expr.eval_reg_of_eq (by simp [s0, startState])) (by omega)) hTgt
    rw [hres]
    exact ⟨s0, _, runs_cond_iff.mpr ⟨1, _, by simpa [hA] using heAct,
      by simpa using runs_ret_iff.mpr ⟨_, heTgt, rfl, rfl, rfl⟩, rfl⟩, rfl, by simp [Expr.size]⟩
  · set r1 := Function.update s0.regs 6 (lastOp e)
    have ha6 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 1) (.reg 5)))) s0 .normal ⟨mem₀, r1, pos⟩ 5 :=
      runs_assign_iff.mpr ⟨lastOp e, Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s0, startState]))
          (Expr.eval_reg_of_eq (by simp [s0, startState])) (by omega)) hLO, rfl, rfl, rfl⟩
    by_cases hL1 : lastOp e = 1
    · have hres : res = 1 := by simp [res, tgtEDec, hA, hL1]
      have heC1 : (Expr.bin .eq (.reg 6) (.const 1)).eval w ⟨mem₀, r1, pos⟩ = some 1 := by
        simp [Expr.eval, r1, hL1, BinOp.eval, h1w]
      rw [hres]
      refine ⟨⟨mem₀, r1, pos⟩, _, runs_cond_iff.mpr ⟨0, _, by simpa [hA] using heAct, by
        simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha6,
          runs_cond_iff.mpr ⟨1, _, heC1, by
            simpa using runs_ret_iff.mpr ⟨1, Expr.eval_const h1w, rfl, rfl, rfl⟩, rfl⟩, rfl⟩), rfl⟩,
        rfl, by simp [Expr.size]⟩
    · have heC1 : (Expr.bin .eq (.reg 6) (.const 1)).eval w ⟨mem₀, r1, pos⟩ = some 0 := by
        simp [Expr.eval, r1, hL1, BinOp.eval, h0w, h1w]
      by_cases hL0 : lastOp e = 0
      · have heC0 : (Expr.bin .eq (.reg 6) (.const 0)).eval w ⟨mem₀, r1, pos⟩ = some 1 := by
          simp [Expr.eval, r1, hL0, BinOp.eval, h0w, h1w]
        have heOld : (Expr.load (.bin .add (.reg 0) (.reg 5))).eval w ⟨mem₀, r1, pos⟩ =
            some (if e ∈ inOldS then 1 else 0) :=
          Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1, s0, startState]))
            (Expr.eval_reg_of_eq (by simp [r1, s0, startState])) (by omega)) hOld
        by_cases hO : e ∈ inOldS
        · have hres : res = 1 := by simp [res, tgtEDec, hA, hL0, hO]
          rw [hres]
          refine ⟨⟨mem₀, r1, pos⟩, _, runs_cond_iff.mpr ⟨0, _, by simpa [hA] using heAct, by
            simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha6,
              runs_cond_iff.mpr ⟨0, _, heC1, by
                simpa using runs_cond_iff.mpr ⟨1, _, heC0, by
                  simpa using runs_cond_iff.mpr ⟨1, _, by simpa [hO] using heOld, by
                    simpa using runs_ret_iff.mpr ⟨1, Expr.eval_const h1w, rfl, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩), rfl⟩,
            rfl, by simp [Expr.size]⟩
        · have hres : res = if e ∈ inFDel then 1 else 0 := by simp [res, tgtEDec, hA, hL0, hO]
          have heFD : (Expr.load (.bin .add (.reg 2) (.reg 5))).eval w ⟨mem₀, r1, pos⟩ =
              some (if e ∈ inFDel then 1 else 0) :=
            Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1, s0, startState]))
              (Expr.eval_reg_of_eq (by simp [r1, s0, startState])) (by omega)) hFD
          rw [hres]
          refine ⟨⟨mem₀, r1, pos⟩, _, runs_cond_iff.mpr ⟨0, _, by simpa [hA] using heAct, by
            simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha6,
              runs_cond_iff.mpr ⟨0, _, heC1, by
                simpa using runs_cond_iff.mpr ⟨1, _, heC0, by
                  simpa using runs_cond_iff.mpr ⟨0, _, by simpa [hO] using heOld, by
                    simpa using runs_ret_iff.mpr ⟨_, heFD, rfl, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩), rfl⟩,
            rfl, by simp [Expr.size]⟩
      · have hres : res = 0 := by simp [res, tgtEDec, hA, hL1, hL0]
        have heC0 : (Expr.bin .eq (.reg 6) (.const 0)).eval w ⟨mem₀, r1, pos⟩ = some 0 := by
          simp [Expr.eval, r1, hL0, BinOp.eval, h0w]
        rw [hres]
        refine ⟨⟨mem₀, r1, pos⟩, _, runs_cond_iff.mpr ⟨0, _, by simpa [hA] using heAct, by
          simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha6,
            runs_cond_iff.mpr ⟨0, _, heC1, by
              simpa using runs_cond_iff.mpr ⟨0, _, heC0, by
                simpa using runs_ret_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩), rfl⟩,
          rfl, by simp [Expr.size]⟩

/-! ## Verification of `asmFirstMarkOutSelStmt` -/

set_option maxHeartbeats 600000 in
theorem asmFirstMarkOutSel_runs
    {w fEvalTgt delSupPtr insSupPtr outEPres lastOpPtr inDelBPtr inFDelPtr
      inDtotPtr inActPtr inTgtPtr eCap h pos : ℕ} {p : Program}
    (hfEval : p.procs[fEvalTgt]? = some asmFirstEvalTgtEStmt)
    {delSup insSup : List ℕ}
    {inOldS inDelB inFDel inDtot inAct inTgt outDelS outInsS E' : Finset ℕ}
    {lastOp : ℕ → ℕ} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hDS : ListAt mem₀ delSupPtr delSup) (hDS_le : delSupPtr + delSup.length ≤ h)
    (hDS_cap : ∀ e ∈ delSup, e < eCap) (hDS_cov : ∀ e ∈ outDelS, e ∈ delSup)
    (hIS : ListAt mem₀ insSupPtr insSup) (hIS_le : insSupPtr + insSup.length ≤ h)
    (hIS_cap : ∀ e ∈ insSup, e < eCap) (hIS_cov : ∀ e ∈ outInsS, e ∈ insSup)
    (hOld : ∀ e < eCap, mem₀ (outEPres + e) = if e ∈ inOldS then 1 else 0) (hOld_le : outEPres + eCap ≤ h)
    (hLO : ∀ e < eCap, mem₀ (lastOpPtr + e) = lastOp e) (hLO_le : lastOpPtr + eCap ≤ h)
    (hDB : ∀ e < eCap, mem₀ (inDelBPtr + e) = if e ∈ inDelB then 1 else 0) (hDB_le : inDelBPtr + eCap ≤ h)
    (hFD : ∀ e < eCap, mem₀ (inFDelPtr + e) = if e ∈ inFDel then 1 else 0) (hFD_le : inFDelPtr + eCap ≤ h)
    (hDT : ∀ e < eCap, mem₀ (inDtotPtr + e) = if e ∈ inDtot then 1 else 0) (hDT_le : inDtotPtr + eCap ≤ h)
    (hAct : ∀ e < eCap, mem₀ (inActPtr + e) = if e ∈ inAct then 1 else 0) (hAct_le : inActPtr + eCap ≤ h)
    (hTgt : ∀ e < eCap, mem₀ (inTgtPtr + e) = if e ∈ inTgt then 1 else 0) (hTgt_le : inTgtPtr + eCap ≤ h)
    (hDel_iff : ∀ e ∈ delSup, e ∈ outDelS ↔
      e ∈ inOldS ∧ (¬ tgtEDec inOldS inFDel inAct inTgt lastOp e ∨ e ∈ inDelB ∨ e ∈ inDtot))
    (hE'_iff : ∀ e ∈ outDelS, e ∈ E' ↔ lastOp e ≠ 2)
    (hIns_iff : ∀ e ∈ insSup, e ∈ outInsS ↔
      tgtEDec inOldS inFDel inAct inTgt lastOp e ∧ (e ∉ inOldS ∨ e ∈ inDelB ∨ e ∈ inDtot))
    (hz : ZeroFrom mem₀ h)
    (hsp : h + 3 * eCap < 2 ^ w) :
    ∃ st' cost,
      Runs w p ω (asmFirstMarkOutSelStmt fEvalTgt)
        (startState [delSupPtr, delSup.length, insSupPtr, insSup.length, outEPres,
          lastOpPtr, inDelBPtr, inFDelPtr, inDtotPtr, inActPtr, inTgtPtr, eCap, h] mem₀ pos)
        (.returned (h + 3 * eCap)) st' cost ∧
      OutSelFlagsAt st'.mem h eCap outDelS ∧
      OutDelFlagsAt st'.mem (h + eCap) eCap (E' ∩ outDelS) ∧
      OutSelFlagsAt st'.mem (h + 2 * eCap) eCap outInsS ∧
      ZeroFrom st'.mem (h + 3 * eCap) ∧
      (∀ a < h, st'.mem a = mem₀ a) ∧
      cost ≤ 115 * (delSup.length + insSup.length) + 80 := by
  classical
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  set s0 := startState [delSupPtr, delSup.length, insSupPtr, insSup.length, outEPres,
    lastOpPtr, inDelBPtr, inFDelPtr, inDtotPtr, inActPtr, inTgtPtr, eCap, h] mem₀ pos
  set r1 := Function.update s0.regs 13 (h + eCap)
  set r2 := Function.update r1 14 (h + 2 * eCap)
  set r3 := Function.update r2 15 (h + 3 * eCap)
  have ha13 : Runs w p ω (.assign 13 (.bin .add (.reg 12) (.reg 11))) s0 .normal ⟨mem₀, r1, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨h + eCap, Expr.eval_add (Expr.eval_reg_of_eq (by simp [s0, startState]))
      (Expr.eval_reg_of_eq (by simp [s0, startState])) (by omega), rfl, rfl, rfl⟩
  have ha14 : Runs w p ω (.assign 14 (.bin .add (.reg 13) (.reg 11))) ⟨mem₀, r1, pos⟩ .normal ⟨mem₀, r2, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨h + 2 * eCap, by
      have h13r : r1 13 = h + eCap := by simp [r1]
      have h11r : r1 11 = eCap := by simp [r1, s0, startState]
      have he : (Expr.bin .add (.reg 13) (.reg 11)).eval w ⟨mem₀, r1, pos⟩ = some (h + eCap + eCap) :=
        Expr.eval_add (Expr.eval_reg_of_eq h13r) (Expr.eval_reg_of_eq h11r) (by omega)
      simpa [show h + eCap + eCap = h + 2 * eCap by omega] using he, rfl, rfl, rfl⟩
  have ha15 : Runs w p ω (.assign 15 (.bin .add (.reg 14) (.reg 11))) ⟨mem₀, r2, pos⟩ .normal ⟨mem₀, r3, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨h + 3 * eCap, by
      have h14r : r2 14 = h + 2 * eCap := by simp [r2]
      have h11r : r2 11 = eCap := by simp [r2, r1, s0, startState]
      have he : (Expr.bin .add (.reg 14) (.reg 11)).eval w ⟨mem₀, r2, pos⟩ = some (h + 2 * eCap + eCap) :=
        Expr.eval_add (Expr.eval_reg_of_eq h14r) (Expr.eval_reg_of_eq h11r) (by omega)
      simpa [show h + 2 * eCap + eCap = h + 3 * eCap by omega] using he, rfl, rfl, rfl⟩
  -- Loop 1: delSup
  let dInv : ℕ → State → Prop := fun i st =>
    st.regs 0 = delSupPtr ∧ st.regs 1 = delSup.length ∧ st.regs 2 = insSupPtr ∧ st.regs 3 = insSup.length ∧
    st.regs 4 = outEPres ∧ st.regs 5 = lastOpPtr ∧ st.regs 6 = inDelBPtr ∧ st.regs 7 = inFDelPtr ∧
    st.regs 8 = inDtotPtr ∧ st.regs 9 = inActPtr ∧ st.regs 10 = inTgtPtr ∧
    st.regs 12 = h ∧ st.regs 13 = h + eCap ∧ st.regs 14 = h + 2 * eCap ∧ st.regs 15 = h + 3 * eCap ∧
    st.regs 16 = i ∧
    (∀ e < eCap, st.mem (h + e) = if e ∈ delSup.take i ∧ e ∈ outDelS then 1 else 0) ∧
    (∀ e < eCap, st.mem (h + eCap + e) = if e ∈ delSup.take i ∧ e ∈ E' ∩ outDelS then 1 else 0) ∧
    ZeroFrom st.mem (h + 2 * eCap) ∧
    (∀ a < h, st.mem a = mem₀ a)
  have hDloop := Triple.forRange_le (w := w) (p := p) (r := 16) (lo := .const 0) (hi := .reg 1)
    (body := asmFirstMarkDelBody fEvalTgt)
    (P := fun st => dInv 0 { st with regs := Function.update st.regs 16 0 })
    (Inv := dInv) (fun _ => 100) 0 delSup.length (Nat.zero_le _) h1w (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const h0w, hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.1)
    (fun i _ hi st ω' ⟨r0, r1', r2', r3', r4, r5, r6, r7, r8, r9, r10, r12, r13, r14, r15, r16, hsd, hse, hz2, hfr⟩ => by
      set e := delSup[i]'hi
      have he_mem : e ∈ delSup := List.getElem_mem hi
      have heCap : e < eCap := hDS_cap e he_mem
      have hme : st.mem (delSupPtr + i) = e := (hfr _ (by omega)).trans (hDS i hi)
      have hmOld : st.mem (outEPres + e) = if e ∈ inOldS then 1 else 0 := (hfr _ (by omega)).trans (hOld e heCap)
      have hmLO : st.mem (lastOpPtr + e) = lastOp e := (hfr _ (by omega)).trans (hLO e heCap)
      have hmDB : st.mem (inDelBPtr + e) = if e ∈ inDelB then 1 else 0 := (hfr _ (by omega)).trans (hDB e heCap)
      have hmFD : st.mem (inFDelPtr + e) = if e ∈ inFDel then 1 else 0 := (hfr _ (by omega)).trans (hFD e heCap)
      have hmDT : st.mem (inDtotPtr + e) = if e ∈ inDtot then 1 else 0 := (hfr _ (by omega)).trans (hDT e heCap)
      have hmAct : st.mem (inActPtr + e) = if e ∈ inAct then 1 else 0 := (hfr _ (by omega)).trans (hAct e heCap)
      have hmTgt : st.mem (inTgtPtr + e) = if e ∈ inTgt then 1 else 0 := (hfr _ (by omega)).trans (hTgt e heCap)
      set rA := Function.update st.regs 17 e
      set rB := Function.update rA 18 (if e ∈ inOldS then 1 else 0)
      have h17 : Runs w p ω' (.assign 17 (.load (.bin .add (.reg 0) (.reg 16)))) st .normal ⟨st.mem, rA, st.pos⟩ 5 :=
        runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r16) (by omega)) hme, rfl, rfl, rfl⟩
      have h18 : Runs w p ω' (.assign 18 (.load (.bin .add (.reg 4) (.reg 17))))
          ⟨st.mem, rA, st.pos⟩ .normal ⟨st.mem, rB, st.pos⟩ 5 :=
        runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r4])) (Expr.eval_reg_of_eq (by simp [rA])) (by omega))
          hmOld, rfl, rfl, rfl⟩
      by_cases hO : e ∈ inOldS
      · obtain ⟨stE, cE, hrE, hmemE, hcE⟩ := asmFirstEvalTgtE_runs (p := p) (ω := ω') (pos := st.pos)
          hw16 heCap hmOld hmLO hmFD hmAct hmTgt (by omega) (by omega) (by omega) (by omega) (by omega)
        set tval := if tgtEDec inOldS inFDel inAct inTgt lastOp e then 1 else 0
        set rC := Function.update rB 19 tval
        set rD := Function.update rC 20 (if e ∈ inDelB then 1 else 0)
        set rE := Function.update rD 21 (if e ∈ inDtot then 1 else 0)
        have heArgs : evalArgs w ⟨st.mem, rB, st.pos⟩ [.reg 4, .reg 5, .reg 7, .reg 9, .reg 10, .reg 17] =
            some [outEPres, lastOpPtr, inFDelPtr, inActPtr, inTgtPtr, e] :=
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, r4])) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, r5])) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, r7])) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, r9])) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA, r10])) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [rB, rA])) <| evalArgs_nil _ _
        have hcall : Runs w p ω' (.call 19 fEvalTgt [.reg 4, .reg 5, .reg 7, .reg 9, .reg 10, .reg 17])
            ⟨st.mem, rB, st.pos⟩ .normal ⟨st.mem, rC, stE.pos⟩
            (argsSize [.reg 4, .reg 5, .reg 7, .reg 9, .reg 10, .reg 17] + cE + 1) := by
          have h0 : Runs w p ω' (.call 19 fEvalTgt [.reg 4, .reg 5, .reg 7, .reg 9, .reg 10, .reg 17])
              ⟨st.mem, rB, st.pos⟩ .normal ⟨stE.mem, rC, stE.pos⟩
              (argsSize [.reg 4, .reg 5, .reg 7, .reg 9, .reg 10, .reg 17] + cE + 1) :=
            runs_call_iff.mpr ⟨_, asmFirstEvalTgtEStmt, .returned tval, stE, cE, heArgs, hfEval, hrE, rfl, rfl, rfl⟩
          rwa [hmemE] at h0
        have h20 : Runs w p ω' (.assign 20 (.load (.bin .add (.reg 6) (.reg 17))))
            ⟨st.mem, rC, stE.pos⟩ .normal ⟨st.mem, rD, stE.pos⟩ 5 :=
          runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rC, rB, rA, r6]))
              (Expr.eval_reg_of_eq (by simp [rC, rB, rA])) (by omega)) hmDB, rfl, rfl, rfl⟩
        have h21 : Runs w p ω' (.assign 21 (.load (.bin .add (.reg 8) (.reg 17))))
            ⟨st.mem, rD, stE.pos⟩ .normal ⟨st.mem, rE, stE.pos⟩ 5 :=
          runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rD, rC, rB, rA, r8]))
              (Expr.eval_reg_of_eq (by simp [rD, rC, rB, rA])) (by omega)) hmDT, rfl, rfl, rfl⟩
        set condV := (if tval = 0 then 1 else 0) + (if e ∈ inDelB then 1 else 0) + (if e ∈ inDtot then 1 else 0)
        have hcondE : (Expr.bin .add (.bin .add (.bin .eq (.reg 19) (.const 0)) (.reg 20)) (.reg 21)).eval w
            ⟨st.mem, rE, stE.pos⟩ = some condV := by
          have he19 : (Expr.bin .eq (.reg 19) (.const 0)).eval w ⟨st.mem, rE, stE.pos⟩ =
              some (if tval = 0 then 1 else 0) := by
            have hr19 : rE 19 = tval := by simp [rE, rD, rC]
            by_cases ht0 : tval = 0 <;> simp [Expr.eval, hr19, ht0, BinOp.eval, h0w, h1w]
          have hr20 : rE 20 = if e ∈ inDelB then 1 else 0 := by simp [rE, rD]
          have hr21 : rE 21 = if e ∈ inDtot then 1 else 0 := by simp [rE]
          have h12' : (Expr.bin .add (.bin .eq (.reg 19) (.const 0)) (.reg 20)).eval w ⟨st.mem, rE, stE.pos⟩ =
              some ((if tval = 0 then 1 else 0) + (if e ∈ inDelB then 1 else 0)) :=
            Expr.eval_add he19 (Expr.eval_reg_of_eq hr20) (by split_ifs <;> omega)
          exact Expr.eval_add h12' (Expr.eval_reg_of_eq hr21) (by split_ifs <;> omega)
        have hcond_iff : condV ≠ 0 ↔ e ∈ outDelS := by
          rw [hDel_iff e he_mem]; simp only [hO, true_and, condV, tval]; split_ifs <;> simp_all
        by_cases heOut : e ∈ outDelS
        · have hcv_ne : condV ≠ 0 := hcond_iff.mpr heOut
          set m1 := Function.update st.mem (h + e) 1
          set rF := Function.update rE 22 (lastOp e)
          have hst1 : Runs w p ω' (.store (.bin .add (.reg 12) (.reg 17)) (.const 1))
              ⟨st.mem, rE, stE.pos⟩ .normal ⟨m1, rE, stE.pos⟩ 5 :=
            runs_store_iff.mpr ⟨h + e, 1,
              Expr.eval_add (Expr.eval_reg_of_eq (by simp [rE, rD, rC, rB, rA, r12]))
                (Expr.eval_reg_of_eq (by simp [rE, rD, rC, rB, rA])) (by omega),
              Expr.eval_const h1w, rfl, rfl, rfl⟩
          have hm1_lo : m1 (lastOpPtr + e) = lastOp e := by
            dsimp only [m1]; rw [Function.update_of_ne (by omega)]; exact hmLO
          have h22 : Runs w p ω' (.assign 22 (.load (.bin .add (.reg 5) (.reg 17))))
              ⟨m1, rE, stE.pos⟩ .normal ⟨m1, rF, stE.pos⟩ 5 :=
            runs_assign_iff.mpr ⟨lastOp e, Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rE, rD, rC, rB, rA, r5]))
                (Expr.eval_reg_of_eq (by simp [rE, rD, rC, rB, rA])) (by omega)) hm1_lo, rfl, rfl, rfl⟩
          set m2 := if lastOp e = 2 then m1 else Function.update m1 (h + eCap + e) 1
          have hbr2 : ∃ c2, Runs w p ω'
              (.cond (.bin .eq (.reg 22) (.const 2)) .nop (.store (.bin .add (.reg 13) (.reg 17)) (.const 1)))
              ⟨m1, rF, stE.pos⟩ .normal ⟨m2, rF, stE.pos⟩ c2 ∧ c2 ≤ 10 := by
            by_cases hl2 : lastOp e = 2
            · have he2 : (Expr.bin .eq (.reg 22) (.const 2)).eval w ⟨m1, rF, stE.pos⟩ = some 1 := by
                simp [Expr.eval, rF, hl2, BinOp.eval, h1w, h2w]
              exact ⟨_, runs_cond_iff.mpr ⟨1, 1, he2, by
                simpa [m2, hl2] using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩, by simp [Expr.size]⟩
            · have he2 : (Expr.bin .eq (.reg 22) (.const 2)).eval w ⟨m1, rF, stE.pos⟩ = some 0 := by
                simp [Expr.eval, rF, hl2, BinOp.eval, h0w, h2w]
              have hst2 : Runs w p ω' (.store (.bin .add (.reg 13) (.reg 17)) (.const 1))
                  ⟨m1, rF, stE.pos⟩ .normal ⟨Function.update m1 (h + eCap + e) 1, rF, stE.pos⟩ 5 :=
                runs_store_iff.mpr ⟨h + eCap + e, 1,
                  Expr.eval_add (Expr.eval_reg_of_eq (by simp [rF, rE, rD, rC, rB, rA, r13]))
                    (Expr.eval_reg_of_eq (by simp [rF, rE, rD, rC, rB, rA])) (by omega),
                  Expr.eval_const h1w, rfl, rfl, rfl⟩
              exact ⟨_, runs_cond_iff.mpr ⟨0, 5, he2, by simpa [m2, hl2] using hst2, rfl⟩, by simp [Expr.size]⟩
          obtain ⟨c2, hr2, hc2⟩ := hbr2
          refine ⟨.normal, ⟨m2, rF, stE.pos⟩, _,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h17,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, h18,
                runs_cond_iff.mpr ⟨1, _, Expr.eval_reg_of_eq (by simp [rB, hO]), by
                  simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcall,
                    runs_seq_iff.mpr (Or.inr ⟨_, _, _, h20,
                      runs_seq_iff.mpr (Or.inr ⟨_, _, _, h21,
                        runs_cond_iff.mpr ⟨condV, _, hcondE, by
                          simpa [hcv_ne] using runs_seq_iff.mpr (Or.inr ⟨_, _, _, hst1,
                            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h22, hr2, rfl⟩), rfl⟩), rfl⟩,
                        rfl⟩), rfl⟩), rfl⟩), rfl⟩, rfl⟩), rfl⟩),
            ⟨⟨by simp [rF, rE, rD, rC, rB, rA, r0], by simp [rF, rE, rD, rC, rB, rA, r1'],
              by simp [rF, rE, rD, rC, rB, rA, r2'], by simp [rF, rE, rD, rC, rB, rA, r3'],
              by simp [rF, rE, rD, rC, rB, rA, r4], by simp [rF, rE, rD, rC, rB, rA, r5],
              by simp [rF, rE, rD, rC, rB, rA, r6], by simp [rF, rE, rD, rC, rB, rA, r7],
              by simp [rF, rE, rD, rC, rB, rA, r8], by simp [rF, rE, rD, rC, rB, rA, r9],
              by simp [rF, rE, rD, rC, rB, rA, r10], by simp [rF, rE, rD, rC, rB, rA, r12],
              by simp [rF, rE, rD, rC, rB, rA, r13], by simp [rF, rE, rD, rC, rB, rA, r14],
              by simp [rF, rE, rD, rC, rB, rA, r15], by simp, ?_, ?_, ?_, ?_⟩,
             by simp [rF, rE, rD, rC, rB, rA, r16]⟩,
            by show _ ≤ 100; simp only [Expr.size]; omega⟩
          · intro e' he'
            change m2 (h + e') = if e' ∈ delSup.take (i + 1) ∧ e' ∈ outDelS then 1 else 0
            have htk : e' ∈ delSup.take (i + 1) ↔ e' ∈ delSup.take i ∨ e' = e := by
              rw [List.take_succ_eq_append_getElem hi, List.mem_append, List.mem_singleton]
            by_cases hee : e' = e
            · subst hee; by_cases hl2 : lastOp e = 2
              · simp [m2, hl2, m1, htk, heOut]
              · simp only [m2, hl2, ↓reduceIte]
                rw [Function.update_of_ne (by omega : h + e ≠ h + eCap + e)]; simp [m1, htk, heOut]
            · simp only [htk, hee, or_false]
              have hm2_eq : m2 (h + e') = st.mem (h + e') := by
                by_cases hl2 : lastOp e = 2
                · simp [m2, hl2, m1, Function.update_of_ne (by omega : h + e' ≠ h + e)]
                · simp only [m2, hl2, ↓reduceIte]
                  rw [Function.update_of_ne (by omega : h + e' ≠ h + eCap + e)]
                  simp [m1, Function.update_of_ne (by omega : h + e' ≠ h + e)]
              rw [hm2_eq]; exact hsd e' he'
          · intro e' he'
            change m2 (h + eCap + e') = if e' ∈ delSup.take (i + 1) ∧ e' ∈ E' ∩ outDelS then 1 else 0
            have htk : e' ∈ delSup.take (i + 1) ↔ e' ∈ delSup.take i ∨ e' = e := by
              rw [List.take_succ_eq_append_getElem hi, List.mem_append, List.mem_singleton]
            by_cases hee : e' = e
            · subst hee
              have hE'e : e ∈ E' ↔ lastOp e ≠ 2 := hE'_iff e heOut
              by_cases hl2 : lastOp e = 2
              · have hneE' : e ∉ E' := fun hE => (hE'e.mp hE) hl2
                have hm2_eq : m2 (h + eCap + e) = st.mem (h + eCap + e) := by
                  simp only [m2, hl2, ↓reduceIte, m1, Function.update_of_ne (by omega : h + eCap + e ≠ h + e)]
                rw [hm2_eq, hse e heCap]; simp [hneE']
              · have hE'in : e ∈ E' := hE'e.mpr hl2
                simp [m2, hl2, htk, heOut, hE'in]
            · simp only [htk, hee, or_false]
              have hm2_eq : m2 (h + eCap + e') = st.mem (h + eCap + e') := by
                simp only [m2]; split_ifs
                · simp [m1, Function.update_of_ne (by omega : h + eCap + e' ≠ h + e)]
                · rw [Function.update_of_ne (by omega : h + eCap + e' ≠ h + eCap + e)]
                  simp [m1, Function.update_of_ne (by omega : h + eCap + e' ≠ h + e)]
              rw [hm2_eq]; exact hse e' he'
          · intro a ha
            change m2 a = 0
            have : m2 a = st.mem a := by
              simp only [m2]; split_ifs
              · simp [m1, Function.update_of_ne (by omega : a ≠ h + e)]
              · rw [Function.update_of_ne (by omega : a ≠ h + eCap + e)]
                simp [m1, Function.update_of_ne (by omega : a ≠ h + e)]
            rw [this]; exact hz2 a ha
          · intro a ha
            change m2 a = mem₀ a
            have : m2 a = st.mem a := by
              simp only [m2]; split_ifs
              · simp [m1, Function.update_of_ne (by omega : a ≠ h + e)]
              · rw [Function.update_of_ne (by omega : a ≠ h + eCap + e)]
                simp [m1, Function.update_of_ne (by omega : a ≠ h + e)]
            rw [this]; exact hfr a ha
        · have hcv0 : condV = 0 := Classical.not_not.mp fun hne => heOut (hcond_iff.mp hne)
          refine ⟨.normal, ⟨st.mem, rE, stE.pos⟩, _,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h17,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, h18,
                runs_cond_iff.mpr ⟨1, _, Expr.eval_reg_of_eq (by simp [rB, hO]), by
                  simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcall,
                    runs_seq_iff.mpr (Or.inr ⟨_, _, _, h20,
                      runs_seq_iff.mpr (Or.inr ⟨_, _, _, h21,
                        runs_cond_iff.mpr ⟨0, 1, by simpa [hcv0] using hcondE,
                          by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
                        rfl⟩), rfl⟩), rfl⟩), rfl⟩, rfl⟩), rfl⟩),
            ⟨⟨by simp [rE, rD, rC, rB, rA, r0], by simp [rE, rD, rC, rB, rA, r1'],
              by simp [rE, rD, rC, rB, rA, r2'], by simp [rE, rD, rC, rB, rA, r3'],
              by simp [rE, rD, rC, rB, rA, r4], by simp [rE, rD, rC, rB, rA, r5],
              by simp [rE, rD, rC, rB, rA, r6], by simp [rE, rD, rC, rB, rA, r7],
              by simp [rE, rD, rC, rB, rA, r8], by simp [rE, rD, rC, rB, rA, r9],
              by simp [rE, rD, rC, rB, rA, r10], by simp [rE, rD, rC, rB, rA, r12],
              by simp [rE, rD, rC, rB, rA, r13], by simp [rE, rD, rC, rB, rA, r14],
              by simp [rE, rD, rC, rB, rA, r15], by simp, ?_, ?_, hz2, hfr⟩,
             by simp [rE, rD, rC, rB, rA, r16]⟩,
            by show _ ≤ 100; simp only [Expr.size]; omega⟩
          · intro e' he'
            have htk : e' ∈ delSup.take (i + 1) ↔ e' ∈ delSup.take i ∨ e' = e := by
              rw [List.take_succ_eq_append_getElem hi, List.mem_append, List.mem_singleton]
            by_cases hee : e' = e
            · subst hee; rw [hsd e heCap]; simp [heOut]
            · simp only [htk, hee, or_false]; exact hsd e' he'
          · intro e' he'
            have htk : e' ∈ delSup.take (i + 1) ↔ e' ∈ delSup.take i ∨ e' = e := by
              rw [List.take_succ_eq_append_getElem hi, List.mem_append, List.mem_singleton]
            by_cases hee : e' = e
            · subst hee; rw [hse e heCap]; simp [heOut]
            · simp only [htk, hee, or_false]; exact hse e' he'
      · have heNotOut : e ∉ outDelS := fun h => hO ((hDel_iff e he_mem).mp h).1
        refine ⟨.normal, ⟨st.mem, rB, st.pos⟩, _,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, h17,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h18,
              runs_cond_iff.mpr ⟨0, 1, Expr.eval_reg_of_eq (by simp [rB, hO]),
                by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩, rfl⟩), rfl⟩),
          ⟨⟨by simp [rB, rA, r0], by simp [rB, rA, r1'], by simp [rB, rA, r2'], by simp [rB, rA, r3'],
            by simp [rB, rA, r4], by simp [rB, rA, r5], by simp [rB, rA, r6], by simp [rB, rA, r7],
            by simp [rB, rA, r8], by simp [rB, rA, r9], by simp [rB, rA, r10], by simp [rB, rA, r12],
            by simp [rB, rA, r13], by simp [rB, rA, r14], by simp [rB, rA, r15], by simp,
            ?_, ?_, hz2, hfr⟩, by simp [rB, rA, r16]⟩,
          by show _ ≤ 100; simp only [Expr.size]; omega⟩
        · intro e' he'
          have htk : e' ∈ delSup.take (i + 1) ↔ e' ∈ delSup.take i ∨ e' = e := by
            rw [List.take_succ_eq_append_getElem hi, List.mem_append, List.mem_singleton]
          by_cases hee : e' = e
          · subst hee; rw [hsd e heCap]; simp [heNotOut]
          · simp only [htk, hee, or_false]; exact hsd e' he'
        · intro e' he'
          have htk : e' ∈ delSup.take (i + 1) ↔ e' ∈ delSup.take i ∨ e' = e := by
            rw [List.take_succ_eq_append_getElem hi, List.mem_append, List.mem_singleton]
          by_cases hee : e' = e
          · subst hee; rw [hse e heCap]; simp [heNotOut]
          · simp only [htk, hee, or_false]; exact hse e' he' )
  obtain ⟨oD, st1, cD, hrD, hpostD, hcD⟩ := hDloop ⟨mem₀, r3, pos⟩ ω
    ⟨by simp [r3, r2, r1, s0, startState], by simp [r3, r2, r1, s0, startState],
     by simp [r3, r2, r1, s0, startState], by simp [r3, r2, r1, s0, startState],
     by simp [r3, r2, r1, s0, startState], by simp [r3, r2, r1, s0, startState],
     by simp [r3, r2, r1, s0, startState], by simp [r3, r2, r1, s0, startState],
     by simp [r3, r2, r1, s0, startState], by simp [r3, r2, r1, s0, startState],
     by simp [r3, r2, r1, s0, startState], by simp [r3, r2, r1, s0, startState],
     by simp [r3, r2, r1], by simp [r3, r2], by simp [r3], by simp,
     fun e he => by simp [hz (h + e) (by omega)],
     fun e he => by simp [hz (h + eCap + e) (by omega)],
     fun a ha => hz a (by omega), fun _ _ => rfl⟩
  cases oD with
  | returned _ => cases hpostD
  | normal =>
  obtain ⟨r0_1, _, r2_1, r3_1, r4_1, r5_1, r6_1, r7_1, r8_1, r9_1, r10_1, _, _, r14_1, r15_1, _,
      hsd1, hse1, hz2_1, hfr1⟩ := hpostD
  rw [List.take_length] at hsd1 hse1
  -- Loop 2: insSup
  let iInv : ℕ → State → Prop := fun i st =>
    st.regs 2 = insSupPtr ∧ st.regs 3 = insSup.length ∧
    st.regs 4 = outEPres ∧ st.regs 5 = lastOpPtr ∧ st.regs 6 = inDelBPtr ∧ st.regs 7 = inFDelPtr ∧
    st.regs 8 = inDtotPtr ∧ st.regs 9 = inActPtr ∧ st.regs 10 = inTgtPtr ∧
    st.regs 14 = h + 2 * eCap ∧ st.regs 15 = h + 3 * eCap ∧ st.regs 16 = i ∧
    (∀ e < eCap, st.mem (h + 2 * eCap + e) = if e ∈ insSup.take i ∧ e ∈ outInsS then 1 else 0) ∧
    (∀ a, a < h + 2 * eCap ∨ h + 3 * eCap ≤ a → st.mem a = st1.mem a)
  have hIloop := Triple.forRange_le (w := w) (p := p) (r := 16) (lo := .const 0) (hi := .reg 3)
    (body := asmFirstMarkInsBody fEvalTgt)
    (P := fun st => iInv 0 { st with regs := Function.update st.regs 16 0 })
    (Inv := iInv) (fun _ => 100) 0 insSup.length (Nat.zero_le _) h1w (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const h0w, hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.1)
    (fun i _ hi st ω' ⟨r2', r3', r4, r5, r6, r7, r8, r9, r10, r14, r15, r16, hsi, hfrI⟩ => by
      set e := insSup[i]'hi
      have he_mem : e ∈ insSup := List.getElem_mem hi
      have heCap : e < eCap := hIS_cap e he_mem
      have hpre : ∀ a < h, st.mem a = mem₀ a := fun a ha =>
        (hfrI a (Or.inl (by omega))).trans (hfr1 a ha)
      have hme : st.mem (insSupPtr + i) = e := (hpre _ (by omega)).trans (hIS i hi)
      have hmOld : st.mem (outEPres + e) = if e ∈ inOldS then 1 else 0 := (hpre _ (by omega)).trans (hOld e heCap)
      have hmLO : st.mem (lastOpPtr + e) = lastOp e := (hpre _ (by omega)).trans (hLO e heCap)
      have hmDB : st.mem (inDelBPtr + e) = if e ∈ inDelB then 1 else 0 := (hpre _ (by omega)).trans (hDB e heCap)
      have hmFD : st.mem (inFDelPtr + e) = if e ∈ inFDel then 1 else 0 := (hpre _ (by omega)).trans (hFD e heCap)
      have hmDT : st.mem (inDtotPtr + e) = if e ∈ inDtot then 1 else 0 := (hpre _ (by omega)).trans (hDT e heCap)
      have hmAct : st.mem (inActPtr + e) = if e ∈ inAct then 1 else 0 := (hpre _ (by omega)).trans (hAct e heCap)
      have hmTgt : st.mem (inTgtPtr + e) = if e ∈ inTgt then 1 else 0 := (hpre _ (by omega)).trans (hTgt e heCap)
      set rA := Function.update st.regs 17 e
      have h17 : Runs w p ω' (.assign 17 (.load (.bin .add (.reg 2) (.reg 16)))) st .normal ⟨st.mem, rA, st.pos⟩ 5 :=
        runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq r2') (Expr.eval_reg_of_eq r16) (by omega)) hme, rfl, rfl, rfl⟩
      obtain ⟨stE, cE, hrE, hmemE, hcE⟩ := asmFirstEvalTgtE_runs (p := p) (ω := ω') (pos := st.pos)
        hw16 heCap hmOld hmLO hmFD hmAct hmTgt (by omega) (by omega) (by omega) (by omega) (by omega)
      set tval := if tgtEDec inOldS inFDel inAct inTgt lastOp e then 1 else 0
      set rB := Function.update rA 19 tval
      have heArgs : evalArgs w ⟨st.mem, rA, st.pos⟩ [.reg 4, .reg 5, .reg 7, .reg 9, .reg 10, .reg 17] =
          some [outEPres, lastOpPtr, inFDelPtr, inActPtr, inTgtPtr, e] :=
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, r4])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, r5])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, r7])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, r9])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, r10])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA])) <| evalArgs_nil _ _
      have hcall : Runs w p ω' (.call 19 fEvalTgt [.reg 4, .reg 5, .reg 7, .reg 9, .reg 10, .reg 17])
          ⟨st.mem, rA, st.pos⟩ .normal ⟨st.mem, rB, stE.pos⟩
          (argsSize [.reg 4, .reg 5, .reg 7, .reg 9, .reg 10, .reg 17] + cE + 1) := by
        have h0 : Runs w p ω' (.call 19 fEvalTgt [.reg 4, .reg 5, .reg 7, .reg 9, .reg 10, .reg 17])
            ⟨st.mem, rA, st.pos⟩ .normal ⟨stE.mem, rB, stE.pos⟩
            (argsSize [.reg 4, .reg 5, .reg 7, .reg 9, .reg 10, .reg 17] + cE + 1) :=
          runs_call_iff.mpr ⟨_, asmFirstEvalTgtEStmt, .returned tval, stE, cE, heArgs, hfEval, hrE, rfl, rfl, rfl⟩
        rwa [hmemE] at h0
      by_cases hT : tgtEDec inOldS inFDel inAct inTgt lastOp e
      · have ht1 : tval = 1 := by simp [tval, hT]
        set rC := Function.update rB 18 (if e ∈ inOldS then 1 else 0)
        set rD := Function.update rC 20 (if e ∈ inDelB then 1 else 0)
        set rE := Function.update rD 21 (if e ∈ inDtot then 1 else 0)
        have h18 : Runs w p ω' (.assign 18 (.load (.bin .add (.reg 4) (.reg 17))))
            ⟨st.mem, rB, stE.pos⟩ .normal ⟨st.mem, rC, stE.pos⟩ 5 :=
          runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, r4]))
              (Expr.eval_reg_of_eq (by simp [rB, rA])) (by omega)) hmOld, rfl, rfl, rfl⟩
        have h20 : Runs w p ω' (.assign 20 (.load (.bin .add (.reg 6) (.reg 17))))
            ⟨st.mem, rC, stE.pos⟩ .normal ⟨st.mem, rD, stE.pos⟩ 5 :=
          runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rC, rB, rA, r6]))
              (Expr.eval_reg_of_eq (by simp [rC, rB, rA])) (by omega)) hmDB, rfl, rfl, rfl⟩
        have h21 : Runs w p ω' (.assign 21 (.load (.bin .add (.reg 8) (.reg 17))))
            ⟨st.mem, rD, stE.pos⟩ .normal ⟨st.mem, rE, stE.pos⟩ 5 :=
          runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rD, rC, rB, rA, r8]))
              (Expr.eval_reg_of_eq (by simp [rD, rC, rB, rA])) (by omega)) hmDT, rfl, rfl, rfl⟩
        set condV := (if (if e ∈ inOldS then 1 else 0) = 0 then 1 else 0) +
          (if e ∈ inDelB then 1 else 0) + (if e ∈ inDtot then 1 else 0)
        have hcondE : (Expr.bin .add (.bin .add (.bin .eq (.reg 18) (.const 0)) (.reg 20)) (.reg 21)).eval w
            ⟨st.mem, rE, stE.pos⟩ = some condV := by
          have hr18 : rE 18 = if e ∈ inOldS then 1 else 0 := by simp [rE, rD, rC]
          have he18 : (Expr.bin .eq (.reg 18) (.const 0)).eval w ⟨st.mem, rE, stE.pos⟩ =
              some (if (if e ∈ inOldS then 1 else 0) = 0 then 1 else 0) := by
            by_cases hO : e ∈ inOldS <;> simp [Expr.eval, hr18, hO, BinOp.eval, h0w, h1w]
          have hr20 : rE 20 = if e ∈ inDelB then 1 else 0 := by simp [rE, rD]
          have hr21 : rE 21 = if e ∈ inDtot then 1 else 0 := by simp [rE]
          have h12' : (Expr.bin .add (.bin .eq (.reg 18) (.const 0)) (.reg 20)).eval w ⟨st.mem, rE, stE.pos⟩ =
              some ((if (if e ∈ inOldS then 1 else 0) = 0 then 1 else 0) + (if e ∈ inDelB then 1 else 0)) :=
            Expr.eval_add he18 (Expr.eval_reg_of_eq hr20) (by split_ifs <;> omega)
          exact Expr.eval_add h12' (Expr.eval_reg_of_eq hr21) (by split_ifs <;> omega)
        have hcond_iff : condV ≠ 0 ↔ e ∈ outInsS := by
          rw [hIns_iff e he_mem]; simp only [hT, true_and, condV]; split_ifs <;> simp_all
        by_cases heIn : e ∈ outInsS
        · have hcv_ne : condV ≠ 0 := hcond_iff.mpr heIn
          set m1 := Function.update st.mem (h + 2 * eCap + e) 1
          have hst1 : Runs w p ω' (.store (.bin .add (.reg 14) (.reg 17)) (.const 1))
              ⟨st.mem, rE, stE.pos⟩ .normal ⟨m1, rE, stE.pos⟩ 5 :=
            runs_store_iff.mpr ⟨h + 2 * eCap + e, 1,
              Expr.eval_add (Expr.eval_reg_of_eq (by simp [rE, rD, rC, rB, rA, r14]))
                (Expr.eval_reg_of_eq (by simp [rE, rD, rC, rB, rA])) (by omega),
              Expr.eval_const h1w, rfl, rfl, rfl⟩
          refine ⟨.normal, ⟨m1, rE, stE.pos⟩, _,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h17,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcall,
                runs_cond_iff.mpr ⟨1, _, Expr.eval_reg_of_eq (by simp [rB, ht1]), by
                  simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, h18,
                    runs_seq_iff.mpr (Or.inr ⟨_, _, _, h20,
                      runs_seq_iff.mpr (Or.inr ⟨_, _, _, h21,
                        runs_cond_iff.mpr ⟨condV, _, hcondE, by simpa [hcv_ne] using hst1, rfl⟩,
                        rfl⟩), rfl⟩), rfl⟩), rfl⟩, rfl⟩), rfl⟩),
            ⟨⟨by simp [rE, rD, rC, rB, rA, r2'], by simp [rE, rD, rC, rB, rA, r3'],
              by simp [rE, rD, rC, rB, rA, r4], by simp [rE, rD, rC, rB, rA, r5],
              by simp [rE, rD, rC, rB, rA, r6], by simp [rE, rD, rC, rB, rA, r7],
              by simp [rE, rD, rC, rB, rA, r8], by simp [rE, rD, rC, rB, rA, r9],
              by simp [rE, rD, rC, rB, rA, r10], by simp [rE, rD, rC, rB, rA, r14],
              by simp [rE, rD, rC, rB, rA, r15], by simp, ?_, ?_⟩,
             by simp [rE, rD, rC, rB, rA, r16]⟩,
            by show _ ≤ 100; simp only [argsSize, Expr.size]; omega⟩
          · intro e' he'
            change m1 (h + 2 * eCap + e') = if e' ∈ insSup.take (i + 1) ∧ e' ∈ outInsS then 1 else 0
            have htk : e' ∈ insSup.take (i + 1) ↔ e' ∈ insSup.take i ∨ e' = e := by
              rw [List.take_succ_eq_append_getElem hi, List.mem_append, List.mem_singleton]
            by_cases hee : e' = e
            · subst hee; simp [m1, htk, heIn]
            · simp only [htk, hee, or_false, m1, Function.update_of_ne (by omega : h + 2 * eCap + e' ≠ h + 2 * eCap + e)]
              exact hsi e' he'
          · intro a ha; dsimp only [m1]
            rw [Function.update_of_ne (show a ≠ h + 2 * eCap + e by rcases ha with h1 | h2 <;> omega)]
            exact hfrI a ha
        · have hcv0 : condV = 0 := Classical.not_not.mp fun hne => heIn (hcond_iff.mp hne)
          refine ⟨.normal, ⟨st.mem, rE, stE.pos⟩, _,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h17,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcall,
                runs_cond_iff.mpr ⟨1, _, Expr.eval_reg_of_eq (by simp [rB, ht1]), by
                  simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, h18,
                    runs_seq_iff.mpr (Or.inr ⟨_, _, _, h20,
                      runs_seq_iff.mpr (Or.inr ⟨_, _, _, h21,
                        runs_cond_iff.mpr ⟨0, 1, by simpa [hcv0] using hcondE,
                          by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
                        rfl⟩), rfl⟩), rfl⟩), rfl⟩, rfl⟩), rfl⟩),
            ⟨⟨by simp [rE, rD, rC, rB, rA, r2'], by simp [rE, rD, rC, rB, rA, r3'],
              by simp [rE, rD, rC, rB, rA, r4], by simp [rE, rD, rC, rB, rA, r5],
              by simp [rE, rD, rC, rB, rA, r6], by simp [rE, rD, rC, rB, rA, r7],
              by simp [rE, rD, rC, rB, rA, r8], by simp [rE, rD, rC, rB, rA, r9],
              by simp [rE, rD, rC, rB, rA, r10], by simp [rE, rD, rC, rB, rA, r14],
              by simp [rE, rD, rC, rB, rA, r15], by simp, ?_, hfrI⟩,
             by simp [rE, rD, rC, rB, rA, r16]⟩,
            by show _ ≤ 100; simp only [argsSize, Expr.size]; omega⟩
          intro e' he'
          have htk : e' ∈ insSup.take (i + 1) ↔ e' ∈ insSup.take i ∨ e' = e := by
            rw [List.take_succ_eq_append_getElem hi, List.mem_append, List.mem_singleton]
          by_cases hee : e' = e
          · subst hee; rw [hsi e heCap]; simp [heIn]
          · simp only [htk, hee, or_false]; exact hsi e' he'
      · have ht0 : tval = 0 := by simp [tval, hT]
        have heNotIn : e ∉ outInsS := fun h => hT ((hIns_iff e he_mem).mp h).1
        refine ⟨.normal, ⟨st.mem, rB, stE.pos⟩, _,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, h17,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcall,
              runs_cond_iff.mpr ⟨0, 1, Expr.eval_reg_of_eq (by simp [rB, ht0]),
                by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩, rfl⟩), rfl⟩),
          ⟨⟨by simp [rB, rA, r2'], by simp [rB, rA, r3'], by simp [rB, rA, r4], by simp [rB, rA, r5],
            by simp [rB, rA, r6], by simp [rB, rA, r7], by simp [rB, rA, r8], by simp [rB, rA, r9],
            by simp [rB, rA, r10], by simp [rB, rA, r14], by simp [rB, rA, r15], by simp,
            ?_, hfrI⟩, by simp [rB, rA, r16]⟩,
          by show _ ≤ 100; simp only [argsSize, Expr.size]; omega⟩
        intro e' he'
        have htk : e' ∈ insSup.take (i + 1) ↔ e' ∈ insSup.take i ∨ e' = e := by
          rw [List.take_succ_eq_append_getElem hi, List.mem_append, List.mem_singleton]
        by_cases hee : e' = e
        · subst hee; rw [hsi e heCap]; simp [heNotIn]
        · simp only [htk, hee, or_false]; exact hsi e' he')
  obtain ⟨oI, st2, cI, hrI, hpostI, hcI⟩ := hIloop st1 ω
    ⟨r2_1, r3_1, r4_1, r5_1, r6_1, r7_1, r8_1, r9_1, r10_1, r14_1, r15_1, by simp,
     fun e he => by simp [hz2_1 (h + 2 * eCap + e) (by omega)], fun _ _ => rfl⟩
  cases oI with
  | returned _ => cases hpostI
  | normal =>
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hr15_2, -, hsi2, hfr2⟩ := hpostI
  rw [List.take_length] at hsi2
  have hret : Runs w p ω (.ret (.reg 15)) st2 (.returned (h + 3 * eCap)) st2 2 :=
    runs_ret_iff.mpr ⟨h + 3 * eCap, Expr.eval_reg_of_eq hr15_2, rfl, rfl, rfl⟩
  have hrcD : rangeCost (fun _ => 100) 0 delSup.length = 100 * delSup.length := by
    simp [rangeCost, Nat.mul_comm]
  have hrcI : rangeCost (fun _ => 100) 0 insSup.length = 100 * insSup.length := by
    simp [rangeCost, Nat.mul_comm]
  dsimp only at hcD hcI; simp only [hrcD, hrcI, Nat.sub_zero, Expr.size] at hcD hcI
  refine ⟨st2, _,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha13,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha14,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha15,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrD,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrI, hret, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    ?_, ?_, ?_, ?_, ?_, by omega⟩
  · intro e he
    rw [hfr2 (h + e) (Or.inl (by omega)), hsd1 e he]
    by_cases h1 : e ∈ outDelS
    · simp [h1, hDS_cov e h1]
    · simp [h1]
  · intro e he
    rw [hfr2 (h + eCap + e) (Or.inl (by omega)), hse1 e he]
    by_cases h1 : e ∈ E' ∩ outDelS
    · simp [h1, hDS_cov e (Finset.mem_inter.mp h1).2]
    · simp [h1]
  · intro e he
    rw [hsi2 e he]
    by_cases h1 : e ∈ outInsS
    · simp [h1, hIS_cov e h1]
    · simp [h1]
  · intro a ha
    rw [hfr2 a (Or.inr ha)]; exact hz2_1 a (by omega)
  · intro a ha
    rw [hfr2 a (Or.inl (by omega))]; exact hfr1 a ha

end

end MinCostFlow.SparseCore.Program
