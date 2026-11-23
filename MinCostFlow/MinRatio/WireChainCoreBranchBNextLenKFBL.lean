module

public import MinCostFlow.MinRatio.WireChainCoreLens
import WordRAM.Tactic

/-!
# The length update of the next level in a Branch B level step (`WireChainCoreBranchBNextLenKFBL`)

After op `2` and the descriptor copy (`wireBranchBReadDescStmt`), a level `idx < d - 1` that
`Update` does not rebuild writes the lengths of the next level: for each edge that the forwarded
batch inserts, its length is the core length of the new forest (`coreLen`), computed from the
stretch tables (`wireUpdateCoreLenFromBatchBody`, `WireChainCoreLens.lean`). This file gives that
part, `wireBranchBNextLenStmt`, with the new descriptor (`reg 31`) and the table width (`reg 32`),
and its two run lemmas: `wireBranchBNextLenStmt_runs_lt` for `idx + 1 < d`, and
`wireBranchBNextLenStmt_runs_ge` for the last level, where the statement does nothing.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program

/-- When `reg 96 + 1 < reg 75`, load the length vector of the next level from the level meta table
(`reg 83`) and write the core lengths of the edges that the forwarded batch at `reg 10` inserts,
from the stretch descriptor `reg 31` of width `reg 32`, with the heap pointer `reg 4`. -/
@[expose] def wireBranchBNextLenStmt (updLen : ℕ) : Stmt :=
  .cond (.bin .lt (.bin .add (.reg 96) (.const 1)) (.reg 75))
    (.assign 20 (.load (.bin .add (.reg 83) (.bin .add (.reg 96) (.const 1)))) ;;
     .call 4 updLen [.reg 10, .reg 31, .reg 7, .reg 20, .reg 94, .reg 32, .reg 4])
    .nop

theorem wireBranchBNextLenStmt_noRand (updLen : ℕ) : (wireBranchBNextLenStmt updLen).NoRand := by
  simp [wireBranchBNextLenStmt, Stmt.NoRand]

/-- At the last level (`idx + 1 = d`), `wireBranchBNextLenStmt` does nothing. -/
theorem wireBranchBNextLenStmt_runs_ge {w updLen idx d : ℕ} {p : Program} {ω : ℕ → Bool}
    {s : State} (hw : 1 < 2 ^ w) (h96 : s.regs 96 = idx) (h75 : s.regs 75 = d)
    (hge : d ≤ idx + 1) (hW : idx + 1 < 2 ^ w) :
    ∃ c, Runs w p ω (wireBranchBNextLenStmt updLen) s .normal s c ∧ c ≤ 10 := by
  refine ⟨_, runs_cond_iff.mpr ⟨0, 1, ?_, ?_, rfl⟩, by simp [Expr.size]⟩
  · simp [Expr.eval, BinOp.eval, h96, h75, show ¬ idx + 1 < d by omega, hW, hw]
  · simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 800000 in
/-- At a level with `idx + 1 < d`, `wireBranchBNextLenStmt` runs `wireUpdateCoreLenFromBatchBody`
on the forwarded batch, the new descriptor and the length vectors of the two levels. It gives the
core lengths at the next level, changes no word below `heap` outside that vector, and costs at most
a constant per batch entry. -/
theorem wireBranchBNextLenStmt_runs_lt
    {w updLen edgeProc signExt mul intDiv copy idx d levelMeta batchPtr stretchDesc prevLenPtr
      curLenPtr L Lw P ecPrev ecCur totalWords heap : ℕ}
    {p : Program} {ω : ℕ → Bool} {s : State} {G : MGraph} {U : List Update}
    {forest : LSF} {prevℓ oldCurℓ : ℕ → ℝ} {prevE : Finset ℕ}
    (hUpdLen : p.procs[updLen]? = some (wireUpdateCoreLenFromBatchBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hRegs : s.regs 96 = idx ∧ s.regs 75 = d ∧ s.regs 83 = levelMeta ∧ s.regs 10 = batchPtr ∧
      s.regs 31 = stretchDesc ∧ s.regs 7 = prevLenPtr ∧ s.regs 94 = L ∧ s.regs 32 = Lw ∧
      s.regs 4 = heap)
    (hlt : idx + 1 < d) (hMetaW : levelMeta + (idx + 1) < 2 ^ w)
    (hCell : s.mem (levelMeta + (idx + 1)) = curLenPtr)
    (hSmall : SmallBatchAt s.mem batchPtr G U totalWords)
    (hBatchW : ∀ j < totalWords, s.mem (batchPtr + j) < 2 ^ w)
    (hStretch : StretchValuesAt s.mem stretchDesc 4 Lw P prevE forest.wstr)
    (hPrevLen : EdgeValuesAt s.mem prevLenPtr 4 L P prevE prevℓ)
    (hCurLen : EdgeValuesAt s.mem curLenPtr 4 L P G.E oldCurℓ)
    (hGE : ∀ e ∈ G.E, e < ecCur)
    (hInsInfo : ∀ u ∈ U, match u with
      | .insert e _ _ => e ∈ prevE ∧ e < ecPrev ∧ e < ecCur ∧
          (∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P = coreLen forest prevℓ e)
      | _ => True)
    (hAgreeOld : ∀ e ∈ (G.applyBatch U).E, (¬ ∃ u ∈ U, u.Inserts e) →
      e ∈ G.E ∧ oldCurℓ e = coreLen forest prevℓ e)
    (hMemIns : ∀ e ∈ (G.applyBatch U).E, (∃ u ∈ U, u.Inserts e) →
      ∃ k, ∃ hk : k < U.length, U[k].Inserts e)
    (hBatchLe : batchPtr + totalWords ≤ heap)
    (hStretchLe : stretchDesc + 2 ≤ heap)
    (hNumDenLe : ∀ e ∈ prevE, s.mem stretchDesc + e * Lw + Lw ≤ heap ∧
      s.mem (stretchDesc + 1) + e * Lw + Lw ≤ heap)
    (hPrevLe : prevLenPtr + ecPrev * L ≤ heap)
    (hCurLe : curLenPtr + ecCur * L ≤ heap)
    (hDisjBatch : batchPtr + totalWords ≤ curLenPtr ∨ curLenPtr + ecCur * L ≤ batchPtr)
    (hDisjPrev : prevLenPtr + ecPrev * L ≤ curLenPtr ∨ curLenPtr + ecCur * L ≤ prevLenPtr)
    (hDisjNum : ∀ e ∈ prevE, ∀ k < Lw, s.mem stretchDesc + e * Lw + k < curLenPtr ∨
      curLenPtr + ecCur * L ≤ s.mem stretchDesc + e * Lw + k)
    (hDisjDen : ∀ e ∈ prevE, ∀ k < Lw, s.mem (stretchDesc + 1) + e * Lw + k < curLenPtr ∨
      curLenPtr + ecCur * L ≤ s.mem (stretchDesc + 1) + e * Lw + k)
    (hz : ZeroFrom s.mem heap)
    (hRoom : heap + U.length * wireCoreLenEdgeSpace (max L Lw) < 2 ^ w)
    (hw5 : 5 < 2 ^ w) :
    ∃ (out : State) (cost : ℕ),
      Runs w p ω (wireBranchBNextLenStmt updLen) s .normal out cost ∧
      heap ≤ out.regs 4 ∧ out.regs 4 ≤ heap + U.length * wireCoreLenEdgeSpace (max L Lw) ∧
      (∀ r, r ≠ 4 → r ≠ 20 → out.regs r = s.regs r) ∧
      EdgeValuesAt out.mem curLenPtr 4 L P (G.applyBatch U).E (coreLen forest prevℓ) ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ a < heap, (a < curLenPtr ∨ curLenPtr + ecCur * L ≤ a) → out.mem a = s.mem a) ∧
      cost ≤ U.length * (wireCoreLenEdgeCost (max L Lw) + 60) + 90 := by
  obtain ⟨h96, h75, h83, h10, h31, h7, h94, h32, h4⟩ := hRegs
  obtain ⟨nextHeap, o1, c1, hrun1, hlo1, hhi1, hc1, hlen1, hz1, hfr1⟩ :=
    wireUpdateCoreLenFromBatchBody_runs (pos := s.pos) (ω := ω) hEdgeProc hSign hMul hDiv hCopy
      hSmall hBatchW hStretch hPrevLen hCurLen hGE hInsInfo hAgreeOld hMemIns hBatchLe hStretchLe
      hNumDenLe hPrevLe hCurLe hDisjBatch hDisjPrev hDisjNum hDisjDen hz hRoom hw5
  let s1 : State := { s with regs := Function.update s.regs 20 curLenPtr }
  have r1 : Runs w p ω (.assign 20 (.load (.bin .add (.reg 83) (.bin .add (.reg 96) (.const 1)))))
      s .normal s1 7 :=
    runs_assign_iff.mpr ⟨curLenPtr, by
      simp [Expr.eval, BinOp.eval, h83, h96, show 1 < 2 ^ w by omega,
        show idx + 1 < 2 ^ w by omega, hMetaW, hCell], rfl, rfl, by simp [Expr.size]⟩
  have hargs : evalArgs w s1 [.reg 10, .reg 31, .reg 7, .reg 20, .reg 94, .reg 32, .reg 4] =
      some [batchPtr, stretchDesc, prevLenPtr, curLenPtr, L, Lw, heap] := by
    simp [evalArgs, Expr.eval, s1, h10, h31, h7, h94, h32, h4]
  let s2 : State := { o1 with regs := Function.update s1.regs 4 nextHeap }
  have r2 : Runs w p ω (.call 4 updLen [.reg 10, .reg 31, .reg 7, .reg 20, .reg 94, .reg 32,
      .reg 4]) s1 .normal s2 (7 + c1 + 1) :=
    runs_call_iff.mpr ⟨_, _, _, o1, c1, hargs, hUpdLen, hrun1, rfl, rfl, by
      simp [argsSize, Expr.size]⟩
  have r12 := runs_seq_iff.mpr (Or.inr ⟨s1, 7, _, r1, r2, rfl⟩)
  have h24 : s2.regs 4 = nextHeap := by simp [s2]
  refine ⟨s2, _, runs_cond_iff.mpr ⟨1, 7 + (7 + c1 + 1) + 1, ?_, ?_, rfl⟩, h24 ▸ hlo1, h24 ▸ hhi1,
    fun r h4' h20 => ?_, hlen1, h24 ▸ hz1, hfr1, ?_⟩
  · simp [Expr.eval, BinOp.eval, h96, h75, hlt, show 1 < 2 ^ w by omega,
      show idx + 1 < 2 ^ w by omega]
  · simpa using r12
  · simp [s2, s1, Function.update_of_ne h4', Function.update_of_ne h20]
  · simp only [Expr.size]; omega

end MinCostFlow.MinRatio
