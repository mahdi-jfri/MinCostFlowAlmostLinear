module

public import MinCostFlow.MinRatio.WireChainCoreSelOutSlotKFBL
import WordRAM.Tactic

/-!
# The slot call at the end of a Branch B level step (`WireChainCoreBranchBSlotCallKFBL`)

A Branch B level step ends with the call of the slot writer `wireSelOutSlotBody`
(`WireChainCoreSelOutSlotKFBL.lean`) on the slot of the level, `selOutBase + 1 + 12 idx`, with the
places of the copies that the step made earlier (`fDel` and re-embedding lists in `regs 26..29`,
the descriptor and the table width in `regs 31, 32`), the level batch (`regs 23, 24`) and the
forwarded batch (`reg 10`). This file gives that statement, `wireBranchBSlotStmt`, and its run
lemma `wireBranchBSlotStmt_runs`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Chain MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

/-- Call the slot writer at `slotProc` on the slot `reg 72 + 1 + 12 * reg 96`, with the heap
pointer `reg 4`; the returned free word goes to `reg 4`. -/
@[expose] def wireBranchBSlotStmt (slotProc : ℕ) : Stmt :=
  .assign 33 (.bin .add (.bin .add (.reg 72) (.const 1)) (.bin .mul (.const 12) (.reg 96))) ;;
  .call 4 slotProc [.reg 33, .reg 4, .reg 26, .reg 27, .reg 28, .reg 29, .reg 31, .reg 32,
    .reg 23, .reg 24, .reg 10]

theorem wireBranchBSlotStmt_noRand (slotProc : ℕ) : (wireBranchBSlotStmt slotProc).NoRand := by
  simp [wireBranchBSlotStmt, Stmt.NoRand]

set_option maxHeartbeats 800000 in
/-- One run of `wireBranchBSlotStmt`, with the slot writer at `slotProc` and the collector at
`collectProc`. It leaves `SelOutSlotPost` at the slot of the level and moves `reg 4` past the two
touched-edge lists. -/
theorem wireBranchBSlotStmt_runs {w slotProc collectProc selBase idx hp fDelPtr fDelLen reembPtr
      reembLen descPtr Lw uPtr uWords nextPtr nextWords : ℕ}
    {p : Program} {ω : ℕ → Bool} {s : State} {G GS : MGraph} {U US : List Update}
    (hw : 12 < 2 ^ w)
    (hSlotP : p.procs[slotProc]? = some (wireSelOutSlotBody collectProc))
    (hColl : p.procs[collectProc]? = some wireCollectTouchedEdgesBody)
    (hRegs : s.regs 72 = selBase ∧ s.regs 96 = idx ∧ s.regs 4 = hp ∧ s.regs 26 = fDelPtr ∧
      s.regs 27 = fDelLen ∧ s.regs 28 = reembPtr ∧ s.regs 29 = reembLen ∧
      s.regs 31 = descPtr ∧ s.regs 32 = Lw ∧ s.regs 23 = uPtr ∧ s.regs 24 = uWords ∧
      s.regs 10 = nextPtr)
    (hU : SmallBatchAt s.mem uPtr G U uWords) (hUW : ∀ t < uWords, s.mem (uPtr + t) < 2 ^ w)
    (hULe : uPtr + uWords ≤ hp)
    (hUS : SmallBatchAt s.mem nextPtr GS US nextWords)
    (hUSW : ∀ t < nextWords, s.mem (nextPtr + t) < 2 ^ w) (hUSLe : nextPtr + nextWords ≤ hp)
    (hSlot : selBase + 1 + 12 * idx + 12 ≤ hp) (hz : ZeroFrom s.mem hp)
    (hRoom : hp + U.length + US.length < 2 ^ w) :
    ∃ (out : State) (cost : ℕ),
      Runs w p ω (wireBranchBSlotStmt slotProc) s .normal out cost ∧
      out.regs 4 = hp + (coreBatchTouchedEdges U).length + (coreBatchTouchedEdges US).length ∧
      (∀ r, r ≠ 4 → r ≠ 33 → out.regs r = s.regs r) ∧
      SelOutSlotPost s.mem out.mem (selBase + 1 + 12 * idx) hp fDelPtr fDelLen reembPtr reembLen
        descPtr Lw uPtr uWords (coreBatchTouchedEdges U) (coreBatchTouchedEdges US) ∧
      cost ≤ 60 * (U.length + US.length) + 340 := by
  obtain ⟨h72, h96, h4, h26, h27, h28, h29, h31, h32, h23, h24, h10⟩ := hRegs
  generalize hsl : selBase + 1 + 12 * idx = sl at hSlot ⊢
  have hTLU := coreBatchTouchedEdges_length_le U
  have hTLS := coreBatchTouchedEdges_length_le US
  obtain ⟨o1, cost1, hrun1, hc1, hpost1⟩ :=
    wireSelOutSlotBody_runs (w := w) (slot := sl) (hp := hp) (fDelPtr := fDelPtr)
      (fDelLen := fDelLen) (reembPtr := reembPtr) (reembLen := reembLen) (descPtr := descPtr)
      (Lw := Lw) (pos := s.pos) (p := p) (ω := ω) (by omega) hColl hU hUW hULe hUS hUSW hUSLe
      (by omega) hz hRoom
  let s1 : State := { s with regs := Function.update s.regs 33 sl }
  have r1 : Runs w p ω (.assign 33 (.bin .add (.bin .add (.reg 72) (.const 1))
      (.bin .mul (.const 12) (.reg 96)))) s .normal s1 8 :=
    runs_assign_iff.mpr ⟨sl, by
      simp only [Expr.eval, BinOp.eval, h72, h96]
      simp [show 1 < 2 ^ w by omega, show 12 < 2 ^ w by omega, show 12 * idx < 2 ^ w by omega,
        show selBase + 1 < 2 ^ w by omega, show sl < 2 ^ w by omega, hsl],
      rfl, rfl, by simp [Expr.size]⟩
  have hargs : evalArgs w s1 [.reg 33, .reg 4, .reg 26, .reg 27, .reg 28, .reg 29, .reg 31,
      .reg 32, .reg 23, .reg 24, .reg 10] =
      some [sl, hp, fDelPtr, fDelLen, reembPtr, reembLen, descPtr, Lw, uPtr, uWords, nextPtr] := by
    simp [evalArgs, Expr.eval, s1, h4, h26, h27, h28, h29, h31, h32, h23, h24, h10]
  let ret := hp + (coreBatchTouchedEdges U).length + (coreBatchTouchedEdges US).length
  let s2 : State := { o1 with regs := Function.update s1.regs 4 ret }
  have r2 : Runs w p ω (.call 4 slotProc [.reg 33, .reg 4, .reg 26, .reg 27, .reg 28, .reg 29,
      .reg 31, .reg 32, .reg 23, .reg 24, .reg 10]) s1 .normal s2 (11 + cost1 + 1) :=
    runs_call_iff.mpr ⟨_, _, _, o1, cost1, hargs, hSlotP, hrun1, rfl, rfl, by
      simp [argsSize, Expr.size]⟩
  refine ⟨s2, _, runs_seq_iff.mpr (Or.inr ⟨s1, 8, _, r1, r2, rfl⟩), by simp [s2, ret], fun r h4' h33 => ?_,
    hpost1, by omega⟩
  simp [s2, s1, Function.update_of_ne h4', Function.update_of_ne h33]

end MinCostFlow.MinRatio
