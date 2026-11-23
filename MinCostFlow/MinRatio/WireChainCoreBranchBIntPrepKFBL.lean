module

public import MinCostFlow.MinRatio.WireCoreReadKFBL
public import MinCostFlow.MinRatio.WireChainCoreOps
import WordRAM.Tactic

/-!
# The first part of the interior rebuild step under `KFBL` (`WireChainCoreBranchBIntPrepKFBL`)

When the batch of level `idx` (with `0 < idx < d`) would push its update counter over the rebuild
threshold, Branch B of the chain-update core rebuilds the levels `idx, …, d` from scratch. Before
the rebuild it needs three things: the graph of level `idx` with the batch applied, the order list
of level `idx - 1` (the input order of the new level `idx`), and the rebuild counter of level `idx`
increased by one. This file gives that part of the interior step, `wireBranchBIntPrepKFBL`, and its
run lemma `wireBranchBIntPrepKFBL_runs`. It is the first part of
`wireBranchBInteriorRebuildStep` (`WireChainCoreBranchBInterior.lean`), with op `5` under the
layout contract (`ordCoreReadOrdKFBL_runs`), which places the order list itself.

Below the heap pointer, the part writes only the level graph, the footprint of core `idx - 1` and
the counter. Op `5` may rewrite that footprint, where the stretch tables of level `idx - 1` lie.
So the caller reads the descriptor of level `idx - 1` again at the end of the step
(`wireBranchBRefreshDescStmt`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- Apply the batch `reg 10` to the graph of level `idx = reg 96`, read the order list of level
`idx - 1` (op `5`, the list at `reg 9`), move the heap pointer past it, and add one to the rebuild
counter of level `idx`. -/
@[expose] def wireBranchBIntPrepKFBL (dgApply readOrd : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 96))) ;;
  .call 15 dgApply [.reg 6, .reg 10, .const 1] ;;
  .assign 22 (.bin .sub (.reg 96) (.const 1)) ;;
  .assign 3 (.load (.bin .add (.reg 77) (.reg 22))) ;;
  .assign 2 (.load (.bin .add (.reg 78) (.reg 22))) ;;
  ordCoreReadOrdStmt readOrd ;;
  .assign 4 (.reg 5) ;;
  .assign 0 (.reg 86) ;;
  .assign 1 (.reg 96) ;;
  incrementLevelCounter

theorem wireBranchBIntPrepKFBL_noRand (dgApply readOrd : ℕ) :
    (wireBranchBIntPrepKFBL dgApply readOrd).NoRand := by
  simp [wireBranchBIntPrepKFBL, ordCoreReadOrdStmt_noRand, incrementLevelCounter_noRand,
    Stmt.NoRand]

/-- The batch target with insertions allowed is the batch itself. -/
theorem foldl_dgBatchTarget_one (G : MGraph) (U : List Update) :
    U.foldl (dgBatchTarget 1) G = G.applyBatch U := by
  have hfun : dgBatchTarget 1 = MGraph.applyUpdate := by funext H u; simp [dgBatchTarget]
  rw [hfun]; rfl

section Execution

variable {w L depth k M N vCap eCap capExp : ℕ} {fmt : Num.Format w}
  {tool : SparseCoreRestartTool} {initialGraph : MGraph} {Psc : SparseCoreOrdParams}
  {allocation : ℕ → List ℕ → ℕ} {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ}

set_option maxHeartbeats 800000 in
/-- One run of `wireBranchBIntPrepKFBL` at level `idx`, with the heap pointer `curHeap = reg 4`.
Afterwards the graph at `gPtr` is `G` with the batch applied, the order list of the active branch
of core `idx - 1` lies at `curHeap + 1`, the heap pointer is the end `h1` of the op-`5` output,
and the rebuild counter of level `idx` is one larger. Below `curHeap` only the graph, the
footprint of core `idx - 1` and the counter change. -/
theorem wireBranchBIntPrepKFBL_runs {dgApply d idx curHeap curBatch bW gPtr handleBase branchBase
      levelMeta rcBase coreH branch count : ℕ}
    {G : MGraph} {U : List Update} {a : SparseCoreOrdAbs tool} {x : R.τ} {st : State}
    {ω : ℕ → Bool}
    (hLocal : R.Local)
    (hFootAt : SparseCoreReadoutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp Psc
      allocation R p op)
    (hDGApply : MeetsContract w p dgApply (dgApplyBatchContract w vCap eCap G G U bW))
    (hRegs : st.regs 4 = curHeap ∧ st.regs 10 = curBatch ∧ st.regs 75 = d ∧
      st.regs 77 = handleBase ∧ st.regs 78 = branchBase ∧ st.regs 83 = levelMeta ∧
      st.regs 86 = rcBase ∧ st.regs 96 = idx)
    (hCells : st.mem (levelMeta + d + idx) = gPtr ∧ st.mem (handleBase + (idx - 1)) = coreH ∧
      st.mem (branchBase + (idx - 1)) = branch ∧ st.mem (rcBase + idx) = count)
    (hIdx : 0 < idx)
    (hAddrW : levelMeta + d + idx < 2 ^ w ∧ handleBase + idx < 2 ^ w ∧
      branchBase + idx < 2 ^ w ∧ rcBase + idx < 2 ^ w)
    (hCountW : count + 1 < 2 ^ w) (hw : 16 ≤ 2 ^ w)
    (hGEnd : gPtr + dynGraphSize vCap eCap ≤ curHeap) (hBEnd : curBatch + bW ≤ curHeap)
    (hBOff : ∀ i < bW, curBatch + i < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ curBatch + i)
    (hBW : ∀ i < bW, st.mem (curBatch + i) < 2 ^ w)
    (hB : BatchAt st.mem curBatch G U bW) (hValid : G.BatchIsValid U)
    (hCaps : BatchWithinCaps vCap eCap U) (hG : DynGraphAt st.mem gPtr vCap eCap G)
    (hGOff : ∀ z, gPtr ≤ z → z < gPtr + dynGraphSize vCap eCap →
      ¬ R.foot coreH x z ∧ z ≠ handleBase + (idx - 1) ∧ z ≠ branchBase + (idx - 1) ∧
        z ≠ rcBase + idx)
    (hb : branch < k) (hkw : k < 2 ^ w) (hhw : coreH < 2 ^ w)
    (hrep : R.rep coreH a x st.mem) (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ z, R.foot coreH x z → z < curHeap) (hz : ZeroFrom st.mem curHeap)
    (hroom : curHeap + (1 + ordRotWords a branch) < 2 ^ w)
    (hRCLt : rcBase + idx < curHeap) (hRCOff : ¬ R.foot coreH x (rcBase + idx)) :
    ∃ (out : State) (cost h1 words : ℕ) (y : R.τ),
      Runs w p ω (wireBranchBIntPrepKFBL dgApply (op 5)) st .normal out cost ∧
      curHeap ≤ h1 ∧ h1 ≤ curHeap + (1 + ordRotWords a branch) ∧
      out.regs 4 = h1 ∧ out.regs 9 = curHeap + 1 ∧ out.regs 22 = idx - 1 ∧
      out.regs 2 = branch ∧ out.regs 3 = coreH ∧ out.regs 6 = gPtr ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 9 → r ≠ 15 →
        r ≠ 22 → out.regs r = st.regs r) ∧
      R.rep coreH a y out.mem ∧
      (∀ z, R.foot coreH y z → R.foot coreH x z ∨ (curHeap ≤ z ∧ z < h1)) ∧
      ZeroFrom out.mem h1 ∧
      OrdListAt out.mem (curHeap + 1) (tool.rot a.st branch) words ∧
      words ≤ ordRotWords a branch ∧ curHeap + 1 + words ≤ h1 ∧
      (∀ j < words, out.mem (curHeap + 1 + j) < 2 ^ w) ∧
      DynGraphAt out.mem gPtr vCap eCap (G.applyBatch U) ∧
      out.mem (rcBase + idx) = count + 1 ∧
      (∀ z < curHeap, ¬ R.foot coreH x z →
        (z < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ z) → z ≠ rcBase + idx →
        out.mem z = st.mem z) ∧
      cost + R.phi coreH y out.mem ≤
        670 * bW + Psc.mul * (ordRotWords a branch + 1) * SparseCore.bundleLogFactor M N + 100 +
          R.phi coreH x st.mem := by
  obtain ⟨hr4, hr10, hr75, hr77, hr78, hr83, hr86, hr96⟩ := hRegs
  obtain ⟨hGC, hHC, hBC, hRC⟩ := hCells
  obtain ⟨hGW, hHW, hBBW, hRCW⟩ := hAddrW
  -- Step 1: load the graph pointer and apply the batch
  let s1 := { st with regs := Function.update st.regs 6 gPtr }
  have r1 : Runs w p ω (.assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 96))))
      st .normal s1 7 :=
    runs_assign_iff.mpr ⟨gPtr, by simp [Expr.eval, BinOp.eval, hr83, hr75, hr96,
      show levelMeta + d < 2 ^ w by omega, hGW, hGC], rfl, rfl, rfl⟩
  obtain ⟨bodyDG, hBodyDG, oDG, outDG, cDG, rDGBody, hPostDG, hcDG⟩ :=
    hDGApply [gPtr, curBatch, 1] s1.mem s1.pos ω
      (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl <;> omega)
      ⟨gPtr, curBatch, 1, rfl, hw, by omega, by omega, hBOff, hBW, hB, hValid, hCaps, hG,
        Or.inl ⟨by decide, rfl⟩⟩
  obtain ⟨_, _, _, hEqDG, _, hDGAfter, hDGFr⟩ := hPostDG
  simp only [List.cons.injEq, and_true] at hEqDG
  obtain ⟨rfl, rfl, rfl⟩ := hEqDG
  rw [foldl_dgBatchTarget_one] at hDGAfter
  let s2 : State :=
    { regs := Function.update s1.regs 15 oDG.value, mem := outDG.mem, pos := outDG.pos }
  have r2 : Runs w p ω (.call 15 dgApply [.reg 6, .reg 10, .const 1]) s1 .normal s2 (3 + cDG + 1) :=
    runs_call_iff.mpr ⟨[gPtr, curBatch, 1], bodyDG, oDG, outDG, cDG,
      by simp [evalArgs, Expr.eval, s1, hr10, show 1 < 2 ^ w by omega],
      hBodyDG, rDGBody, rfl, rfl, by simp [argsSize, Expr.size]⟩
  have hcDG' : cDG ≤ 670 * bW + 30 := hcDG
  have hm2 (z : ℕ) (hz' : z < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ z) : s2.mem z = st.mem z :=
    hDGFr z hz'
  have hOffG (z : ℕ) (hz' : ¬ (gPtr ≤ z ∧ z < gPtr + dynGraphSize vCap eCap)) :
      z < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ z := by omega
  have hLoc2 := hLocal coreH a x st.mem s2.mem fun z hf =>
    (hm2 z (hOffG z fun ⟨h1, h2⟩ => (hGOff z h1 h2).1 hf)).symm
  -- Step 2: op `5` on core `idx - 1`
  let s3 := { s2 with regs := Function.update s2.regs 22 (idx - 1) }
  let s4 := { s3 with regs := Function.update s3.regs 3 coreH }
  let s5 := { s4 with regs := Function.update s4.regs 2 branch }
  have hHC2 : outDG.mem (handleBase + (idx - 1)) = coreH :=
    (hm2 _ (hOffG _ fun ⟨h1, h2⟩ => (hGOff _ h1 h2).2.1 rfl)).trans hHC
  have hBC2 : outDG.mem (branchBase + (idx - 1)) = branch :=
    (hm2 _ (hOffG _ fun ⟨h1, h2⟩ => (hGOff _ h1 h2).2.2.1 rfl)).trans hBC
  have r3 : Runs w p ω (.assign 22 (.bin .sub (.reg 96) (.const 1))) s2 .normal s3 4 :=
    runs_assign_iff.mpr ⟨idx - 1, by simp [Expr.eval, BinOp.eval, s2, s1, hr96,
      show 1 < 2 ^ w by omega, show idx - 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 77) (.reg 22)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨coreH, by simp [Expr.eval, BinOp.eval, s3, s2, s1, hr77,
      show handleBase + (idx - 1) < 2 ^ w by omega, hHC2], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 78) (.reg 22)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨branch, by simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, hr78,
      show branchBase + (idx - 1) < 2 ^ w by omega, hBC2], rfl, rfl, rfl⟩
  have hz5 : ZeroFrom s5.mem curHeap := fun z hz' =>
    (hm2 z (Or.inr (by omega))).trans (hz z hz')
  obtain ⟨s6, h1, words, cOrd, y, r6, hs6_5, hs6_9m, hRep6, hOrd6, hWLe6, hs6_9, hOrdEnd6,
      hOrdW6, hResp6, hc6, hs6_regs⟩ :=
    ordCoreReadOrdKFBL_runs (branch := branch) (handle := coreH) (heap := curHeap) (st := s5)
      (ω := ω) hFootAt (by simp [s5]) (by simp [s5, s4]) (by simp [s5, s4, s3, s2, s1, hr4])
      hb hkw hhw (hLoc2.1 hrep) hIn hfoot hz5 hroom
  obtain ⟨hh1Lo, hh1Hi, hz6, hfr6, hft6⟩ := hResp6
  rw [hs6_9] at hOrd6 hOrdEnd6 hOrdW6
  -- Step 3: the heap pointer and the counter
  let s7 := { s6 with regs := Function.update s6.regs 4 h1 }
  have r7 : Runs w p ω (.assign 4 (.reg 5)) s6 .normal s7 2 :=
    runs_assign_iff.mpr ⟨h1, by simp [Expr.eval, hs6_5], rfl, rfl, rfl⟩
  have hs6r (r : ℕ) (h5 : r ≠ 5) (h9 : r ≠ 9) (h2 : r ≠ 2) (h3 : r ≠ 3) (h22 : r ≠ 22)
      (h15 : r ≠ 15) (h6 : r ≠ 6) : s6.regs r = st.regs r := by
    rw [hs6_regs r h5 h9]
    simp [s5, s4, s3, s2, s1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h22, Function.update_of_ne h15, Function.update_of_ne h6]
  let s8 := { s7 with regs := Function.update s7.regs 0 rcBase }
  let s9 := { s8 with regs := Function.update s8.regs 1 idx }
  have r8 : Runs w p ω (.assign 0 (.reg 86)) s7 .normal s8 2 :=
    runs_assign_iff.mpr ⟨rcBase, by
      simp [Expr.eval, s7, hs6r 86 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hr86], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 1 (.reg 96)) s8 .normal s9 2 :=
    runs_assign_iff.mpr ⟨idx, by
      simp [Expr.eval, s8, s7, hs6r 96 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hr96], rfl, rfl, rfl⟩
  have hRC6 : s6.mem (rcBase + idx) = count :=
    (hfr6 _ (by omega) hRCOff).trans
      ((hm2 _ (hOffG _ fun ⟨h1, h2⟩ => (hGOff _ h1 h2).2.2.2 rfl)).trans hRC)
  obtain ⟨s10, r10, hs10Mem, hs10Regs, _⟩ :=
    incrementLevelCounter_runs (w := w) (base := rcBase) (level := idx) (count := count) (p := p)
      (st := s9) (ω := ω) (by simp [s9, s8]) (by simp [s9]) hRC6 hRCW hCountW
  have hm10 (z : ℕ) (hne : z ≠ rcBase + idx) : s10.mem z = s6.mem z := by
    rw [hs10Mem]; simp [s9, s8, s7, Function.update_of_ne hne]
  have hrun : Runs w p ω (wireBranchBIntPrepKFBL dgApply (op 5)) st .normal s10
      (cOrd + cDG + 50) := by
    unfold wireBranchBIntPrepKFBL
    exact runs_seq_iff.mpr (Or.inr ⟨s1, _, _, r1, runs_seq_iff.mpr (Or.inr ⟨s2, _, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, _, _, r3, runs_seq_iff.mpr (Or.inr ⟨s4, _, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, _, _, r5, runs_seq_iff.mpr (Or.inr ⟨s6, _, _, r6,
      runs_seq_iff.mpr (Or.inr ⟨s7, _, _, r7, runs_seq_iff.mpr (Or.inr ⟨s8, _, _, r8,
      runs_seq_iff.mpr (Or.inr ⟨s9, _, _, r9, r10, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      rfl⟩), rfl⟩), by omega⟩)
  -- the counter cell is off the new footprint
  have hRCy : ¬ R.foot coreH y (rcBase + idx) := fun hf => by
    rcases hft6 _ hf with h' | ⟨h', _⟩
    · exact hRCOff h'
    · omega
  have hLoc10 := hLocal coreH a y s6.mem s10.mem fun z hf =>
    (hm10 z fun he => hRCy (he ▸ hf)).symm
  have hs10r : s10.regs = s9.regs := hs10Regs
  refine ⟨s10, cOrd + cDG + 50, h1, words, y, hrun, hh1Lo, hh1Hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hLoc10.1 hRep6, hft6, ?_, ?_, hWLe6, hOrdEnd6, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs10r]; simp [s9, s8, s7]
  · rw [hs10r]; simp [s9, s8, s7, hs6_9]
  · rw [hs10r]; simp [s9, s8, s7, hs6_regs 22 (by decide) (by decide), s5, s4, s3]
  · rw [hs10r]; simp [s9, s8, s7, hs6_regs 2 (by decide) (by decide), s5]
  · rw [hs10r]; simp [s9, s8, s7, hs6_regs 3 (by decide) (by decide), s5, s4]
  · rw [hs10r]; simp [s9, s8, s7, hs6_regs 6 (by decide) (by decide), s5, s4, s3, s2, s1]
  · intro r h0 h1' h2 h3 h4 h5 h6 h9 h15 h22
    rw [hs10r]
    simp only [s9, s8, s7, Function.update_of_ne h1', Function.update_of_ne h0,
      Function.update_of_ne h4]
    exact hs6r r h5 h9 h2 h3 h22 h15 h6
  · intro z hz'
    rw [hm10 z (by omega)]
    exact hz6 z hz'
  · exact ordListAt_of_agree hOrd6 fun t ht => hm10 _ (by omega)
  · intro t ht
    rw [hm10 _ (by omega)]
    exact hOrdW6 t ht
  · exact dynGraphAt_of_agree hDGAfter fun z h1' h2' => by
      rw [hm10 z (hGOff z h1' h2').2.2.2]
      exact hfr6 z (by omega) (hGOff z h1' h2').1
  · rw [hs10Mem]; simp
  · intro z hz' hn hg hne
    rw [hm10 z hne, hfr6 z hz' hn]
    exact hm2 z hg
  · have hc6' : cOrd + R.phi coreH y s6.mem ≤
        Psc.mul * (ordRotWords a branch + 1) * SparseCore.bundleLogFactor M N + 8 +
          R.phi coreH x s5.mem := hc6
    have hphi5 : R.phi coreH x s5.mem = R.phi coreH x st.mem := hLoc2.2.symm
    rw [← hLoc10.2]
    omega

end Execution

end MinCostFlow.MinRatio
