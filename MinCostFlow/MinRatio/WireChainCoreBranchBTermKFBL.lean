module

public import MinCostFlow.MinRatio.WireChainCoreBranchBTermRebuildKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBRefreshKFBL
import WordRAM.Tactic

/-!
# The terminal step of Branch B under `KFBL` (`WireChainCoreBranchBTermKFBL`)

The loop of Branch B ends without a rebuild at a level `idx < d` exactly when every level `j < d`
took a plain update step. Then the step at level `d` tests the batch `nextU` for level `d`, whose
length is the word at `reg 10`.

* If the batch is empty, nothing is rebuilt. The step stores `firstReb = d + 1` at the select base
  `reg 72` (the word `mem heap = firstReb` of `UpdateCoreSelectOutAt`).
* If the batch is not empty, the step builds the last level from core `d - 1`
  (`wireBranchBTermRebuildKFBL`), stores `firstReb = d`, and reads the descriptor of level `d - 1`
  again (`wireBranchBRefreshDescStmt`). The readout ran ops `3`, `2` and `5` on core `d - 1` after
  its step, and these may rewrite the footprint, where the stretch rows of slot `d - 1` lie.

This file gives the step `wireBranchBTermKFBL` and one run lemma for each case:
`wireBranchBTermKFBL_runs_empty` and `wireBranchBTermKFBL_runs_nonEmpty`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- The terminal step of Branch B: if the batch at `mem (reg 10)` is not empty, build the last
level, store `d` at `reg 72` and refresh the descriptor of level `d - 1`; otherwise store `d + 1`
at `reg 72`. -/
@[expose] def wireBranchBTermKFBL (readGraph readLSF coreLenProc readOrd lastInit : ℕ) : Stmt :=
  .cond (.load (.reg 10))
    (wireBranchBTermRebuildKFBL readGraph readLSF coreLenProc readOrd lastInit ;;
     .store (.reg 72) (.reg 75) ;;
     .assign 22 (.bin .sub (.reg 75) (.const 1)) ;;
     wireBranchBRefreshDescStmt readLSF)
    (.store (.reg 72) (.bin .add (.reg 75) (.const 1)))

theorem wireBranchBTermKFBL_noRand (readGraph readLSF coreLenProc readOrd lastInit : ℕ) :
    (wireBranchBTermKFBL readGraph readLSF coreLenProc readOrd lastInit).NoRand := by
  simp [wireBranchBTermKFBL, wireBranchBTermRebuildKFBL_noRand,
    wireBranchBRefreshDescStmt_noRand, Stmt.NoRand]

/-- The terminal step with an empty batch for level `d`: it only stores `d + 1` at the select
base. -/
theorem wireBranchBTermKFBL_runs_empty {w d selBase curBatch : ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} (readGraph readLSF coreLenProc readOrd lastInit : ℕ)
    (hRegs : st.regs 10 = curBatch ∧ st.regs 72 = selBase ∧ st.regs 75 = d)
    (hEmpty : st.mem curBatch = 0) (hdW : d + 1 < 2 ^ w) :
    Runs w p ω (wireBranchBTermKFBL readGraph readLSF coreLenProc readOrd lastInit) st .normal
      { st with mem := Function.update st.mem selBase (d + 1) } 8 := by
  obtain ⟨hr10, hr72, hr75⟩ := hRegs
  have hw1 : 1 < 2 ^ w := by omega
  have rS : Runs w p ω (.store (.reg 72) (.bin .add (.reg 75) (.const 1))) st .normal
      { st with mem := Function.update st.mem selBase (d + 1) } 5 :=
    runs_store_iff.mpr ⟨selBase, d + 1, by simp [Expr.eval, hr72],
      by simp [Expr.eval, BinOp.eval, hr75, hw1, hdW], rfl, rfl, rfl⟩
  exact runs_cond_iff.mpr ⟨0, 5, by simp [Expr.eval, hr10, hEmpty], by simpa using rS, rfl⟩

set_option maxHeartbeats 800000 in
/-- The terminal step with a non-empty batch for level `d`, with the heap pointer `cur = reg 4`.
The hypotheses are those of `wireBranchBTermRebuildKFBL_runs`, the batch test, and the facts that
the refresh of `wireBranchBRefreshDescStmt_runs` needs at level `d - 1`. Let `h1` be the heap
pointer after the rebuild. The last level lies in `[cur, h1)`, and the refresh puts the two
stretch rows of slot `d - 1` in `[h1, h1 + 5)`. Below `cur` the step writes only the footprint
of core `d - 1`, the cells `handleBase + d` and `branchBase + d`, the select base and the two
descriptor words of slot `d - 1`. -/
theorem wireBranchBTermKFBL_runs_nonEmpty
    {w L depth k M N vCap eCap capExp capLimit init coreLenProc edgeProc signExt mul intDiv copy
      lastInit lastMul stretchPrec lastSpace nextM d cur handleBase branchBase levelMeta handle
      branch graph lens curBatch selBase : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {Psc : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ} {lastAlloc : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {RL : DSRep (ℕ × (ℕ → LSF))} {lastTool : LastLevelTool}
    {a : SparseCoreOrdAbs tool} {x : R.τ} {p : Program} {op opLast : ℕ → ℕ} {st : State}
    {ω : ℕ → Bool}
    (ℓ : ℕ → ℝ)
    (hFour : fmt.limbBits = 4)
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractKFBL fmt L depth tool initialGraph k M N vCap eCap capExp Psc
        allocation))
    (hFootAt : SparseCoreReadoutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp Psc
      allocation R p op)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hLastImpl : RL.Implements w p lastInit opLast
      (lastLevelRuntimeMachineContract fmt L lastTool (tool.S a.st branch) vCap eCap lastMul
        stretchPrec lastAlloc))
    (hLastSp : ∀ g l h, lastAlloc 1 [g, l, L, fmt.precision, h] ≤ lastSpace)
    (hRegs : st.regs 4 = cur ∧ st.regs 75 = d ∧ st.regs 77 = handleBase ∧
      st.regs 78 = branchBase ∧ st.regs 83 = levelMeta ∧ st.regs 94 = L ∧
      st.regs 95 = fmt.precision)
    (hRegs' : st.regs 10 = curBatch ∧ st.regs 72 = selBase)
    (hNonEmpty : st.mem curBatch ≠ 0)
    (hd : 0 < d)
    (hCells : st.mem (handleBase + (d - 1)) = handle ∧ st.mem (branchBase + (d - 1)) = branch ∧
      st.mem (levelMeta + d + (d - 1)) = graph ∧ st.mem (levelMeta + (d - 1)) = lens)
    (hAddrW : handleBase + d < 2 ^ w ∧ branchBase + d < 2 ^ w ∧ levelMeta + 2 * d < 2 ^ w)
    (hb : branch < k) (hkw : k < 2 ^ w) (hhw : handle < 2 ^ w) (hw9 : 9 < 2 ^ w)
    (hLWord : L < 2 ^ w) (hPWord : fmt.precision < 2 ^ w) (hWidth : fmt.precision ≤ 4 * L)
    (hG : DynGraphAt st.mem graph vCap eCap a.G)
    (hgEnd : graph + dynGraphSize vCap eCap ≤ cur)
    (hFootG : ∀ z, graph ≤ z → z < graph + dynGraphSize vCap eCap → ¬ R.foot handle x z)
    (hLen : EdgeValuesAt st.mem lens 4 L fmt.precision a.G.E ℓ)
    (hLenEnd : lens + eCap * L ≤ cur)
    (hFootLen : ∀ z, lens ≤ z → z < lens + eCap * L → ¬ R.foot handle x z)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ z, R.foot handle x z → z < cur) (hz : ZeroFrom st.mem cur)
    (hHE : (tool.S a.st branch).E ⊆ a.G.E)
    (hHm : (tool.S a.st branch).m ≤ nextM)
    (hRotWords : ordRotWords a branch ≤ 1 + 2 * N + 2 * nextM)
    (hCoreLenFits : ∀ e ∈ (tool.S a.st branch).E,
      ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ fmt.precision =
        coreLen (tool.lsfs a.st branch) ℓ e)
    (hStr : ∀ e ∈ (tool.S a.st branch).E, 2 * (2 : ℝ) ^ stretchPrec *
      lastLevelStretchBound (tool.S a.st branch) (coreLen (tool.lsfs a.st branch) ℓ) e <
        Num.capacity fmt.limbBits L)
    (hPos : ∀ e ∈ (tool.S a.st branch).E, 0 < coreLen (tool.lsfs a.st branch) ℓ e)
    (hAgree : lastTool.build (tool.S a.st branch)
        (fun e => if e ∈ (tool.S a.st branch).E then coreLen (tool.lsfs a.st branch) ℓ e else 0) =
      lastTool.build (tool.S a.st branch) (coreLen (tool.lsfs a.st branch) ℓ))
    (hTermCells : handleBase + d < cur ∧ branchBase + d < cur ∧
      handleBase + d ≠ branchBase + d ∧ ¬ R.foot handle x (handleBase + d) ∧
      ¬ R.foot handle x (branchBase + d))
    (hKeep : ∀ z, z = handleBase + (d - 1) ∨ z = branchBase + (d - 1) ∨
        z = levelMeta + d + (d - 1) ∨ (graph ≤ z ∧ z < graph + dynGraphSize vCap eCap) →
      z < cur ∧ ¬ R.foot handle x z ∧ z ≠ handleBase + d ∧ z ≠ branchBase + d ∧ z ≠ selBase)
    (hSel : selBase < cur ∧ ¬ R.foot handle x selBase)
    (hTermSel : ∀ z, z = handleBase + d ∨ z = branchBase + d →
      z ≠ selBase ∧ z ≠ selBase + 1 + 12 * (d - 1) + 8 ∧ z ≠ selBase + 1 + 12 * (d - 1) + 9)
    (hSlotLt : selBase + 1 + 12 * (d - 1) + 9 < cur)
    (hSlotOff : ¬ R.foot handle x (selBase + 1 + 12 * (d - 1) + 8) ∧
      ¬ R.foot handle x (selBase + 1 + 12 * (d - 1) + 9))
    (hroom : cur + (1 + dynGraphSize capLimit capLimit + 5 + capLimit * L +
      nextM * wireCoreLenEdgeSpace (ordLevelLwMax L capExp M N) + (2 + 2 * N + 2 * nextM)) +
        lastSpace + 7 < 2 ^ w) :
    let H := tool.S a.st branch
    let LwMax := ordLevelLwMax L capExp M N
    let slot := selBase + 1 + 12 * (d - 1)
    ∃ (out : State) (cost h1 ret : ℕ) (y : R.τ) (termTok : RL.τ),
      Runs w p ω (wireBranchBTermKFBL (op 3) (op 2) coreLenProc (op 5) lastInit)
        st .normal out cost ∧
      cur ≤ h1 ∧
      h1 ≤ cur + (1 + dynGraphSize capLimit capLimit + 5 + capLimit * L +
        nextM * wireCoreLenEdgeSpace LwMax + (2 + 2 * N + 2 * nextM)) + lastSpace ∧
      h1 ≤ ret ∧ ret ≤ h1 + 5 ∧ out.regs 4 = h1 + 7 ∧ ZeroFrom out.mem (h1 + 7) ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      R.rep handle a y out.mem ∧
      (∀ z, R.foot handle y z → R.foot handle x z ∨ (cur ≤ z ∧ z < ret)) ∧
      out.mem (branchBase + d) = 0 ∧ cur ≤ out.mem (handleBase + d) ∧
      RL.rep (out.mem (handleBase + d)) (lastTool.build H (coreLen (tool.lsfs a.st branch) ℓ))
        termTok out.mem ∧
      (∀ z, RL.foot (out.mem (handleBase + d)) termTok z →
        cur ≤ z ∧ z < h1 ∧ ¬ R.foot handle y z) ∧
      out.mem selBase = d ∧
      (∀ z < cur, ¬ R.foot handle x z → z ≠ handleBase + d → z ≠ branchBase + d →
        z ≠ selBase → z ≠ slot + 8 → z ≠ slot + 9 → out.mem z = st.mem z) ∧
      out.mem (slot + 8) = h1 + 5 ∧ out.mem (slot + 9) ≤ LwMax ∧
      StretchValuesAt out.mem (h1 + 5) fmt.limbBits (out.mem (slot + 9)) fmt.precision a.G.E
        (tool.lsfs a.st branch).wstr ∧
      SelOutTableAt w (R.foot handle y) h1 (h1 + 5) out.mem (h1 + 5) (out.mem (slot + 9))
        a.G.E ∧
      SelOutTableAt w (R.foot handle y) h1 (h1 + 5) out.mem (h1 + 5 + 1) (out.mem (slot + 9))
        a.G.E ∧
      cost + R.phi handle y out.mem + RL.phi (out.mem (handleBase + d)) termTok out.mem ≤
        3 * Psc.readout + copyGraphLiveCost H.n H.m + H.m * (wireCoreLenEdgeCost LwMax + 30) +
          Psc.mul * (ordRotWords a branch + 1) * SparseCore.bundleLogFactor M N +
          lastMul * (lastTool.cost H + 1) + R.phi handle x st.mem + 360 := by
  dsimp only
  have hA := wireBranchBTermRebuildKFBL_runs (ω := ω) (nextM := nextM) ℓ hFour himpl hFootAt
    hcapLim hCoreLenProc hEdgeProc hSign hMul hDiv hCopy hLastImpl hLastSp hRegs hd hCells hAddrW
    hb hkw hhw hw9 hLWord hPWord hWidth hG hgEnd hFootG hLen hLenEnd hFootLen hrep hIn hfoot hz
    hHE hHm hRotWords hCoreLenFits hStr hPos hAgree hTermCells (by omega)
  dsimp only at hA
  obtain ⟨sA, cA, y1, termTok, rA, hA4Lo, hA4Hi, hzA, hAregs, hRepA, hFootA, hTB, hTH, hTRep,
    hTFoot, hFrA, hcA⟩ := hA
  obtain ⟨hr4, hr75, hr77, hr78, hr83, -, -⟩ := hRegs
  obtain ⟨hr10, hr72⟩ := hRegs'
  obtain ⟨hHC, hBC, hGC, -⟩ := hCells
  obtain ⟨hHW, hBW, hLMW⟩ := hAddrW
  obtain ⟨hHLt, hBLt, -, hOffH, hOffB⟩ := hTermCells
  obtain ⟨hSelLt, hSelOff⟩ := hSel
  obtain ⟨hOff8, hOff9⟩ := hSlotOff
  have hw1 : 1 < 2 ^ w := by omega
  set h1 := sA.regs 4 with hh1
  set slot := selBase + 1 + 12 * (d - 1) with hslot
  have hFootA' (z : ℕ) (hz' : R.foot handle y1 z) : z < h1 := by
    rcases hFootA z hz' with h0 | ⟨_, h2⟩
    · have := hfoot z h0; omega
    · exact h2
  -- Step 1: store `firstReb = d` and set `reg 22 := d - 1`
  let sS := { sA with mem := Function.update sA.mem selBase d }
  have rS : Runs w p ω (.store (.reg 72) (.reg 75)) sA .normal sS 3 :=
    runs_store_iff.mpr ⟨selBase, d, by simp [Expr.eval, hAregs 72 (by decide), hr72],
      by simp [Expr.eval, hAregs 75 (by decide), hr75], rfl, rfl, rfl⟩
  let sT := { sS with regs := Function.update sS.regs 22 (d - 1) }
  have rT : Runs w p ω (.assign 22 (.bin .sub (.reg 75) (.const 1))) sS .normal sT 4 :=
    runs_assign_iff.mpr ⟨d - 1, by simp [Expr.eval, BinOp.eval, sS, hAregs 75 (by decide), hr75,
      hw1, show d - 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hmT (z : ℕ) (hz1 : z ≠ selBase) : sT.mem z = sA.mem z := by
    show Function.update sA.mem selBase d z = sA.mem z
    rw [Function.update_of_ne hz1]
  have hmTst (z : ℕ) (hlt : z < cur) (hnf : ¬ R.foot handle x z) (hnh : z ≠ handleBase + d)
      (hnb : z ≠ branchBase + d) (hns : z ≠ selBase) : sT.mem z = st.mem z :=
    (hmT z hns).trans (hFrA z hlt hnf hnh hnb)
  have hKeepT (z : ℕ) (hz' : z = handleBase + (d - 1) ∨ z = branchBase + (d - 1) ∨
      z = levelMeta + d + (d - 1) ∨ (graph ≤ z ∧ z < graph + dynGraphSize vCap eCap)) :
      sT.mem z = st.mem z := by
    obtain ⟨h1', h2', h3', h4', h5'⟩ := hKeep z hz'
    exact hmTst z h1' h2' h3' h4' h5'
  have hLocS := himpl.1 handle a y1 sA.mem sT.mem (fun z hz' => by
    have hne : z ≠ selBase := by
      rintro rfl
      rcases hFootA z hz' with h0 | ⟨h2, _⟩
      · exact hSelOff h0
      · omega
    exact (hmT z hne).symm)
  have hLocLS := hLastImpl.1 (sA.mem (handleBase + d))
    (lastTool.build (tool.S a.st branch) (coreLen (tool.lsfs a.st branch) ℓ)) termTok sA.mem sT.mem (fun z hz' => by
    have hne : z ≠ selBase := by
      rintro rfl
      have := (hTFoot z hz').1; omega
    exact (hmT z hne).symm)
  -- Step 2: the refresh of the descriptor of level `d - 1`
  obtain ⟨sR, cRef, ret, y, rR, hRetLo, hRetHi, hR4, hRregs, hRepR, hFootR, hzR, hFrR, h8R, h9R,
      hSVR, hT0R, hT1R, hcR⟩ :=
    wireBranchBRefreshDescStmt_runs (j := d - 1) (selBase := selBase) (cur := h1) (ω := ω)
      (st := sT) himpl.1 hFootAt
      ⟨by simp [sT, sS, hh1], by simp [sT], by simp [sT, sS, hAregs 72 (by decide), hr72],
        by simp [sT, sS, hAregs 75 (by decide), hr75],
        by simp [sT, sS, hAregs 77 (by decide), hr77],
        by simp [sT, sS, hAregs 78 (by decide), hr78],
        by simp [sT, sS, hAregs 83 (by decide), hr83]⟩
      ⟨(hKeepT _ (Or.inl rfl)).trans hHC, (hKeepT _ (Or.inr (Or.inl rfl))).trans hBC,
        (hKeepT _ (Or.inr (Or.inr (Or.inl rfl)))).trans hGC⟩
      ⟨by omega, by omega, by omega⟩ hb hkw hhw
      (dynGraphAt_of_agree hG fun z hlo hhi => hKeepT z (Or.inr (Or.inr (Or.inr ⟨hlo, hhi⟩))))
      (by omega) (hLocS.1 hRepA) hIn hFootA'
      (fun z hz' => by
        have hne : z ≠ selBase := by omega
        rw [hmT z hne]; exact hzA z hz')
      (by omega) (by omega)
      ⟨fun hf => by
        rcases hFootA _ hf with h0 | ⟨h2, _⟩
        · exact hOff8 h0
        · omega,
       fun hf => by
        rcases hFootA _ hf with h0 | ⟨h2, _⟩
        · exact hOff9 h0
        · omega⟩
  -- the last level across the refresh
  have hLocR := hLastImpl.1 (sA.mem (handleBase + d))
    (lastTool.build (tool.S a.st branch) (coreLen (tool.lsfs a.st branch) ℓ)) termTok sT.mem sR.mem (fun z hz' => by
    have hzA' := hTFoot z hz'
    have hnf : ¬ R.foot handle y1 z := hzA'.2.2
    exact (hFrR z hzA'.2.1 hnf (by omega) (by omega)).symm)
  obtain ⟨hHS, hH8, hH9⟩ := hTermSel _ (Or.inl rfl)
  obtain ⟨hBS, hB8, hB9⟩ := hTermSel _ (Or.inr rfl)
  have hHd : sR.mem (handleBase + d) = sA.mem (handleBase + d) := by
    have hnf : ¬ R.foot handle y1 (handleBase + d) := fun hf => by
      rcases hFootA _ hf with h0 | ⟨h2, _⟩
      · exact hOffH h0
      · omega
    rw [hFrR _ (by omega) hnf hH8 hH9, hmT _ hHS]
  have hBd : sR.mem (branchBase + d) = sA.mem (branchBase + d) := by
    have hnf : ¬ R.foot handle y1 (branchBase + d) := fun hf => by
      rcases hFootA _ hf with h0 | ⟨h2, _⟩
      · exact hOffB h0
      · omega
    rw [hFrR _ (by omega) hnf hB8 hB9, hmT _ hBS]
  have hSelR : sR.mem selBase = d := by
    have hnf : ¬ R.foot handle y1 selBase := fun hf => by
      rcases hFootA _ hf with h0 | ⟨h2, _⟩
      · exact hSelOff h0
      · omega
    rw [hFrR _ (by omega) hnf (by omega) (by omega)]
    show Function.update sA.mem selBase d selBase = d
    simp
  have rThen := runs_seq_iff.mpr (Or.inr ⟨sA, cA, _, rA,
    runs_seq_iff.mpr (Or.inr ⟨sS, 3, _, rS,
    runs_seq_iff.mpr (Or.inr ⟨sT, 4, cRef, rT, rR, rfl⟩), rfl⟩), rfl⟩)
  have rCond : Runs w p ω (wireBranchBTermKFBL (op 3) (op 2) coreLenProc (op 5) lastInit)
      st .normal sR _ :=
    runs_cond_iff.mpr ⟨st.mem curBatch, _, by simp [Expr.eval, hr10],
      by simpa [hNonEmpty] using rThen, rfl⟩
  refine ⟨sR, _, h1, ret, y, termTok, rCond, hA4Lo, hA4Hi, hRetLo, hRetHi, hR4, hzR,
    fun r hr => ?_, hRepR, fun z hz' => ?_, hBd.trans hTB, hHd ▸ hTH, ?_, fun z hz' => ?_,
    hSelR, fun z hz' hnf hnh hnb hns hn8 hn9 => ?_, h8R, h9R, hSVR, hT0R, hT1R, ?_⟩
  · rw [hRregs r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)]
    simp only [sT, sS, Function.update_of_ne (by omega : r ≠ 22)]
    exact hAregs r hr
  · rcases hFootR z hz' with h0 | h0
    · rcases hFootA z h0 with h2 | ⟨h2, h3⟩
      · exact Or.inl h2
      · exact Or.inr ⟨h2, by omega⟩
    · exact Or.inr ⟨by omega, h0.2⟩
  · rw [hHd]; exact hLocR.1 (hLocLS.1 hTRep)
  · rw [hHd] at hz'
    obtain ⟨h2, h3, h4⟩ := hTFoot z hz'
    refine ⟨h2, h3, fun hf => ?_⟩
    rcases hFootR z hf with h0 | ⟨h5, _⟩
    · exact h4 h0
    · omega
  · have hnf' : ¬ R.foot handle y1 z := fun hf => by
      rcases hFootA z hf with h0 | ⟨h2, _⟩
      · exact hnf h0
      · omega
    rw [hFrR z (by omega) hnf' hn8 hn9]
    exact hmTst z hz' hnf hnh hnb hns
  · have hPhiS : R.phi handle y1 sT.mem = R.phi handle y1 sA.mem := hLocS.2.symm
    have hPhiL : RL.phi (sA.mem (handleBase + d)) termTok sR.mem =
        RL.phi (sA.mem (handleBase + d)) termTok sA.mem := (hLocLS.2.trans hLocR.2).symm
    rw [hHd, hPhiL]
    rw [hPhiS] at hcR
    simp only [Expr.size]
    clear rCond rThen rA rR rS rT hRepR hRepA hTRep hLocS hLocLS hLocR
    omega

end MinCostFlow.MinRatio
