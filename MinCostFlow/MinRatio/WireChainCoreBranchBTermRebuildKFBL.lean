module

public import MinCostFlow.MinRatio.WireInitReadoutKFBL
public import MinCostFlow.MinRatio.WireRebuildSuffixLoopKBase
import WordRAM.Tactic

/-!
# The rebuild of the last level in Branch B under `KFBL` (`WireChainCoreBranchBTermRebuildKFBL`)

When no level `idx < d` of Branch B is rebuilt and the batch for level `d` is not empty, the
step reads the graph and the lengths of level `d` from core `d - 1` with the live readout
`ordReadoutNextLevelKFBL`, and then builds the last level on them with
`rebuildTerminalRuntimeStep`. This file gives that part, `wireBranchBTermRebuildKFBL`, and its run
lemma `wireBranchBTermRebuildKFBL_runs`. It is `wireBranchBTerminalStep` without the test on the
batch, with the readout of `KFBL` in place of the readout of that step.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- Read the level-`d` graph and lengths from core `d - 1`, then build the last level and store
its handle and the branch `0` at `handleBase + d` and `branchBase + d`. -/
@[expose] def wireBranchBTermRebuildKFBL (readGraph readLSF coreLenProc readOrd lastInit : ℕ) :
    Stmt :=
  .assign 22 (.bin .sub (.reg 75) (.const 1)) ;;
  .assign 3 (.load (.bin .add (.reg 77) (.reg 22))) ;;
  .assign 2 (.load (.bin .add (.reg 78) (.reg 22))) ;;
  .assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 22))) ;;
  .assign 7 (.load (.bin .add (.reg 83) (.reg 22))) ;;
  .assign 67 (.reg 94) ;;
  .assign 68 (.reg 95) ;;
  ordReadoutNextLevelKFBL readGraph readLSF coreLenProc readOrd ;;
  .assign 51 (.bin .add (.reg 77) (.reg 75)) ;;
  .assign 52 (.bin .add (.reg 78) (.reg 75)) ;;
  rebuildTerminalRuntimeStep lastInit

theorem wireBranchBTermRebuildKFBL_noRand (readGraph readLSF coreLenProc readOrd lastInit : ℕ) :
    (wireBranchBTermRebuildKFBL readGraph readLSF coreLenProc readOrd lastInit).NoRand := by
  simp [wireBranchBTermRebuildKFBL, ordReadoutNextLevelKFBL_noRand, rebuildTerminalRuntimeStep,
    rebuildLastLevelRuntime, storeRebuiltLevel, Stmt.NoRand]

set_option maxHeartbeats 800000 in
/-- One run of `wireBranchBTermRebuildKFBL` with the heap pointer `cur = reg 4`. Core `d - 1` has
handle `handle`, branch `branch`, graph `a.G` at `graph` and lengths `ℓ` at `lens`. Let
`H = tool.S a.st branch` be the sparsifier of its active branch. The part builds the last level on
`H` with the lengths `coreLen (tool.lsfs a.st branch) ℓ`, in fresh heap. Below `cur` it writes only
the footprint of core `d - 1` and the two cells `handleBase + d` and `branchBase + d`. -/
theorem wireBranchBTermRebuildKFBL_runs
    {w L depth k M N vCap eCap capExp capLimit init coreLenProc edgeProc signExt mul intDiv copy
      lastInit lastMul stretchPrec lastSpace nextM d cur handleBase branchBase levelMeta handle
      branch graph lens : ℕ}
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
    (hroom : cur + (1 + dynGraphSize capLimit capLimit + 5 + capLimit * L +
      nextM * wireCoreLenEdgeSpace (ordLevelLwMax L capExp M N) + (2 + 2 * N + 2 * nextM)) +
        lastSpace < 2 ^ w) :
    let H := tool.S a.st branch
    let LwMax := ordLevelLwMax L capExp M N
    ∃ (out : State) (cost : ℕ) (y : R.τ) (termTok : RL.τ),
      Runs w p ω (wireBranchBTermRebuildKFBL (op 3) (op 2) coreLenProc (op 5) lastInit)
        st .normal out cost ∧
      cur ≤ out.regs 4 ∧
      out.regs 4 ≤ cur + (1 + dynGraphSize capLimit capLimit + 5 + capLimit * L +
        nextM * wireCoreLenEdgeSpace LwMax + (2 + 2 * N + 2 * nextM)) + lastSpace ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      R.rep handle a y out.mem ∧
      (∀ z, R.foot handle y z → R.foot handle x z ∨ (cur ≤ z ∧ z < out.regs 4)) ∧
      out.mem (branchBase + d) = 0 ∧ cur ≤ out.mem (handleBase + d) ∧
      RL.rep (out.mem (handleBase + d)) (lastTool.build H (coreLen (tool.lsfs a.st branch) ℓ))
        termTok out.mem ∧
      (∀ z, RL.foot (out.mem (handleBase + d)) termTok z →
        cur ≤ z ∧ z < out.regs 4 ∧ ¬ R.foot handle y z) ∧
      (∀ z < cur, ¬ R.foot handle x z → z ≠ handleBase + d → z ≠ branchBase + d →
        out.mem z = st.mem z) ∧
      cost + R.phi handle y out.mem + RL.phi (out.mem (handleBase + d)) termTok out.mem ≤
        2 * Psc.readout + copyGraphLiveCost H.n H.m + H.m * (wireCoreLenEdgeCost LwMax + 30) +
          Psc.mul * (ordRotWords a branch + 1) * SparseCore.bundleLogFactor M N +
          lastMul * (lastTool.cost H + 1) + R.phi handle x st.mem + 220 := by
  dsimp only
  obtain ⟨hr4, hr75, hr77, hr78, hr83, hr94, hr95⟩ := hRegs
  obtain ⟨hHC, hBC, hGC, hLC⟩ := hCells
  obtain ⟨hHW, hBW, hLMW⟩ := hAddrW
  obtain ⟨hHLt, hBLt, hHBNe, hOffH, hOffB⟩ := hTermCells
  have hw1 : 1 < 2 ^ w := by omega
  -- Step 1: the seven loads and moves
  let s1 := { st with regs := Function.update st.regs 22 (d - 1) }
  let s2 := { s1 with regs := Function.update s1.regs 3 handle }
  let s3 := { s2 with regs := Function.update s2.regs 2 branch }
  let s4 := { s3 with regs := Function.update s3.regs 6 graph }
  let s5 := { s4 with regs := Function.update s4.regs 7 lens }
  let s6 := { s5 with regs := Function.update s5.regs 67 L }
  let s7 := { s6 with regs := Function.update s6.regs 68 fmt.precision }
  have r1 : Runs w p ω (.assign 22 (.bin .sub (.reg 75) (.const 1))) st .normal s1 4 :=
    runs_assign_iff.mpr ⟨d - 1, by simp [Expr.eval, BinOp.eval, hr75, hw1,
      show d - 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 77) (.reg 22)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, BinOp.eval, s1, hr77,
      show handleBase + (d - 1) < 2 ^ w by omega, hHC], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 78) (.reg 22)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨branch, by simp [Expr.eval, BinOp.eval, s2, s1, hr78,
      show branchBase + (d - 1) < 2 ^ w by omega, hBC], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 22))))
      s3 .normal s4 7 :=
    runs_assign_iff.mpr ⟨graph, by simp [Expr.eval, BinOp.eval, s3, s2, s1, hr83, hr75,
      show levelMeta + d < 2 ^ w by omega, show levelMeta + d + (d - 1) < 2 ^ w by omega, hGC],
      rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 83) (.reg 22)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨lens, by simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, hr83,
      show levelMeta + (d - 1) < 2 ^ w by omega, hLC], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 67 (.reg 94)) s5 .normal s6 2 :=
    runs_assign_iff.mpr ⟨L, by simp [Expr.eval, s5, s4, s3, s2, s1, hr94], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 68 (.reg 95)) s6 .normal s7 2 :=
    runs_assign_iff.mpr ⟨fmt.precision, by simp [Expr.eval, s6, s5, s4, s3, s2, s1, hr95],
      rfl, rfl, rfl⟩
  have hs7 (r : ℕ) (h1 : r ≠ 2) (h2 : r ≠ 3) (h3 : r ≠ 6) (h4 : r ≠ 7) (h5 : r ≠ 22)
      (h6 : r ≠ 67) (h7 : r ≠ 68) : s7.regs r = st.regs r := by
    simp [s7, s6, s5, s4, s3, s2, s1, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5,
      Function.update_of_ne h6, Function.update_of_ne h7]
  -- Step 2: the live readout of core `d - 1`
  have hRoomRead : cur + 1 + dynGraphSize capLimit capLimit + 5 + capLimit * L +
      nextM * wireCoreLenEdgeSpace (ordLevelLwMax L capExp M N) + (2 + 2 * N + 2 * nextM) <
        2 ^ w := by omega
  obtain ⟨s8, vcH, ecH, nOW, Lw, cRead, y1, r8, hLw8, hvcH, hecH, _, hRep8, hDG8, hLen8, _,
      _, _, _, _, _, h6Lo8, h6End8, _, h7Lo8, h7End8, _, h4Lo8, h4Hi8, hz8, hFr8, hFoot8Lt,
      hFoot8In, hs8_regs, hc8⟩ :=
    ordReadoutNextLevelKFBL_runs_bounded (ω := ω) (st := s7) (nextM := nextM) ℓ hFour himpl
      hFootAt hcapLim hCoreLenProc hEdgeProc hSign hMul hDiv hCopy
      (by simp [s7, s6, s5, s4, s3]) (by simp [s7, s6, s5, s4, s3, s2])
      ((hs7 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans hr4) (by simp [s7, s6, s5, s4]) (by simp [s7, s6, s5])
      (by simp [s7, s6]) hb hkw hhw hw9 hG hgEnd hFootG hLen hLenEnd hFootLen hrep hIn hfoot
      hz hHE hHm hRotWords hCoreLenFits hRoomRead
  rw [hvcH, hecH] at hDG8 h6End8
  rw [hecH] at h7End8
  have hs8r (r : ℕ) (hr : 70 ≤ r) : s8.regs r = st.regs r :=
    (hs8_regs r (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr)))))).trans
      (hs7 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  -- Step 3: the two cells of level `d`
  let s9 := { s8 with regs := Function.update s8.regs 51 (handleBase + d) }
  let s10 := { s9 with regs := Function.update s9.regs 52 (branchBase + d) }
  have r9 : Runs w p ω (.assign 51 (.bin .add (.reg 77) (.reg 75))) s8 .normal s9 4 :=
    runs_assign_iff.mpr ⟨handleBase + d, by
      simp [Expr.eval, BinOp.eval, hs8r 77 (by decide), hs8r 75 (by decide), hr77, hr75, hHW],
      rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.assign 52 (.bin .add (.reg 78) (.reg 75))) s9 .normal s10 4 :=
    runs_assign_iff.mpr ⟨branchBase + d, by
      simp [Expr.eval, BinOp.eval, s9, hs8r 78 (by decide), hs8r 75 (by decide), hr78, hr75,
        hBW], rfl, rfl, rfl⟩
  -- Step 4: the last-level rebuild
  have hs8_67 : s8.regs 67 = L :=
    (hs8_regs 67 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).trans (by simp [s7, s6])
  have hs8_68 : s8.regs 68 = fmt.precision :=
    (hs8_regs 68 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).trans (by simp [s7])
  obtain ⟨s11, ret11, cTerm, termTok, r11, hTermH11, hTermB11, hs11_4, hTermRep11, hz11,
      hTermFoot11, hFrTerm11, hRet11Lo, hRet11Hi, hcTerm⟩ :=
    wireRebuildTerminalStep_runs (w := w) (L := L) (init := lastInit) (graph := s8.regs 6)
      (lengths := s8.regs 7) (heap := s8.regs 4) (vCap := vCap) (eCap := eCap)
      (multiplier := lastMul) (stretchPrecision := stretchPrec)
      (handleCell := handleBase + d) (branchCell := branchBase + d)
      (st := s10) (ω := ω) hLastImpl
      (by simp [s10, s9]) (by simp [s10, s9]) (by simp [s10, s9])
      (by simp [s10, s9, hs8_67]) (by simp [s10, s9, hs8_68])
      hLWord hPWord hFour hWidth (coreLen (tool.lsfs a.st branch) ℓ) hDG8 h6End8 h7End8
      (by rw [hFour]; exact hLen8) hStr hPos hz8
      ((Nat.add_le_add_left (hLastSp _ _ _) _).trans_lt (by omega)) hAgree
      (by simp [s10, s9]) (by simp [s10]) hHBNe (by omega) (by omega)
  -- the state of core `d - 1` across the rebuild
  have hLoc11 := himpl.1 handle a y1 s8.mem s11.mem
    (fun z hz' => (hFrTerm11 z (hFoot8Lt z hz')
      (fun h => (hFoot8In z hz').elim (fun h0 => hOffH (h ▸ h0)) (fun ⟨hlo, _⟩ => by omega))
      (fun h => (hFoot8In z hz').elim (fun h0 => hOffB (h ▸ h0))
        (fun ⟨hlo, _⟩ => by omega))).symm)
  have hs11r (r : ℕ) (hr : 70 ≤ r) : s11.regs r = st.regs r := by
    have h1' : s11.regs r = s10.regs r :=
      runs_preserves_above (s := rebuildTerminalRuntimeStep lastInit) (by omega : 53 ≤ r) rfl r11
    rw [h1']
    simp only [s10, s9, Function.update_of_ne (by omega : r ≠ 52),
      Function.update_of_ne (by omega : r ≠ 51)]
    exact hs8r r hr
  have rAll := runs_seq_iff.mpr (Or.inr ⟨s1, 4, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 7, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 5, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 2, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 2, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, cRead, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 4, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 4, cTerm, r10, r11, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hPhi11 : R.phi handle y1 s11.mem = R.phi handle y1 s8.mem := hLoc11.2.symm
  refine ⟨s11, _, y1, termTok, rAll, by rw [hs11_4]; exact h4Lo8.trans hRet11Lo,
    by rw [hs11_4]; have := hLastSp (s8.regs 6) (s8.regs 7) (s8.regs 4); omega,
    hs11_4.symm ▸ hz11, hs11r, hLoc11.1 hRep8, fun z hz' => ?_, hTermB11,
    hTermH11.symm ▸ h4Lo8, hTermH11.symm ▸ hTermRep11, fun z hz' => ?_,
    fun z hz' hnf hnh hnb => ?_, ?_⟩
  · rcases hFoot8In z hz' with h0 | ⟨hlo, hhi⟩
    · exact Or.inl h0
    · exact Or.inr ⟨hlo, hhi.trans_le (hs11_4.symm ▸ hRet11Lo)⟩
  · rw [hTermH11] at hz'
    have hf := hTermFoot11 z hz'
    exact ⟨h4Lo8.trans hf.1, hs11_4.symm ▸ hf.2, fun hfc => by have := hFoot8Lt z hfc; omega⟩
  · exact (hFrTerm11 z (hz'.trans_le h4Lo8) hnh hnb).trans (hFr8 z hz' hnf)
  · have hPhi7 : R.phi handle x s7.mem = R.phi handle x st.mem := rfl
    rw [hPhi11, hTermH11]
    rw [hPhi7] at hc8
    clear rAll r11 r8 hTermRep11 hRep8 hDG8 hLen8 hLoc11
    omega

end MinCostFlow.MinRatio
