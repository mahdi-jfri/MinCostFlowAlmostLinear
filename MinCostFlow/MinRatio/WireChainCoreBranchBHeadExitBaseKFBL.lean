module

public import MinCostFlow.MinRatio.WireChainCoreBranchBHeadExitKFBL
import MinCostFlow.MinRatio.WireStmtNoWriteIn
import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailBaseKFBL
import WordRAM.Tactic

/-!
# Basic facts on a run of Branch B up to the exit of the loop (`WireChainCoreBranchBHeadExitBaseKFBL`)

The three exits of the loop of Branch B start from the same state. This file collects the facts
on a run up to the exit (`BranchBRunPreExitKFBL`) that all three exits read first.

* `sE_regs`: the registers `70`, `80`, `81`, `87` at the top of the last pass of the loop hold
  their values of the dispatch. The prefix and the front keep the registers from `70` on (but
  `96`, `97` and `99`), and the loop does not write them (`wireBranchBLoopKFBL_noWrite`).
* `sE_loopRegs`: the registers `96 = i₀` and `75 = d` at the top of the last pass, from the loop
  invariant.
* `sL_regs`: the same registers at the end `sL` of the loop, where the test of the exit reads
  them. The loop facts relate `sL` to `sE`.
* `heap_order`: the heap pointers `uIntBuf`, `heap`, `hS1`, `heap2` and `sE.regs 4` are in order.
* `i₀_pos`, `i₀_le`, `exit_cases`: `0 < i₀ ≤ d`, so the exit is interior (`i₀ < d`), terminal
  with a batch, or terminal with an empty batch. Level `0` does not fire (`noFire` of the start),
  so the loop passes level `0`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

namespace BranchBRunPreExitKFBL

variable {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
      canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
      collectDel emitCuts zeroIns filterEdits pushInsProc pushProc : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {stepCap : ℕ → ℕ → ℕ}
    {root uIntBuf editsPtr editWords g l heap pos : ℕ} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}

variable (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)

/-- The registers `70`, `80`, `81` and `87` at the top of the last pass of the loop hold their
values of the dispatch: the prefix and the front keep the registers from `70` on (but `96`, `97`
and `99`), the loop does not write them (`wireBranchBLoopKFBL_noWrite`), and the loop facts
relate the end of the loop to the top of its last pass. -/
theorem sE_regs :
    H.sE.regs 70 = root ∧ H.sE.regs 80 = heap + 1 + 12 * cfg.P.d ∧
      H.sE.regs 81 = heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) ∧ H.sE.regs 87 = uIntBuf := by
  have hPreR := H.pre.2.2.1
  have hFrR := H.front.2.2.2.2
  have hLER := H.loop.2.2.2.2.2.2.2.2.2.1
  have hLRun := H.loop.1
  have hD := H.dispatch.2.2.1
  have hNW := runs_regs_of_noWriteIn hLRun (wireBranchBLoopKFBL_noWrite _ _ _ _ _ _)
  have hPres (r : ℕ) (hS : r = 70 ∨ r = 80 ∨ r = 81 ∨ r = 87) :
      H.sE.regs r = H.st.regs r := by
    have h70 : 70 ≤ r := by omega
    have h1 : H.sL.regs r = H.sE.regs r := hLER r (by omega) (by omega) (by omega) (by omega)
    have h2 : H.sL.regs r = H.sF0.regs r := hNW r hS
    have h3 : H.sF0.regs r = H.sP.regs r :=
      hFrR r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
    have h4 : H.sP.regs r = H.st.regs r := hPreR r h70
    rw [← h1, h2, h3, h4]
  obtain ⟨_, _, _, _, _, _, _, _, _, h80, h81, _, _, _, _, h87, _⟩ := hD.2
  exact ⟨(hPres 70 (by omega)).trans hD.2.1, (hPres 80 (by omega)).trans h80,
    (hPres 81 (by omega)).trans h81, (hPres 87 (by omega)).trans h87⟩

/-- The registers `96` and `75` at the top of the last pass of the loop hold the level `i₀` and
the depth `d` (the loop invariant `regs`). -/
theorem sE_loopRegs : H.sE.regs 96 = H.i₀ ∧ H.sE.regs 75 = cfg.P.d := by
  obtain ⟨_, _, _, _, _, _, _, _, r75, _, _, _, _, _, _, _, _, _, r96, _⟩ :=
    H.loop.2.2.2.2.1.regs
  exact ⟨r96, r75⟩

/-- The registers at the end `sL` of the loop, where the exit reads them: `96` holds `i₀`, `75`
holds `d`, and `70`, `80`, `81`, `87` hold their values of the dispatch. The loop facts give
`sL.regs r = sE.regs r` for these registers, and `sE_regs`, `sE_loopRegs` give their values at
`sE`. The register `4` and the memory are those of `sE`, by the same loop facts. -/
theorem sL_regs :
    H.sL.regs 96 = H.i₀ ∧ H.sL.regs 75 = cfg.P.d ∧ H.sL.regs 70 = root ∧
      H.sL.regs 80 = heap + 1 + 12 * cfg.P.d ∧
      H.sL.regs 81 = heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) ∧ H.sL.regs 87 = uIntBuf ∧
      H.sL.regs 99 = H.i₀ ∧ H.sL.regs 4 = H.sE.regs 4 ∧ H.sL.mem = H.sE.mem := by
  have hLER := H.loop.2.2.2.2.2.2.2.2.2.1
  have h99 := H.loop.2.2.2.2.2.2.2.2.2.2.1
  have hMem := H.loop.2.2.2.2.2.2.2.2.1
  obtain ⟨r70, r80, r81, r87⟩ := sE_regs H
  obtain ⟨r96, r75⟩ := sE_loopRegs H
  have hR (r : ℕ) (h16 : r ≠ 16) (h17 : r ≠ 17) (h18 : r ≠ 18) (h99 : r ≠ 99) :
      H.sL.regs r = H.sE.regs r := hLER r h16 h17 h18 h99
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h99, hR 4 (by omega) (by omega) (by omega) (by omega), hMem⟩
  · rw [hR 96 (by omega) (by omega) (by omega) (by omega)]; exact r96
  · rw [hR 75 (by omega) (by omega) (by omega) (by omega)]; exact r75
  · rw [hR 70 (by omega) (by omega) (by omega) (by omega)]; exact r70
  · rw [hR 80 (by omega) (by omega) (by omega) (by omega)]; exact r80
  · rw [hR 81 (by omega) (by omega) (by omega) (by omega)]; exact r81
  · rw [hR 87 (by omega) (by omega) (by omega) (by omega)]; exact r87

/-- The heap pointers of the run up to the exit are in order: `uIntBuf`, `heap`, `hS1`, `heap2`
and `sE.regs 4` (the start, the prefix, the front and the loop). -/
theorem heap_order :
    uIntBuf ≤ heap ∧ heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ H.hS1 ∧
    H.hS1 + 3 * L ≤ H.heap2 ∧ H.heap2 ≤ H.sE.regs 4 := by
  have h1 := H.start.uLe
  have h2 := H.start.edHeap
  obtain ⟨_, _, _, hh0, _, hS1h, _⟩ := H.pre
  obtain ⟨_, _, hF4, _⟩ := H.front
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hL4, _⟩ := H.loop
  refine ⟨by omega, hh0, hS1h, ?_⟩
  rw [hF4] at hL4
  omega

/-- The loop stops at a level `i₀ ≤ d` (the loop facts). -/
theorem i₀_le : H.i₀ ≤ cfg.P.d := H.loop.2.2.1

/-- The loop passes level `0`: `0 < i₀`. Level `0` does not fire (`noFire` of the start), and
the loop facts say that a level `idx < d` that does not fire is passed. Here `idx = 0`, the
batch is `Uint` and the chain state is `st0`, whose update count at level `0` is that of the
model. -/
theorem i₀_pos : 0 < H.i₀ :=
  H.loop.2.2.2.1 (by rw [H.st0_eq, H.Uint_eq]; exact H.start.noFire) H.start.modelInv.1.1

/-- The three exits of the loop: interior (`0 < i₀ < d`), terminal with a batch (`i₀ = d`,
`curUE ≠ []`), or terminal with an empty batch (`i₀ = d`, `curUE = []`), by `i₀_pos` and
`i₀_le`. -/
theorem exit_cases :
    (0 < H.i₀ ∧ H.i₀ < cfg.P.d) ∨ (H.i₀ = cfg.P.d ∧ H.curUE ≠ []) ∨
      (H.i₀ = cfg.P.d ∧ H.curUE = []) := by
  have h0 := i₀_pos H
  have h1 := i₀_le H
  rcases Nat.lt_or_eq_of_le h1 with h | h
  · exact Or.inl ⟨h0, h⟩
  · by_cases hU : H.curUE = []
    · exact Or.inr (Or.inr ⟨h, hU⟩)
    · exact Or.inr (Or.inl ⟨h, hU⟩)

end BranchBRunPreExitKFBL

end MinCostFlow.MinRatio
