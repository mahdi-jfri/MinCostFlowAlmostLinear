module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunHeadKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailPhaseKFBL
import MinCostFlow.MinRatio.WireStmtNoWriteIn
import MinCostFlow.MinRatio.WireChainCoreBranchBSpaceProofLastTerm
import WordRAM.Tactic

/-!
# Basic facts on the head of a run of Branch B (`WireChainCoreBranchBRunTailBaseKFBL`)

The tail of a run of Branch B starts at the state `sX` after the exit of the loop. This file
collects the facts on the head `BranchBRunHeadKFBL` that the tail reads first:
* `min_fr`: the number of the finished levels is `i₀` in each of the three exits;
* `sE_regs`, `sX_regs`: the registers that the suffix reads, at the state `sX`. The loop does
  not write the registers `70`, `80`, `81`, `87` (`loop_noWrite`), and the exit keeps the
  registers from `70` on except `97` and `99`.

The heap order `heap_order` and the root graph `X_G0` of a head are in
`WireChainCoreBranchBRunTailPhaseKFBL`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The loop of Branch B writes none of the registers `70`, `80`, `81`, `87`. -/
theorem wireBranchBLoopKFBL_noWrite (updCore readLSF dgApply copyProc updLen slotProc : ℕ) :
    stmtNoWriteIn (fun r => r = 70 ∨ r = 80 ∨ r = 81 ∨ r = 87)
      (wireBranchBLoopKFBL updCore readLSF dgApply copyProc updLen slotProc) := by
  simp [wireBranchBLoopKFBL, wireBranchBLoopBodyKFBL, wireBranchBStepKFBL,
    wireBranchBStepHeadKFBL, wireBranchBStepTailKFBL, wireBranchBStepTailFrontKFBL,
    wireBranchBCopyListsStmt, wireBranchBReadDescStmt, wireBranchBNextLenStmt,
    wireBranchBSlotStmt, ordCoreUpdateStmt, ordLoadBranchOutStmt, ordCoreReadLSFStmt,
    wireStretchDescCopyStmt, wireGuardCopyWordStmt, stmtNoWriteIn]

namespace BranchBRunHeadKFBL

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

variable (Hd : BranchBRunHeadKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)

/-- The number of the finished levels after the exit: `min fr d = i₀` (`fr = i₀ < d` at the
interior exit, and `i₀ = d ≤ fr` at the terminal exits). -/
theorem min_fr : min Hd.fr cfg.P.d = Hd.i₀ := by
  rcases Hd.exitCase with ⟨_, hi, hfr, _⟩ | ⟨hi, _, hfr, _⟩ | ⟨hi, _, hfr, _⟩ <;> omega

/-- The registers `70`, `80`, `81` and `87` at the top of the last pass of the loop hold their
values of the dispatch: the prefix and the front keep the registers from `70` on (but `96`, `97`
and `99`), the loop does not write them (`wireBranchBLoopKFBL_noWrite`), and the loop facts
relate the end of the loop to the top of its last pass. -/
theorem sE_regs :
    Hd.sE.regs 70 = root ∧ Hd.sE.regs 80 = heap + 1 + 12 * cfg.P.d ∧
      Hd.sE.regs 81 = heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) ∧ Hd.sE.regs 87 = uIntBuf := by
  have hPreR := Hd.pre.2.2.1
  have hFrR := Hd.front.2.2.2.2
  have hLER := Hd.loop.2.2.2.2.2.2.2.2.2.1
  have hLRun := Hd.loop.1
  have hD := Hd.dispatch.2.2.1
  have hNW := runs_regs_of_noWriteIn hLRun (wireBranchBLoopKFBL_noWrite _ _ _ _ _ _)
  have hPres (r : ℕ) (hS : r = 70 ∨ r = 80 ∨ r = 81 ∨ r = 87) :
      Hd.sE.regs r = Hd.st.regs r := by
    have h70 : 70 ≤ r := by omega
    have h1 : Hd.sL.regs r = Hd.sE.regs r := hLER r (by omega) (by omega) (by omega) (by omega)
    have h2 : Hd.sL.regs r = Hd.sF0.regs r := hNW r hS
    have h3 : Hd.sF0.regs r = Hd.sP.regs r :=
      hFrR r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
    have h4 : Hd.sP.regs r = Hd.st.regs r := hPreR r h70
    rw [← h1, h2, h3, h4]
  obtain ⟨_, _, _, _, _, _, _, _, _, h80, h81, _, _, _, _, h87, _⟩ := hD.2
  exact ⟨(hPres 70 (by omega)).trans hD.2.1, (hPres 80 (by omega)).trans h80,
    (hPres 81 (by omega)).trans h81, (hPres 87 (by omega)).trans h87⟩

/-- The registers that the suffix reads, at the state `sX` after the exit (the premises `hRegs`
and `hSel` of `wireBranchBSuffixKFBL_runs`): the exit keeps the registers from `70` on (but `97`
and `99`), the loop invariant at the top of the last pass gives the registers `72`, `73`, `75`,
`94` and `96`, and `sE_regs` gives the others. -/
theorem sX_regs :
    (Hd.sX.regs 4 = Hd.sX.regs 4 ∧ Hd.sX.regs 70 = root ∧ Hd.sX.regs 72 = heap ∧
      Hd.sX.regs 73 = tok.handle ∧ Hd.sX.regs 75 = cfg.P.d ∧
      Hd.sX.regs 80 = heap + 1 + 12 * cfg.P.d ∧
      Hd.sX.regs 81 = heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) ∧ Hd.sX.regs 87 = uIntBuf ∧
      Hd.sX.regs 94 = L) ∧ Hd.sX.regs 96 = Hd.i₀ := by
  have hX (r : ℕ) (h70 : 70 ≤ r) (h97 : r ≠ 97) (h99 : r ≠ 99) : Hd.sX.regs r = Hd.sE.regs r :=
    Hd.exitOut.regs r h70 h97 h99
  obtain ⟨r70, r80, r81, r87⟩ := sE_regs Hd
  obtain ⟨_, _, _, _, _, r72, r73, _, r75, _, _, _, _, _, _, _, r94, _, r96, _⟩ :=
    Hd.loop.2.2.2.2.1.regs
  have hA := Hd.A_eq
  rw [hA] at r72 r73
  refine ⟨⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hX 70 (by omega) (by omega) (by omega)]; exact r70
  · rw [hX 72 (by omega) (by omega) (by omega)]; exact r72
  · rw [hX 73 (by omega) (by omega) (by omega)]; exact r73
  · rw [hX 75 (by omega) (by omega) (by omega)]; exact r75
  · rw [hX 80 (by omega) (by omega) (by omega)]; exact r80
  · rw [hX 81 (by omega) (by omega) (by omega)]; exact r81
  · rw [hX 87 (by omega) (by omega) (by omega)]; exact r87
  · rw [hX 94 (by omega) (by omega) (by omega)]; exact r94
  · rw [hX 96 (by omega) (by omega) (by omega)]; exact r96

end BranchBRunHeadKFBL

end MinCostFlow.MinRatio
