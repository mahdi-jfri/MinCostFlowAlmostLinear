module

public import MinCostFlow.MinRatio.WireChainCoreBranchBHeadExitCasesKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBStaticKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBFrontRepKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBModelKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBExitOutKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBForestLocGoalKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBMetaDisjKFBL
import MinCostFlow.MinRatio.WireChainCoreSyncDefs
import MinCostFlow.MinRatio.WireStmtNoWriteIn

/-!
# The empty terminal exit of the head of Branch B (`WireChainCoreBranchBHeadExitEmptyKFBL`)

Proves `BranchBHeadExitEmptyGoalKFBL`
(`MinRatio/WireChainCoreBranchBHeadExitCasesKFBL.lean`): from a run of Branch B up to the exit of
its plain-step loop (`BranchBRunPreExitKFBL`) stopping at `i₀ = d` with an empty batch
`curUE = []`, the terminal exit produces all five exit fields of `BranchBRunHeadKFBL` at
`fr = d + 1` with unchanged tokens and unchanged last level:

* `BranchBExitOutKFBL` and the third disjunct of `BranchBExitCaseKFBL`, from
  `wireBranchBTermEmpty_exitOut`;
* `X = (alg2PreResetState cfg model U H.gVec H.lVec).chain`, from the `updateLoop` equation of
  `H.loop` and `branchBUpdateLoop_term`;
* `BranchBExitForestLocKFBL`, from `BranchBExitForestLocKFBL.of_nil` (both forest lists are empty
  since `¬ (d + 1 ≤ d)`);
* `BranchBRebuiltOrdKFBL` at `fr + 1 = d + 2`, vacuously since `d + 2 ≤ j → j < d` is false.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

section Helpers

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

/-- The plain-step loop of Branch B never writes registers `71` or `81`. -/
private theorem wireBranchBLoopKFBL_noWrite71_81
    (updCore readLSF dgApply copyProc updLen slotProc : ℕ) :
    stmtNoWriteIn (fun r => r = 71 ∨ r = 81)
      (wireBranchBLoopKFBL updCore readLSF dgApply copyProc updLen slotProc) := by
  simp [wireBranchBLoopKFBL, wireBranchBLoopBodyKFBL, wireBranchBStepKFBL,
    wireBranchBStepHeadKFBL, wireBranchBStepTailKFBL, wireBranchBStepTailFrontKFBL,
    wireBranchBCopyListsStmt, wireBranchBReadDescStmt, wireBranchBNextLenStmt,
    wireBranchBSlotStmt, ordCoreUpdateStmt, ordLoadBranchOutStmt, ordCoreReadLSFStmt,
    wireStretchDescCopyStmt, wireGuardCopyWordStmt, stmtNoWriteIn]

/-- Registers `71` and `81` keep their dispatch values at `H.sE`. -/
private theorem preExit_regs71_81
    (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace coreFixed
      toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace allocation
      lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf editsPtr editWords
      g l heap pos ω mem0 mem model tok U B R) :
    H.sE.regs 71 = 0 ∧ H.sE.regs 81 = heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) := by
  have hPreR := H.pre.2.2.1
  have hFrR := H.front.2.2.2.2
  have hLER := H.loop.2.2.2.2.2.2.2.2.2.1
  have hNW := runs_regs_of_noWriteIn H.loop.1 (wireBranchBLoopKFBL_noWrite71_81 _ _ _ _ _ _)
  have hPres (r : ℕ) (hS : r = 71 ∨ r = 81) : H.sE.regs r = H.st.regs r := by
    have h70 : 70 ≤ r := by omega
    have h1 : H.sL.regs r = H.sE.regs r := hLER r (by omega) (by omega) (by omega) (by omega)
    have h2 : H.sL.regs r = H.sF0.regs r := hNW r hS
    have h3 : H.sF0.regs r = H.sP.regs r :=
      hFrR r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
    have h4 : H.sP.regs r = H.st.regs r := hPreR r h70
    rw [← h1, h2, h3, h4]
  obtain ⟨_, _, h71d, _, _, _, _, _, _, _, _, h81d, _⟩ := H.dispatch.2.2.1
  exact ⟨(hPres 71 (Or.inl rfl)).trans h71d, (hPres 81 (Or.inr rfl)).trans h81d⟩

/-- The heap pointer `H.sE.regs 4` fits in a machine word (`< 2 ^ w`). -/
private theorem preExit_room
    (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace coreFixed
      toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace allocation
      lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf editsPtr editWords
      g l heap pos ω mem0 mem model tok U B R) :
    H.sE.regs 4 < 2 ^ w := by
  have hhS1 : H.hS1 ≤ heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 +
      (3 * U.length + U.length * wireTreeSyncEditSpace L) := by
    have := H.pre.2.2.2.2.1; omega
  have hheap2 : H.heap2 ≤ H.hS1 + 3 * L + U.length * wireRefreshOneSpace L :=
    H.pre.2.2.2.2.2.2.1
  have hsF0 : H.sF0.regs 4 = H.heap2 + (editsPtr - cfg.P.d - uIntBuf) := H.front.2.2.1
  have hbW : editsPtr - cfg.P.d - uIntBuf ≤ 4 * U.length + 1 := by
    have hEdits := branchBLevel0Edits_of_rep H.start.rep0 H.start.caps0 H.start.modelInv
      H.start.refresh
    have hLe := smallBatchAt_words_le_edgeOnly H.start.small hEdits.2.2.1
    have hFresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt
        model.nextFresh := H.start.rep0.2.2.2.2.1
    have hLen : (translateBatch model.extG model.extToInt model.intToExt
        model.nextFresh U).2.2.2.2.length = U.length :=
      (translateBatch_preserves U model.extG (model.chain.G 0) model.extToInt model.intToExt
        model.nextFresh hFresh H.start.refresh.1).2.2.2.2.1
    rw [hLen] at hLe; exact hLe
  obtain ⟨_, _, hi₀Le, _, _, _, _, _, _, _, _, _, hsELe, _⟩ := H.loop
  have hsE : H.sE.regs 4 ≤ H.sF0.regs 4 +
      (Finset.range cfg.P.d).sum (fun j => updStepSpace j U.length) := by
    have hSub : Finset.Ico 0 H.i₀ ⊆ Finset.range cfg.P.d := fun j hj =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp hj).2 hi₀Le)
    exact hsELe.trans (Nat.add_le_add_left (Finset.sum_le_sum_of_subset hSub) _)
  have hTot := H.envA.ops.spaceTotalBranchB U.length
  have hRoom := H.start.room
  omega

/-- The active terminal-branch table slot and its forest-pointer word lie below `H.A.selBase`. -/
private theorem preExit_term_addrs
    (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace coreFixed
      toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace allocation
      lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf editsPtr editWords
      g l heap pos ω mem0 mem model tok U B R) :
    H.A.coreH cfg.P.d + 1 + H.chE.lastBran < H.A.selBase ∧
      H.sE.mem (H.A.coreH cfg.P.d + 1 + H.chE.lastBran) + 1 < H.A.selBase := by
  have hInv := H.loop.2.2.2.2.1
  have hLastK : H.chE.lastK = model.chain.lastK :=
    hInv.modelFrame.2.2.1.trans (by rw [H.st0_eq])
  have hLastBran : H.chE.lastBran = model.chain.lastBran :=
    hInv.modelFrame.2.2.2.2.1.trans (by rw [H.st0_eq])
  obtain ⟨_, _, _, _, _, _, ⟨hLastLt0, _⟩, _⟩ := H.start.modelInv
  have hLastLt : H.chE.lastBran < H.chE.lastK := by rw [hLastBran, hLastK]; exact hLastLt0
  obtain ⟨hCnt, _, _, hBranches⟩ := hInv.term.1
  obtain ⟨hBW, _⟩ := hBranches H.chE.lastBran hLastLt
  obtain ⟨hB1, hB2, _⟩ := hBW
  dsimp only at hCnt hB1 hB2
  exact ⟨(hInv.term.2 _ ⟨by omega, by omega⟩).1, (hInv.term.2 _ ⟨by omega, by omega⟩).1⟩

end Helpers

/-- **Proof of `BranchBHeadExitEmptyGoalKFBL`.** At the terminal exit with an empty batch
(`H.i₀ = cfg.P.d`, `H.curUE = []`), `wireBranchBTermEmpty_exitOut` produces `sX`, `cX`,
`BranchBExitOutKFBL`, and the empty-batch disjunct of `BranchBExitCaseKFBL` at `fr = cfg.P.d + 1`;
the model equality follows from `H.loop` and `branchBUpdateLoop_term`; the forest locations hold
by `BranchBExitForestLocKFBL.of_nil`; and `BranchBRebuiltOrdKFBL` holds vacuously at `d + 2`. -/
theorem branchBHeadExitEmptyGoalKFBL_proved : BranchBHeadExitEmptyGoalKFBL := by
  intro w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
    forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy
    isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
    updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
    signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
    collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace coreFixed toolMul fmt
    cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Ginit
    reembFn Rcore p opTree opCore opLast stepCap root uIntBuf editsPtr editWords g l heap pos ω
    mem0 mem model tok U B R _ _ _ _ H hi₀ hEmpty
  have hUH : uIntBuf ≤ heap := by have := H.start.uLe; have := H.start.edHeap; omega
  have hS : BranchBStatic cfg.P.d L H.A.handle H.A.table H.A.handleBase H.A.branchBase
      H.A.lvlMTable H.A.levelMeta H.A.rcBase H.A.ucBase H.A.selBase (fun _ => vCap)
      (fun _ => eCap) H.A.gPtr0 H.A.lPtr0 H.A.coreH := by
    rw [H.A_eq]
    exact (branchBStatic_of_rep (heapFloor := H.heap2) H.start.rep0 H.start.meta0 H.start.caps0
      H.start.modelInv H.start.footLt hUH).1
  have hSB : H.A.selBase = heap := by rw [H.A_eq]; rfl
  have hHF : H.A.heapFloor = H.heap2 := by rw [H.A_eq]; rfl
  have hOldLo : H.A.selBase + 1 + 12 * cfg.P.d ≤ heap + 1 + 12 * cfg.P.d := by rw [hSB]
  have hOldNew : heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) ≤
      heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) := le_rfl
  have hNewHi : heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) + (cfg.P.d + 1) ≤ H.A.heapFloor := by
    have hh0 := H.pre.2.2.2.1
    have hhS1 := H.pre.2.2.2.2.2.1
    rw [hHF]; omega
  have hInv : BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt)
      (RL := LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
        (model.chain.G cfg.P.d).E) reembFn H.A
      (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ j) H.ℓ' cfg.N₀
      (fun j => (H.C j).1) (fun j => (H.C j).2.1) (fun j => (H.C j).2.2) H.st0 tok.termTok
      cfg.P.d H.chE H.curGE H.curUE H.curEditsE H.oldOrdE H.sE H.tokE H.bE H.bWE H.eE H.eWE
      H.levelU H.levelUS H.D := hi₀ ▸ H.loop.2.2.2.2.1
  have hM : UpdateLoopModelInv w L P wordExp stretchPrec (fun _ => vCap) (fun _ => eCap)
      (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ j) H.ℓ' H.g' 0 cfg.P.d H.chE
      H.curGE H.curUE H.curEncE H.oldOrdE := by
    have hM0 := H.loop.2.2.2.2.2.1
    rw [hi₀, Nat.sub_self] at hM0
    exact hM0
  have hE0 : (H.st0.G cfg.P.d).E = (model.chain.G cfg.P.d).E := by rw [H.st0_eq]
  obtain ⟨h71, h81⟩ := preExit_regs71_81 H
  obtain ⟨hTW, hLW⟩ := preExit_term_addrs H
  have hRoom : H.sE.regs 4 < 2 ^ w := preExit_room H
  obtain ⟨sX, cX, hRun, hcX, hR4, hPhi, hOut⟩ :=
    wireBranchBTermEmpty_exitOut (readGraph := opCore 3) (readLSF := opCore 2)
      (coreLenProc := coreLenProc) (readOrd := opCore 5) (lastInit := lastInit)
      (intCap := tok.intCap) (p := p) (ω := ω) (st := H.sL)
      (lsfHdr := H.sE.mem (H.A.coreH cfg.P.d + 1 + H.chE.lastBran))
      (forestPtr := H.sE.mem (H.sE.mem (H.A.coreH cfg.P.d + 1 + H.chE.lastBran) + 1))
      H.envB.loop.loc hS hOldLo hOldNew hNewHi hInv hM H.loop.2.2.2.2.2.2.2.2.1
      H.loop.2.2.2.2.2.2.2.2.2.1 hEmpty hE0 h71 h81 rfl rfl hTW hLW hRoom
  let X := (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g' 0 cfg.P.d H.chE
    H.curGE H.curUE H.curEncE).1
  have hModelEq : X = (alg2PreResetState cfg model U H.gVec H.lVec).chain := by
    have hUpd := H.loop.2.2.2.2.2.2.2.1
    rw [hi₀, branchBUpdateLoop_term] at hUpd
    dsimp only [X, alg2PreResetState, Chain.Ordered.algorithm1_update]
    rw [← H.Uint_eq, ← H.g'_eq, ← H.ℓ'_eq, ← H.G1_eq, ← H.st0_eq]
    exact hUpd.symm
  refine ⟨sX, cX, cfg.P.d + 1, tok.vcLast, tok.ecLast, tok.termTok, H.sE.regs 4, H.tokE, X,
    hOut, Or.inr (Or.inr ⟨hi₀, hEmpty, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hRun, hcX, hR4, hPhi⟩),
    hModelEq, ?_, ⟨fun _ h1 h2 => by omega, fun _ _ h1 h2 h3 => by omega⟩⟩
  simp only [Nat.not_succ_le_self, ↓reduceIte]
  exact BranchBExitForestLocKFBL.of_nil

end MinCostFlow.MinRatio

end
