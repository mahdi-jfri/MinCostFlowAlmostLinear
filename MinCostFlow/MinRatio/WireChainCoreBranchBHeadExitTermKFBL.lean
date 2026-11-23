module

public import MinCostFlow.MinRatio.WireChainCoreBranchBHeadExitCasesKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBHeadExitBaseKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBHeadExitHelpModelKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBStaticKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBFrontRepKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBPrefixKFBL
import MinCostFlow.MinRatio.WireStmtNoWriteIn
import MinCostFlow.MinRatio.WireSelectEvalKeyMath
import MinCostFlow.MinRatio.WireChainCoreSyncDefs
import MinCostFlow.Chain.Ordered.Lemma5_11
import WordRAM.Tactic

/-!
# The terminal exit with a batch of the head of Branch B (`WireChainCoreBranchBHeadExitTermKFBL`)

Proves `BranchBHeadExitTermGoalKFBL` (`WireChainCoreBranchBHeadExitCasesKFBL.lean`): from a run
up to the exit of the plain-step loop (`BranchBRunPreExitKFBL`) that stops at level `H.i₀ = d`
with a non-empty terminal batch `H.curUE ≠ []`, produces the post-exit state `sX`, the exit facts
`BranchBExitOutKFBL` (`BranchBExitOutKFBL.of_base_lay` on `BranchBTermExitLayGoalKFBL`), the
terminal-with-batch case of `BranchBExitCaseKFBL`, the post-update model equation
`X = (alg2PreResetState cfg model U H.gVec H.lVec).chain` (via `branchBUpdateLoop_term`), the
forest locations (`BranchBTermExitForestLocGoalKFBL`), and the vacuous rebuilt-block ordering
`BranchBRebuiltOrdKFBL` at `fr + 1 = d + 1`.
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

/-- The plain-step loop of Branch B never writes register `71`. -/
private theorem wireBranchBLoopKFBL_noWrite_71
    (updCore readLSF dgApply copyProc updLen slotProc : ℕ) :
    stmtNoWriteIn (fun r => r = 71)
      (wireBranchBLoopKFBL updCore readLSF dgApply copyProc updLen slotProc) := by
  simp [wireBranchBLoopKFBL, wireBranchBLoopBodyKFBL, wireBranchBStepKFBL,
    wireBranchBStepHeadKFBL, wireBranchBStepTailKFBL, wireBranchBStepTailFrontKFBL,
    wireBranchBCopyListsStmt, wireBranchBReadDescStmt, wireBranchBNextLenStmt,
    wireBranchBSlotStmt, ordCoreUpdateStmt, ordLoadBranchOutStmt, ordCoreReadLSFStmt,
    wireStretchDescCopyStmt, wireGuardCopyWordStmt, stmtNoWriteIn]

/-- Register `71` keeps its dispatch value `0` up to `H.sE`. -/
private theorem preExit_reg71
    (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    H.sE.regs 71 = 0 := by
  have h1 : H.sL.regs 71 = H.sE.regs 71 :=
    H.loop.2.2.2.2.2.2.2.2.2.1 71 (by omega) (by omega) (by omega) (by omega)
  have h2 : H.sL.regs 71 = H.sF0.regs 71 :=
    runs_regs_of_noWriteIn H.loop.1 (wireBranchBLoopKFBL_noWrite_71 _ _ _ _ _ _) 71 rfl
  have h3 : H.sF0.regs 71 = H.sP.regs 71 :=
    H.front.2.2.2.2 71 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have h4 : H.sP.regs 71 = H.st.regs 71 := H.pre.2.2.1 71 (by omega)
  rw [← h1, h2, h3, h4]
  exact H.dispatch.2.2.1.2.2.1

/-- Heap room at `H.sE.regs 4` for the terminal non-empty exit. -/
private theorem preExit_term_room
    (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R) :
    H.sE.regs 4 + (1 + dynGraphSize capLimit capLimit + 5 + capLimit * L +
      levelM cfg.TP cfg.P cfg.P.d * wireCoreLenEdgeSpace
        (ordLevelLwMax L capExp (levelM cfg.TP cfg.P (cfg.P.d - 1)) cfg.N₀) +
      (2 + 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P cfg.P.d)) + lastSpace + 7 < 2 ^ w := by
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
  have hi₀Le : H.i₀ ≤ cfg.P.d := H.loop.2.2.1
  have hsE : H.sE.regs 4 ≤ H.sF0.regs 4 +
      (Finset.range cfg.P.d).sum (fun j => updStepSpace j U.length) := by
    have hL := H.loop.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hSub : Finset.Ico 0 H.i₀ ⊆ Finset.range cfg.P.d := fun j hj =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_Ico.mp hj).2 hi₀Le)
    exact hL.trans (Nat.add_le_add_left (Finset.sum_le_sum_of_subset hSub) _)
  have hTot := H.envA.ops.spaceTotalBranchB U.length
  have hTD := H.envA.ops.termUpdSpaceDom
  have hRoom := H.start.room
  omega

set_option maxHeartbeats 1600000 in
/-- At `H.sE`, the cell `oldPtrs + d` holds the pointer to the old terminal forest, whose graph
remains intact in `H.sE.mem` inside the footprint of the old last level. -/
private theorem preExit_oldLast
    (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    (hS : BranchBStatic cfg.P.d L H.A.handle H.A.table H.A.handleBase H.A.branchBase
      H.A.lvlMTable H.A.levelMeta H.A.rcBase H.A.ucBase H.A.selBase (fun _ => vCap)
      (fun _ => eCap) H.A.gPtr0 H.A.lPtr0 H.A.coreH) :
    ∃ vc ec, DynGraphAt H.sE.mem (H.sE.mem (heap + 1 + 12 * cfg.P.d + cfg.P.d)) vc ec
        (H.st0.lastLSFs H.st0.lastBran).F.F ∧
      ∀ a, H.sE.mem (heap + 1 + 12 * cfg.P.d + cfg.P.d) ≤ a →
        a < H.sE.mem (heap + 1 + 12 * cfg.P.d + cfg.P.d) + dynGraphSize vc ec →
        (LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
          (model.chain.G cfg.P.d).E).foot (H.A.coreH cfg.P.d) tok.termTok a := by
  have hdPos : 0 < cfg.P.d := H.start.modelInv.1.1
  have hUH : uIntBuf ≤ heap := by have := H.start.uLe; have := H.start.edHeap; omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hWire0, hTags0⟩ := H.start.rep0
  obtain ⟨hOwn, hT1, _, _, hT4, hT5, _, _, _, hT9, _, _, hT12, hT13, _, _, _, _, _, _, hT21⟩ :=
    hTags0
  have hLt {x : ℕ} (ht : tok.tag x ≠ 0) : x < uIntBuf := H.start.footLt x (Or.inl (hOwn x ht))
  set lm := solverLevelMetaAddr tok.table cfg.P.d
  set tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  obtain ⟨_, _, _, _, _, _, _, _, ⟨hRootEq, vcOf, ecOf, hLev, _, _⟩, hBatchCaps, hG0'Cap, _⟩ :=
    H.start.modelInv
  have hCapEq (j : ℕ) (hj : j < cfg.P.d) : vcOf j = vCap ∧ ecOf j = eCap :=
    dynGraphAt_caps_eq (hLev j hj).1 (H.start.caps0 j hj)
  have hRootCap : model.extG.n = vCap ∧ tok.rootECap = eCap := by
    have hDG0 := H.start.caps0 0 hdPos
    rw [hRootEq] at hDG0
    exact dynGraphAt_caps_eq hWire0.2.1 hDG0
  have hTagL0 : ∀ x, mem0 lm ≤ x → x < mem0 lm + eCap * L → tok.tag x = 23 + cfg.P.d := by
    intro x h1 h2
    have hL := (hLev 0 hdPos).2.2.2.1
    rw [add_zero, (hCapEq 0 hdPos).2] at hL
    exact hL x h1 h2
  have hLevel0Meta :
      EdgeValuesAt mem0 (mem0 lm) 4 L P (model.chain.G 0).E
        (model.chain.toTreeChain.chainLen model.chain.ℓ 0) ∧
      (∀ x, mem0 lm ≤ x → x < mem0 lm + eCap * L → tok.tag x = 23 + cfg.P.d) ∧
      (∀ e ∈ (model.chain.G 0).E, e < eCap) ∧
      (∀ e ∈ ((model.chain.G 0).applyBatch tr.2.2.2.2).E, e < eCap) ∧
      (∀ u ∈ tr.2.2.2.2, match u with | .insert ei _ _ => ei < eCap | _ => True) := by
    refine ⟨by simpa [lm] using (hLev 0 hdPos).2.1, hTagL0, (H.start.caps0 0 hdPos).2.2.1,
      fun e he => by rw [← hRootCap.2]; exact (hG0'Cap e he).1, fun u hu => ?_⟩
    have hU := hBatchCaps u hu
    cases u with
    | insert ei _ _ => rw [← hRootCap.2]; exact hU
    | delete _ => trivial
    | split _ _ _ _ => trivial
  have hOldT := branchBOldTermForest_of_rep H.start.rep0 H.start.modelInv
  dsimp only at hOldT
  obtain ⟨hTermH0, hTermB0, hTagT1, hTagT2, hDG0, hFoot0⟩ := hOldT
  set lsfHdr := mem0 (tok.termHandle + 1 + model.chain.lastBran)
  set fPtr := mem0 (lsfHdr + 1)
  have hHB0Lt : tok.handle + 18 + cfg.P.d < uIntBuf :=
    hLt (by rw [hT4 cfg.P.d (by omega)]; decide)
  have hBB0Lt : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d < uIntBuf := by
    have h1 : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d = tok.handle + 18 + (2 * cfg.P.d + 1) := by
      omega
    rw [h1]
    exact hLt (by rw [hT4 (2 * cfg.P.d + 1) (by omega)]; decide)
  have hTermHMem : mem (tok.handle + 18 + cfg.P.d) = tok.termHandle := by
    rw [H.start.memEq _ hHB0Lt (by rw [hT4 cfg.P.d (by omega)]; decide)
      (by rw [hT4 cfg.P.d (by omega)]; decide) (by rw [hT4 cfg.P.d (by omega)]; decide)]
    exact hTermH0
  have hTermBMem : mem (tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d) = model.chain.lastBran := by
    have h1 : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d = tok.handle + 18 + (2 * cfg.P.d + 1) := by
      omega
    rw [H.start.memEq _ hBB0Lt (by rw [h1, hT4 (2 * cfg.P.d + 1) (by omega)]; decide)
      (by rw [h1, hT4 (2 * cfg.P.d + 1) (by omega)]; decide)
      (by rw [h1, hT4 (2 * cfg.P.d + 1) (by omega)]; decide)]
    exact hTermB0
  have hT1Lt : tok.termHandle + 1 + model.chain.lastBran < uIntBuf :=
    hLt (by rw [hTagT1]; decide)
  have hT2Lt : lsfHdr + 1 < uIntBuf := hLt (by rw [hTagT2]; decide)
  have hLsfHdrMem : mem (tok.termHandle + 1 + model.chain.lastBran) = lsfHdr :=
    H.start.memEq _ hT1Lt (by rw [hTagT1]; decide) (by rw [hTagT1]; decide) (by rw [hTagT1]; decide)
  have hForestPtrMem : mem (lsfHdr + 1) = fPtr :=
    H.start.memEq _ hT2Lt (by rw [hTagT2]; decide) (by rw [hTagT2]; decide) (by rw [hTagT2]; decide)
  have hSpB := H.envA.ops.spaceTotalBranchB U.length
  have hRoomH := H.start.room
  have hRoomPre : heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 + 3 * U.length +
      U.length * wireTreeSyncEditSpace L + 1 + 3 * L + U.length * wireRefreshOneSpace L < 2 ^ w := by
    omega
  obtain ⟨r4, r70, r71, _, r73, r75, _, r77, r78, _, r80, _, _, r83, _, _, r87, r90, r91, _, _,
    r94, _, _⟩ := H.dispatch.2.2.1
  obtain ⟨out', _, hS1', _, memS1', _, _, _, _, _, rPre', _, _, hh0', _, _, _, _, _, _, _,
    _, hFr1', hFr2', _⟩ :=
    wireBranchBPrefixKFBL_runs (ec0 := eCap) (termHandle := tok.termHandle)
      (lastBran := model.chain.lastBran) (lsfHdr := lsfHdr) (forestPtr := fPtr)
      H.envB.collectP H.envB.emitP H.envB.zeroP H.envA.refAccP H.envA.refOneP H.envA.updLen0P
      H.envA.four H.envA.lPos H.envA.pW H.envA.w18 H.envA.treeImpl H.envA.bindC H.envA.canonC
      H.envA.isNegC H.envA.shiftC H.envA.divC H.envA.addC H.envA.subC H.envA.negC H.envA.copyC
      H.start.rep0 H.start.meta0 H.start.num0 H.start.offInv0 H.start.offBd0 H.start.modelInv
      H.start.logW H.start.capT H.start.refresh H.start.memEq H.start.fresh H.start.trNf
      H.start.batch H.start.small H.start.footLt H.start.gLt H.start.lLt H.start.uLe H.start.edHeap
      hLevel0Meta H.start.zero H.dispatch.1
      ⟨r4, r70, r71, r73, r75, r77, r78, r80, r83, r87, r90, r91, r94⟩
      hTermHMem hTermBMem hLsfHdrMem hForestPtrMem (by omega) (by omega) (by omega) hRoomPre
  have hsPEq : H.sP = out' := (Runs.det H.pre.1 rPre').2.1
  have hR11Lt : root + 11 < uIntBuf := hLt (by rw [hT1 11 (by omega)]; decide)
  have hh0Le : heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ≤ H.hS1 := H.pre.2.2.2.1
  have hhS1Le : H.hS1 + 3 * L ≤ H.heap2 := H.pre.2.2.2.2.2.1
  have hsF0r4 : H.sF0.regs 4 = H.heap2 + (editsPtr - cfg.P.d - uIntBuf) := H.front.2.2.1
  have hSB : H.A.selBase = heap := by rw [H.A_eq]; rfl
  have hCoreH (j : ℕ) (hj : j < cfg.P.d) : H.A.coreH j = tok.coreHandle j := by
    rw [H.A_eq]; show (if j < cfg.P.d then tok.coreHandle j else tok.termHandle) = _; simp [hj]
  have hLoopFr := H.loop.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsLMem : H.sL.mem = H.sE.mem := H.loop.2.2.2.2.2.2.2.2.1
  -- Step 1: `H.sE.mem (oldPtrs + d) = fPtr`
  set opD := heap + 1 + 12 * cfg.P.d + cfg.P.d
  have hOpDP : H.sP.mem opD = fPtr := by
    rw [hsPEq]
    have hOffL0 : opD < mem0 lm ∨ mem0 lm + eCap * L ≤ opD := by
      by_contra hc
      have := hLt (x := opD) (by rw [hTagL0 opD (by omega) (by omega)]; omega)
      omega
    have hNotSlot : ∀ ei < tok.intCap, ei ∉ (model.chain.G 0).E →
        opD ≠ tok.slots + ei ∧ opD ≠ tok.edgeThresholds + ei ∧ opD ≠ tok.edgeRecords + ei := by
      intro ei hei _
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have := hLt (x := tok.slots + ei) (by rw [hT9 ei hei]; decide); omega
      · have := hLt (x := tok.edgeThresholds + ei) (by rw [hT12 ei hei]; decide); omega
      · have := hLt (x := tok.edgeRecords + ei) (by rw [hT13 ei hei]; decide); omega
    rw [hFr2' opD (by omega) hNotSlot hOffL0,
      hFr1' opD (by omega) (by omega) (fun hu => absurd hu (by omega)), Function.update_self]
  have hOpDF : H.sF0.mem opD = fPtr := (H.front.2.2.2.1 opD (by omega)).trans hOpDP
  have hOpDE : H.sE.mem opD = fPtr := by
    rw [← hsLMem, hLoopFr opD (by omega)
      (fun j hj hf => by
        rw [hCoreH j hj] at hf
        have := hLt (x := opD) (by rw [hT21 j hj opD hf]; omega); omega)
      (fun j hj => ⟨Or.inr (by have := hS.gLt j hj; rw [hSB] at this; omega),
        Or.inr (by have := hS.lLt j hj; rw [hSB] at this; omega)⟩)
      (fun j hj => by have := hS.ucLt; rw [hSB] at this; omega)
      (Or.inr (by rw [hSB]; omega))]
    exact hOpDF
  -- Step 2: `H.sE.mem a = mem0 a` on the old terminal forest graph (tag 19)
  have hAgree : ∀ a, fPtr ≤ a → a < fPtr + dynGraphSize tok.vcLast tok.ecLast →
      H.sE.mem a = mem0 a := by
    intro a ha1 ha2
    have hTag19 : tok.tag a = 19 := (hFoot0 a ha1 ha2).2.2
    have haU : a < uIntBuf := hLt (by rw [hTag19]; decide)
    have hMem0 : mem a = mem0 a :=
      H.start.memEq a haU (by rw [hTag19]; decide) (by rw [hTag19]; decide) (by rw [hTag19]; decide)
    have hOffL0 : a < mem0 lm ∨ mem0 lm + eCap * L ≤ a := by
      by_contra hc
      have := hTagL0 a (by omega) (by omega); omega
    have hNotSlot : ∀ ei < tok.intCap, ei ∉ (model.chain.G 0).E →
        a ≠ tok.slots + ei ∧ a ≠ tok.edgeThresholds + ei ∧ a ≠ tok.edgeRecords + ei := by
      intro ei hei _
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have := hT9 ei hei; rw [← h, hTag19] at this; omega
      · have := hT12 ei hei; rw [← h, hTag19] at this; omega
      · have := hT13 ei hei; rw [← h, hTag19] at this; omega
    have hNe11 : a ≠ root + 11 := fun h => by
      have := hT1 11 (by omega); rw [← h, hTag19] at this; omega
    have hP : H.sP.mem a = mem0 a := by
      rw [hsPEq, hFr2' a (by omega) hNotSlot hOffL0,
        hFr1' a (by omega) hNe11 (fun _ => by rw [hTag19]; decide),
        Function.update_of_ne (by omega), hMem0]
    have hF : H.sF0.mem a = mem0 a := (H.front.2.2.2.1 a (by omega)).trans hP
    rw [← hsLMem, hLoopFr a (by omega)
      (fun j hj hf => by
        rw [hCoreH j hj] at hf
        have := hT21 j hj a hf; omega)
      (fun j hj => by
        obtain ⟨hv, he⟩ := hCapEq j hj
        refine ⟨?_, ?_⟩
        · by_contra hc
          have hG := (hLev j hj).2.2.2.2
          rw [hv, he] at hG
          have hA : H.A.gPtr0 j = mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) := by
            rw [H.A_eq]; rfl
          rw [hA] at hc
          have ht := (hG a (by omega) (by omega)).1
          split_ifs at ht <;> omega
        · by_contra hc
          have hL := (hLev j hj).2.2.2.1
          rw [he] at hL
          have hA : H.A.lPtr0 j = mem0 (solverLevelMetaAddr tok.table cfg.P.d + j) := by
            rw [H.A_eq]; rfl
          rw [hA] at hc
          have ht := hL a (by omega) (by omega)
          omega)
      (fun j hj heq => by
        have hA : H.A.ucBase = tok.levelsEnd + 3 * (cfg.P.d + 1) := by rw [H.A_eq]; rfl
        rw [hA] at heq
        have ht := hT5 (3 * (cfg.P.d + 1) + j) (by omega)
        rw [← add_assoc, ← heq, hTag19] at ht; omega)
      (Or.inl (by rw [hSB]; omega))]
    exact hF
  refine ⟨tok.vcLast, tok.ecLast, ?_, ?_⟩
  · rw [hOpDE, H.st0_eq]
    exact dynGraphAt_of_agree hDG0 hAgree
  · intro a ha1 ha2
    rw [hOpDE] at ha1 ha2
    have hFoot := hFoot0 a ha1 ha2
    have hTermH : H.A.coreH cfg.P.d = tok.termHandle := by
      rw [H.A_eq]; show (if cfg.P.d < cfg.P.d then tok.coreHandle cfg.P.d else tok.termHandle) = _
      simp
    change H.A.coreH cfg.P.d ≤ a ∧ a < tok.termTok
    rw [hTermH]
    exact ⟨hFoot.1, hFoot.2.1⟩

/-- Model-derived premises of `BranchBTermExitLayGoalKFBL` at the terminal non-empty exit:
`hLastImpl`, `hHm`, `hRotW`, `hOldLastFCap`, `hKPos`, and `hNewFCap`. -/
private theorem preExit_term_modelPremises
    (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
      lastMul intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc
      initTree bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub
      copy dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit
      coreLenProc edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen
      slotProc collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R)
    (hi₀ : H.i₀ = cfg.P.d) (hneU : H.curUE ≠ []) :
    let X := (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g' 0 cfg.P.d H.chE
      H.curGE H.curUE H.curEncE).1
    (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P H.curGE.E).Implements w p lastInit
        opLast
        (lastLevelRuntimeMachineContract fmt L cfg.L H.curGE vCap eCap lastMul stretchPrec
          lastAlloc) ∧
      H.curGE.m ≤ levelM cfg.TP cfg.P cfg.P.d ∧
      ordRotWords (chainLevelOrdAbs H.chE (cfg.P.d - 1)) (H.chE.bran (cfg.P.d - 1)) ≤
        1 + 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P cfg.P.d ∧
      (∀ e ∈ (H.st0.lastLSFs H.st0.lastBran).F.F.E, e < tok.intCap) ∧
      0 < X.lastK ∧
      (∀ e ∈ (X.lastLSFs X.lastBran).F.F.E, e < tok.intCap) := by
  intro X
  have hdPos : 0 < cfg.P.d := H.start.modelInv.1.1
  have hXEq : X = (alg2PreResetState cfg model U
      (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain := by
    rw [← H.gVec_eq, ← H.lVec_eq]
    exact (H.modelEq_term hi₀).symm
  have hXGd : X.G cfg.P.d = H.curGE := by
    dsimp only [X]
    simp [Chain.Ordered.updateLoop, ite_eq_right hneU]
  have hXG0 : X.G 0 = H.G1 := by
    rw [hXEq, H.G1_eq, H.Uint_eq]
    dsimp only [alg2PreResetState]
    rw [(Chain.Ordered.update_G0_ℓ cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain _ _ _).1,
      ite_eq_right H.start.noFire]
  have hFactsX : ShiftLoopLevelFacts cfg X := hXEq ▸ H.start.modelInvKFBL.2.1
  have hcurGm : H.curGE.m ≤ m := by
    rw [← hXGd]
    have hLe0 : (X.G cfg.P.d).m ≤ (X.G 0).m := hFactsX.2.2.2 cfg.P.d le_rfl
    rw [hXG0, H.G1_eq, H.Uint_eq] at hLe0
    have hFresh0 : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt
        model.nextFresh := H.start.rep0.2.2.2.2.1
    have hTr := translateBatch_preserves U model.extG (model.chain.G 0) model.extToInt
      model.intToExt model.nextFresh hFresh0 H.start.refresh.1
    have hE1 : ((model.chain.G 0).applyBatch
        (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2).E =
        (model.extG.applyBatch U).E.image
          (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.1 := by
      rw [← hTr.1]; exact hTr.2.1.hE
    have hCard : ((model.chain.G 0).applyBatch
        (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2).m ≤
        model.extG.m := by
      unfold MGraph.m
      rw [hE1, H.start.refresh.2.1]
      exact Finset.card_image_le
    exact (hLe0.trans hCard).trans H.start.extM.le
  have hcurGLvl : H.curGE.m ≤ levelM cfg.TP cfg.P cfg.P.d := by
    rw [← hXGd]; exact hXEq ▸ H.start.modelInvKFBL.2.2.2.2.2.2.2.2.2.1
  have hcurGn : H.curGE.n ≤ H.curGE.m + 1 := by
    rw [← hXGd]; exact hFactsX.1 cfg.P.d le_rfl
  have hcurGConn : ∀ u ∈ H.curGE.V, ∀ v ∈ H.curGE.V, H.curGE.Connected u v := by
    rw [← hXGd]; exact hXEq ▸ H.start.modelInvKFBL.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hLastImpl :
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P H.curGE.E).Implements w p
        lastInit opLast
        (lastLevelRuntimeMachineContract fmt L cfg.L H.curGE vCap eCap lastMul stretchPrec
          lastAlloc) := by
    have h := H.envA.lastImpl H.curGE hcurGm hcurGLvl hcurGn hcurGConn
    rwa [H.envA.prec] at h
  have hRotW : ordRotWords (chainLevelOrdAbs H.chE (cfg.P.d - 1)) (H.chE.bran (cfg.P.d - 1)) ≤
      1 + 2 * cfg.N₀ + 2 * levelM cfg.TP cfg.P cfg.P.d := by
    have hScEq : X.scState (cfg.P.d - 1) = H.chE.scState (cfg.P.d - 1) := by
      dsimp only [X]; simp [Chain.Ordered.updateLoop, ite_eq_right hneU]
    have hBrEq : X.bran (cfg.P.d - 1) = H.chE.bran (cfg.P.d - 1) := by
      dsimp only [X]; simp [Chain.Ordered.updateLoop, ite_eq_right hneU]
    have hRotEq : ordRotWords (chainLevelOrdAbs H.chE (cfg.P.d - 1)) (H.chE.bran (cfg.P.d - 1)) =
        ordRotWords (chainLevelOrdAbs X (cfg.P.d - 1)) (X.bran (cfg.P.d - 1)) := by
      unfold ordRotWords chainLevelOrdAbs; dsimp only; rw [hScEq, hBrEq]
    rw [hRotEq]
    have h1 : ordRotWords (chainLevelOrdAbs X (cfg.P.d - 1)) (X.bran (cfg.P.d - 1)) ≤
        1 + 2 * (X.G (cfg.P.d - 1 + 1)).n + 2 * (X.G (cfg.P.d - 1 + 1)).m :=
      hXEq ▸ H.start.modelInvKFBL.2.2.2.2.1 (cfg.P.d - 1) (by omega)
    have hNLe : (X.G cfg.P.d).n ≤ cfg.N₀ := by
      have hN := hXEq ▸ H.start.modelInvKFBL.2.2.2.1 cfg.P.d le_rfl
      rw [hFactsX.2.2.1] at hN; exact hN
    have hMLe : (X.G cfg.P.d).m ≤ levelM cfg.TP cfg.P cfg.P.d := by
      rw [hXGd]; exact hcurGLvl
    rw [show cfg.P.d - 1 + 1 = cfg.P.d by omega] at h1
    omega
  have hOldLastFCap : ∀ e ∈ (H.st0.lastLSFs H.st0.lastBran).F.F.E, e < tok.intCap := by
    intro e he
    rw [H.st0_eq] at he
    have he0 : e ∈ (model.chain.G 0).E :=
      H.start.modelInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 he
    have hWireG := H.start.rep0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
    have hLtRoot : e < tok.rootECap := hWireG.2.2.1 e he0
    have hRootLe : tok.rootECap ≤ tok.intCap := H.start.modelInv.2.1.2.2
    omega
  have hKPos : 0 < X.lastK := hXEq ▸ H.start.modelInv.2.2.2.2.2.2.1.2
  have hNewFCap : ∀ e ∈ (X.lastLSFs X.lastBran).F.F.E, e < tok.intCap := by
    intro e he
    have he0 : e ∈ (X.G 0).E :=
      (hXEq ▸ H.start.modelInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) he
    rw [hXG0, H.G1_eq, H.Uint_eq] at he0
    exact (H.start.modelInv.2.2.2.2.2.2.2.2.2.2.1 e he0).2
  exact ⟨hLastImpl, hcurGLvl, hRotW, hOldLastFCap, hKPos, hNewFCap⟩

end Helpers

/-- **Proof of `BranchBHeadExitTermGoalKFBL`.** At the terminal exit with a non-empty batch
(`H.i₀ = cfg.P.d`, `H.curUE ≠ []`), runs `BranchBTermExitLayGoalKFBL` and
`BranchBTermExitForestLocGoalKFBL` at `fr = cfg.P.d` to produce `BranchBExitOutKFBL`,
`BranchBExitCaseKFBL`, the post-update model equality via `branchBUpdateLoop_term`,
`BranchBExitForestLocKFBL`, and the vacuous `BranchBRebuiltOrdKFBL` at `fr + 1 = cfg.P.d + 1`. -/
theorem branchBHeadExitTermGoalKFBL_proved : BranchBHeadExitTermGoalKFBL := by
  intro w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
    forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy
    isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
    updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
    signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
    collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace coreFixed toolMul fmt
    cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Ginit
    reembFn Rcore p opTree opCore opLast stepCap root uIntBuf editsPtr editWords g l heap pos ω
    mem0 mem model tok U B R _ hTermLay _ hTermLoc H hi₀ hneU
  have hdPos : 0 < cfg.P.d := H.start.modelInv.1.1
  have hUH : uIntBuf ≤ heap := H.heap_order.1
  have hS : BranchBStatic cfg.P.d L H.A.handle H.A.table H.A.handleBase H.A.branchBase
      H.A.lvlMTable H.A.levelMeta H.A.rcBase H.A.ucBase H.A.selBase (fun _ => vCap)
      (fun _ => eCap) H.A.gPtr0 H.A.lPtr0 H.A.coreH := by
    rw [H.A_eq]
    exact (branchBStatic_of_rep (heapFloor := H.heap2) H.start.rep0 H.start.meta0
      H.start.caps0 H.start.modelInv H.start.footLt hUH).1
  have hSB : H.A.selBase = heap := by rw [H.A_eq]; rfl
  have hHF : H.A.heapFloor = H.heap2 := by rw [H.A_eq]; rfl
  have hOldLo : H.A.selBase + 1 + 12 * cfg.P.d ≤ heap + 1 + 12 * cfg.P.d := by rw [hSB]
  have hOldNew : heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) ≤
      heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) := le_rfl
  have hNewHi : heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) + (cfg.P.d + 1) ≤ H.A.heapFloor := by
    obtain ⟨_, hh0, hhS1, _⟩ := H.heap_order
    rw [hHF]; omega
  have hLvlM : ∀ j < cfg.P.d, H.st0.lvlM j = levelM cfg.TP cfg.P j := fun j _ => by
    have h1 : H.st0.lvlM = model.chain.lvlM := by rw [H.st0_eq]
    rw [h1, H.start.modelInvKFBL.1.2.1]
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
  have h71 : H.sE.regs 71 = 0 := preExit_reg71 H
  have h81 : H.sE.regs 81 = heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) := H.sE_regs.2.2.1
  have hRoom := preExit_term_room H
  have hOldLast := preExit_oldLast H hS
  obtain ⟨hLastImpl, hHm, hRotW, hOldLastFCap, hKPos, hNewFCap⟩ :=
    preExit_term_modelPremises H hi₀ hneU
  set X := (Chain.Ordered.updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ H.ℓ' H.g' 0 cfg.P.d H.chE
    H.curGE H.curUE H.curEncE).1
  obtain ⟨out, cost, h1, y, termTokN, hRun, hh1Lo, hh1Hi, hR4, hBase, hCost, hT, hLay⟩ :=
    hTermLay (lastAlloc := lastAlloc) (opLast := opLast) (ω := ω) (st := H.sL)
      (nextM := levelM cfg.TP cfg.P cfg.P.d) (lastMul := lastMul) (lastSpace := lastSpace)
      (oldPtrs := heap + 1 + 12 * cfg.P.d) (newPtrs := heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1))
      (intCap := tok.intCap)
      H.envB.loop hS hOldLo hOldNew hNewHi rfl hLvlM hdPos hInv hM
      H.loop.2.2.2.2.2.2.2.2.1 H.loop.2.2.2.2.2.2.2.2.2.1 hneU H.envA.capLim H.envA.coreLenP
      hLastImpl H.envA.ops.lastSpaceDom H.envA.lW H.envA.pW H.envA.width hHm hRotW hRoom
      h71 h81 hOldLast hOldLastFCap hKPos hNewFCap
  have hLoc :=
    hTermLoc (lastAlloc := lastAlloc) (opLast := opLast) (ω := ω) (st := H.sL)
      (nextM := levelM cfg.TP cfg.P cfg.P.d) (lastMul := lastMul) (lastSpace := lastSpace)
      (oldPtrs := heap + 1 + 12 * cfg.P.d) (newPtrs := heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1))
      (intCap := tok.intCap)
      H.envB.loop hS hOldLo hOldNew hNewHi rfl hLvlM hdPos hInv hM
      H.loop.2.2.2.2.2.2.2.2.1 H.loop.2.2.2.2.2.2.2.2.2.1 hneU H.envA.capLim H.envA.coreLenP
      hLastImpl H.envA.ops.lastSpaceDom H.envA.lW H.envA.pW H.envA.width hHm hRotW hRoom
      h71 h81 hOldLast hOldLastFCap hKPos hNewFCap out cost hRun
  refine ⟨out, cost, cfg.P.d, vCap, eCap, termTokN, hT,
    (fun j => if j = cfg.P.d - 1 then y else H.tokE j), X, ?_, ?_, ?_, ?_, ?_⟩
  · exact BranchBExitOutKFBL.of_base_lay hBase hLay
  · exact Or.inr (Or.inl ⟨hi₀, hneU, rfl, rfl, rfl, rfl, ⟨y, rfl⟩, hRun,
      ⟨h1, hh1Lo, hh1Hi, hR4⟩, hCost⟩)
  · exact (H.modelEq_term hi₀).symm
  · simp only [le_rfl, ↓reduceIte]
    exact hLoc
  · exact ⟨fun _ h1 h2 => absurd h2 (by omega), fun _ _ h1 h2 h3 => absurd h3 (by omega)⟩

end MinCostFlow.MinRatio
