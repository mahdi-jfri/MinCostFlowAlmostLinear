module

public import MinCostFlow.MinRatio.WireChainCoreBranchBTopKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBLevelLocKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBRunTreeKFBL
import WordRAM.Tactic

/-!
# The own fields of Branch B from two smaller goals (`WireChainCoreBranchBOwnKFBL`)

`BranchBOwnGoalKFBL` asks for the fields of `BranchBSufOutKFBL` that are not cost, space or model
fields. Most of them follow from the facts of the run itself (`WireChainCoreBranchBRunFactsKFBL`):
the cores, the branch words, the select word and the cells. Two groups are stated as separate
propositions:
* `BranchBLevelLocGoalKFBL`: the new last level, the level graphs and the length blocks after the
  exit lie in the zones the suffix keeps (`BranchBExitLevelLocKFBL`). With it, `own_levels` gives
  the fields `lastRep`, `graphs` and `lens`.
* `BranchBOwnRestGoalKFBL`: the edge accounts after the suffix (the fields `canon`, `thrLoc`,
  `recLoc` and `thrRecDisj`).
The field `phase` comes from the tree state that the suffix leaves (`own_phase`).
`branchBOwnGoal_of_goals` proves `BranchBOwnGoalKFBL` from these two goals.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The fields of `BranchBOwnFieldsKFBL` on the edge accounts, with the same names and
parameters. -/
structure BranchBOwnRestFieldsKFBL
    {w L P m V psi k epsExp drainUnit capExp vCap eCap : ℕ} {cfg : Alg2Config}
    {reembFn : ToolReembFn cfg.T} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (coreSpace coreFixed : ℕ → ℕ) (toolMul treeMul : ℕ)
    (root uIntBuf heap : ℕ) (mem0 mem : ℕ → ℕ) (model : Alg2State cfg)
    (tok : SolverToken cfg L Rcore) (U : List Update) (gVec lVec : ℕ → ℝ) (B R : ℤ)
    (heap2 hS hT hX fr : ℕ) (levelU levelUS : ℕ → List Update) (D : ℕ → LevelDiffLists)
    (tokN : ℕ → Rcore.τ) (vcL ecL termTokN : ℕ) (curTree : PathTreeState)
    (curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ) (offCnt : ℕ)
    (canonVal : ℕ → PathEdgeValue) (out : State) (nextHeap cost : ℕ) : Prop where
  canon :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    ∀ e ∈ model.extG.E,
      let ei := tr.2.1 e
      let v := canonVal ei
      PathIntAt out.mem (out.mem (tok.edgeThresholds + ei)) 4 L
        (detectorThreshold P cfg.ε (lVec e)) ∧
      (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
      (v.originalGradient : ℝ) / (2 : ℝ) ^ P = gVec e ∧
      (v.length : ℝ) / (2 : ℝ) ^ P = lVec e ∧
      ∃ acc : ℤ, (acc : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
        v.detector = acc - detectorThreshold P cfg.ε (lVec e)
  thrLoc :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    ∀ e ∈ model.extG.E, ∀ j < L,
      let a := out.mem (tok.edgeThresholds + tr.2.1 e) + j
      (a < uIntBuf → tok.tag a = 17) ∧
      (uIntBuf ≤ a → heap + 1 + 12 * cfg.P.d ≤ a ∧ a < heap2) ∧
      ¬ (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok a
  recLoc : ∀ ei ∈ ((alg2PreResetState cfg model U gVec lVec).chain.G 0).E,
    ei ∉ (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E →
    ∀ j < 2 + 4 * L, uIntBuf ≤ out.mem (tok.edgeRecords + ei) + j →
      (heap + 1 + 12 * cfg.P.d ≤ out.mem (tok.edgeRecords + ei) + j ∧
        out.mem (tok.edgeRecords + ei) + j < heap2) ∨
      (hX ≤ out.mem (tok.edgeRecords + ei) + j ∧ out.mem (tok.edgeRecords + ei) + j < nextHeap)
  thrRecDisj :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    ∀ e₁ ∈ model.extG.E, ∀ e₂ ∈ model.extG.E,
      tr.2.1 e₂ ∉ (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E →
      out.mem (tok.edgeThresholds + tr.2.1 e₁) + L ≤ out.mem (tok.edgeRecords + tr.2.1 e₂) ∨
      out.mem (tok.edgeRecords + tr.2.1 e₂) + (2 + 4 * L) ≤
        out.mem (tok.edgeThresholds + tr.2.1 e₁)

/-- **Where the levels lie after the exit.** At every run of Branch B, the new last
level, the level graphs and the length blocks after the exit lie in the zones the suffix keeps. -/
@[expose] def BranchBLevelLocGoalKFBL : Prop :=
  ∀ {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
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
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R),
    BranchBExitLevelLocKFBL (L := L) (P := P) (vCap := vCap) (eCap := eCap) tok.tag uIntBuf H.A
      H.vcL H.ecL H.X H.sE H.sX H.termTokN

/-- **The edge accounts after the suffix.** -/
@[expose] def BranchBOwnRestGoalKFBL : Prop :=
  ∀ {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
      canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
      collectDel emitCuts zeroIns filterEdits pushInsProc pushProc : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul treeMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {stepCap : ℕ → ℕ → ℕ}
    {root uIntBuf editsPtr editWords g l heap pos : ℕ} {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}
    (H : BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
      intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
      bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
      dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
      edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
      collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
      coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
      allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
      editsPtr editWords g l heap pos ω mem0 mem model tok U B R),
    BranchBOwnRestFieldsKFBL (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp) (vCap := vCap)
      (eCap := eCap) (reembFn := reembFn) coreSpace coreFixed toolMul treeMul root uIntBuf heap
      mem0 mem model tok U (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ) B R H.heap2
      (H.sE.regs 4) H.hT (H.sX.regs 4) H.fr H.levelU H.levelUS H.D H.tokN H.vcL H.ecL H.termTokN
      H.curTree H.curTreeTok H.offCnt H.canonVal H.out H.nextHeap H.cost

/-- `BranchBOwnGoalKFBL` from the two propositions `BranchBLevelLocGoalKFBL` and
`BranchBOwnRestGoalKFBL`. The other fields come from the facts of the run
(`BranchBRunKFBL.own_cells`, `own_cores`, `own_sel`, `own_levels` and `own_phase`). -/
theorem branchBOwnGoal_of_goals (hLoc : BranchBLevelLocGoalKFBL)
    (hRest : BranchBOwnRestGoalKFBL) : BranchBOwnGoalKFBL := by
  intro w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
    forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
    canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
    updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
    signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
    collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace coreFixed toolMul
    treeMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace allocation
    lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf editsPtr editWords
    g l heap pos ω mem0 mem model tok U B R H
  obtain ⟨hLocal, hdPos, hBran, hLastB⟩ := H.own_cells
  obtain ⟨hReps, hDisj⟩ := H.own_cores
  obtain ⟨hLast, hGraphs, hLens⟩ := H.own_levels (hLoc H)
  have hR := hRest (treeMul := treeMul) H
  exact
    { coreLocal := hLocal, dPos := hdPos, phase := H.own_phase, canon := hR.canon,
      thrLoc := hR.thrLoc, recLoc := hR.recLoc, thrRecDisj := hR.thrRecDisj, bran := hBran,
      lastB := hLastB, reps := hReps, coreDisj := hDisj, lastRep := hLast, graphs := hGraphs,
      lens := hLens, sel := H.own_sel }

end MinCostFlow.MinRatio
