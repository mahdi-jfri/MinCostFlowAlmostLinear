module

public import MinCostFlow.MinRatio.WireChainCoreBranchBCostGoalKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBSpaceGoalKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBModelGoalKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBForestLocGoalKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBPostRep

/-!
# The top theorem of Branch B from its goals (`WireChainCoreBranchBTopKFBL`)

`BranchBTopGoalKFBL` is the post of Branch B. It follows from `ordChainCoreBranchBPost_of_goal`
with the post goal `branchBPostGoalKFBL_proved`, once every start state has a run of the core that
ends in a state with `BranchBSufOutKFBL`. This file gets that run in two steps:
* `BranchBRunGoalKFBL`: every start state has a run of Branch B with its parts
  (`BranchBRunKFBL`), from the environments, the exit goals, the forest place goals and the tool
  facts;
* the fields of `BranchBSufOutKFBL` at the final state of such a run, in four groups: the cost
  (`BranchBCostGoalKFBL`), the space and the places (`BranchBSpaceGoalKFBL`), the model and the
  kept words (`BranchBModelGoalKFBL`), and the rest (`BranchBOwnGoalKFBL`: the tree state, the
  edge accounts, the cores, the last level, the level graphs and lengths, and the select word).
`branchBTopGoalKFBL_of_goals` proves the top goal from these propositions, the two forest
place goals and the two exit goals.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The rest of the fields of `BranchBSufOutKFBL`, with the same names and parameters. -/
structure BranchBOwnFieldsKFBL
    {w L P m V psi k epsExp drainUnit capExp vCap eCap : ℕ} {cfg : Alg2Config}
    {reembFn : ToolReembFn cfg.T} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (coreSpace coreFixed : ℕ → ℕ) (toolMul treeMul : ℕ)
    (root uIntBuf heap : ℕ) (mem0 mem : ℕ → ℕ) (model : Alg2State cfg)
    (tok : SolverToken cfg L Rcore) (U : List Update) (gVec lVec : ℕ → ℝ) (B R : ℤ)
    (heap2 hS hT hX fr : ℕ) (levelU levelUS : ℕ → List Update) (D : ℕ → LevelDiffLists)
    (tokN : ℕ → Rcore.τ) (vcL ecL termTokN : ℕ) (curTree : PathTreeState)
    (curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ) (offCnt : ℕ)
    (canonVal : ℕ → PathEdgeValue) (out : State) (nextHeap cost : ℕ) : Prop where
  coreLocal : Rcore.Local
  dPos : 0 < cfg.P.d
  phase : TreeSyncPhaseAt L tok root uIntBuf nextHeap tok.rootGraph
    ((alg2PreResetState cfg model U gVec lVec).chain.G 0)
    (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E canonVal B R ∅
    curTree curTreeTok offCnt out.mem
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
  bran : ∀ j < cfg.P.d, out.mem (tok.handle + 18 + (cfg.P.d + 1) + j) =
    (alg2PreResetState cfg model U gVec lVec).chain.bran j
  lastB : out.mem (tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d) =
    (alg2PreResetState cfg model U gVec lVec).chain.lastBran
  reps : ∀ j < cfg.P.d, Rcore.rep (out.mem (tok.handle + 18 + j))
    (chainLevelOrdAbs (alg2PreResetState cfg model U gVec lVec).chain j) (tokN j) out.mem
  coreDisj : ∀ j₁ < cfg.P.d, ∀ j₂ < cfg.P.d, j₁ ≠ j₂ → ∀ a,
    Rcore.foot (out.mem (tok.handle + 18 + j₁)) (tokN j₁) a →
    ¬ Rcore.foot (out.mem (tok.handle + 18 + j₂)) (tokN j₂) a
  lastRep : (LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P
      ((alg2PreResetState cfg model U gVec lVec).chain.G cfg.P.d).E).rep
    (out.mem (tok.handle + 18 + cfg.P.d))
    ((alg2PreResetState cfg model U gVec lVec).chain.lastK,
      (alg2PreResetState cfg model U gVec lVec).chain.lastLSFs) termTokN out.mem
  graphs : ∀ j < cfg.P.d,
    DynGraphAt out.mem (out.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j)) vCap eCap
      ((alg2PreResetState cfg model U gVec lVec).chain.G j)
  lens : ∀ j < cfg.P.d,
    EdgeValuesAt out.mem (out.mem (solverLevelMetaAddr tok.table cfg.P.d + j)) 4 L P
      ((alg2PreResetState cfg model U gVec lVec).chain.G j).E
      ((alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainLen
        (alg2PreResetState cfg model U gVec lVec).chain.ℓ j)
  sel : out.mem heap = fr

/-- **The rest of the fields of Branch B.** For every run of Branch B with its parts,
the fields of `BranchBOwnFieldsKFBL` hold at the final state. -/
@[expose] def BranchBOwnGoalKFBL : Prop :=
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
    BranchBOwnFieldsKFBL (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp) (vCap := vCap)
      (eCap := eCap) (reembFn := reembFn) coreSpace coreFixed toolMul treeMul root uIntBuf heap
      mem0 mem model tok U (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ) B R H.heap2
      (H.sE.regs 4) H.hT (H.sX.regs 4) H.fr H.levelU H.levelUS H.D H.tokN H.vcL H.ecL H.termTokN
      H.curTree H.curTreeTok H.offCnt H.canonVal H.out H.nextHeap H.cost

/-- **A run of Branch B with its parts.** From the environments, the two exit goals,
the two forest place goals and the tool facts, every start state of Branch B has a run with its
parts (`BranchBRunKFBL`). -/
@[expose] def BranchBRunGoalKFBL : Prop :=
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
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ},
    BranchAEnvKFBL w L P m capExp capLimit fcap lastMul intCapMax forestEdgeCap drainUnit
      edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy isNeg
      refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply updateLen0Proc
      initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc signExt mul
      intDiv lastInit rebuildOffReadyProc coreSpace coreFixed toolMul fmt cfg G Psc levelSpace
      levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Rcore p opTree opCore
      opLast stepCap →
    BranchBEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc
      collectProc edgeProc signExt mul intDiv copy collectDel emitCuts zeroIns filterEdits
      pushInsProc pushProc isNeg fmt cfg Psc allocation Ginit reembFn Rcore p opCore →
    BranchBIntExitLayGoalKFBL → BranchBTermExitLayGoalKFBL →
    BranchBIntExitForestLocGoalKFBL → BranchBTermExitForestLocGoalKFBL →
    (∀ ch, ShiftLoopChainInv cfg ch → BranchBToolStepKFBL cfg stepCap ch) →
    BranchBForestShrinkKFBL cfg →
    (∀ b s x mem, Rcore.rep b s x mem → Rcore.foot b x b) →
    cfg.TP.Valid →
    BranchBStartKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp
      stretchPrec intCapMax forestEdgeCap vCap eCap cfg G Rcore coreSpace root uIntBuf editsPtr
      editWords g l heap mem0 mem model tok U B R →
    Nonempty (BranchBRunKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
        intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
        bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
        dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
        edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
        collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
        coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
        allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
        editsPtr editWords g l heap pos ω mem0 mem model tok U B R)


/-- **The top theorem of Branch B from its goals.** `BranchBTopGoalKFBL` holds when every start
state has a run of Branch B with its parts (`BranchBRunGoalKFBL`, from the forest place goals of the
two exits), and the fields of `BranchBSufOutKFBL` hold at the end of every such run (the cost, the
space, the model and the other fields). The post is `branchBPostGoalKFBL_proved`, through
`ordChainCoreBranchBPost_of_goal`. -/
theorem branchBTopGoalKFBL_of_goals (hRun : BranchBRunGoalKFBL)
    (hIntF : BranchBIntExitForestLocGoalKFBL) (hTermF : BranchBTermExitForestLocGoalKFBL)
    (hCost : BranchBCostGoalKFBL) (hSpace : BranchBSpaceGoalKFBL)
    (hModel : BranchBModelGoalKFBL) (hOwn : BranchBOwnGoalKFBL) : BranchBTopGoalKFBL := by
  intro w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
    forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy
    isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
    updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
    signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
    collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace coreFixed toolMul
    treeMul B_bound R_bound fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
    allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap EA EB hInt hTerm hTS
    hShr hHF hTP hTM hMono hγk
  refine ordChainCoreBranchBPost_of_goal (branchBPostGoalKFBL_proved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
  intro root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok U B R tr gVec lVec
    modelPre Rrep h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
    h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35
  have S : BranchBStartKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp
      stretchPrec intCapMax forestEdgeCap vCap eCap cfg G Rcore coreSpace root uIntBuf editsPtr
      editWords g l heap mem0 mem model tok U B R :=
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h11, h12, h13, h14, h15, h16, h17, h18,
      h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35⟩
  obtain ⟨H⟩ := hRun (pos := pos) (ω := ω) EA EB hInt hTerm hIntF hTermF hTS hShr hHF hTP S
  have C := hCost (treeMul := treeMul) H hTM hMono hγk
  have Sp := hSpace (treeMul := treeMul) H
  have M := hModel (treeMul := treeMul) H
  have O := hOwn (treeMul := treeMul) H
  exact ⟨H.heap2, H.sE.regs 4, H.hT, H.sX.regs 4, H.fr, H.levelU, H.levelUS, H.D, H.tokN, H.vcL,
    H.ecL, H.termTokN, H.curTree, H.curTreeTok, H.offCnt, H.canonVal, H.out, H.nextHeap, H.cost,
    H.runs,
    { coreLocal := O.coreLocal, dPos := O.dPos, heaps := Sp.heaps, space := Sp.space,
      zero := Sp.zero, names := M.names, frPos := M.frPos, link := M.link,
      newForest := M.newForest, newSub := M.newSub, rootDir := M.rootDir, header := M.header,
      table := M.table, metaCells := M.metaCells, fresh := M.fresh, sched := M.sched,
      frameMem := M.frameMem, phase := O.phase, treeFoot := Sp.treeFoot, canon := O.canon,
      thrLoc := O.thrLoc, recLoc := O.recLoc, thrRecDisj := O.thrRecDisj, bran := O.bran,
      lastB := O.lastB, reps := O.reps, coreFoot := Sp.coreFoot, coreDisj := O.coreDisj,
      coreHandleLoc := Sp.coreHandleLoc, lastRep := O.lastRep, lastFoot := Sp.lastFoot,
      graphs := O.graphs, lens := O.lens, metaKeep := Sp.metaKeep, metaNew := Sp.metaNew,
      sel := O.sel, slots := Sp.slots, slotModel := M.slotModel, costLe := C.costLe }⟩

end MinCostFlow.MinRatio
