module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBSufOutKFBL

/-!
# The model and the kept words of Branch B as a proposition (`WireChainCoreBranchBModelGoalKFBL`)

The fields `names`, `frPos`, `link`, `newForest`, `newSub`, `sched`, `slotModel`, `rootDir`,
`header`, `table`, `metaCells`, `fresh` and `frameMem` of `BranchBSufOutKFBL`: the name maps and
the chain of the model after the update, the link of the finished levels, the schedule words, and
the words that keep their values. `BranchBModelGoalKFBL` states them for every run of Branch B with
its parts (`BranchBRunKFBL`). Its proof uses `modelEq` (the model `X` of the exit is the chain of
`alg2PreResetState`), `branchBUpdateLoop_int` and `branchBUpdateLoop_term` with the update-loop
equation of the loop facts, the `slotModel` of the loop invariant, `UpdateCoreModelInv` and
`UpdateCoreModelInvKFBL` of `start`, and the frames of the parts.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The model and kept-word fields of `BranchBSufOutKFBL`. They are the fields of
`BranchBSufOutKFBL` of the same names, with the same parameters. -/
structure BranchBModelFieldsKFBL
    {w L P m V psi k epsExp drainUnit capExp vCap eCap : ℕ} {cfg : Alg2Config}
    {reembFn : ToolReembFn cfg.T} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (coreSpace coreFixed : ℕ → ℕ) (toolMul treeMul : ℕ)
    (root uIntBuf heap : ℕ) (mem0 mem : ℕ → ℕ) (model : Alg2State cfg)
    (tok : SolverToken cfg L Rcore) (U : List Update) (gVec lVec : ℕ → ℝ) (B R : ℤ)
    (heap2 hS hT hX fr : ℕ) (levelU levelUS : ℕ → List Update) (D : ℕ → LevelDiffLists)
    (tokN : ℕ → Rcore.τ) (vcL ecL termTokN : ℕ) (curTree : PathTreeState)
    (curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ) (offCnt : ℕ)
    (canonVal : ℕ → PathEdgeValue) (out : State) (nextHeap cost : ℕ) : Prop where
  names :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let modelPre := alg2PreResetState cfg model U gVec lVec
    modelPre.extToInt = tr.2.1 ∧ modelPre.intToExt = tr.2.2.1 ∧ modelPre.nextFresh = tr.2.2.2.1
  frPos : 0 < fr
  link : UpdateCoreLevelLink model.chain (alg2PreResetState cfg model U gVec lVec).chain fr
    levelU levelUS
  newForest : (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.IsForest
  newSub : (alg2PreResetState cfg model U gVec lVec).chain.toTreeChain.chainTree.E ⊆
    ((alg2PreResetState cfg model U gVec lVec).chain.G 0).E
  sched : SolverScheduleAt out.mem tok.levelsEnd (alg2PreResetState cfg model U gVec lVec)
  slotModel : ∀ j < min fr cfg.P.d,
    (D j).uG = coreBatchTouchedEdges (levelU j) ∧
    (D j).uS = coreBatchTouchedEdges (levelUS j) ∧
    (D j).fDel.Nodup ∧
    (D j).fDel.toFinset = (cfg.T.lsfs (model.chain.scState j) (model.chain.bran j)).F.F.E \
      (cfg.T.lsfs ((alg2PreResetState cfg model U gVec lVec).chain.scState j)
        ((alg2PreResetState cfg model U gVec lVec).chain.bran j)).F.F.E ∧
    (D j).reemb = reembFn (model.chain.scState j) (levelU j)
      ((alg2PreResetState cfg model U gVec lVec).chain.levelOrd j) (model.chain.bran j) ∧
    BatchWithinCaps vCap eCap (levelU j)
  rootDir : ∀ j < 16, j ≠ 11 → out.mem (root + j) = mem0 (root + j)
  header : ∀ j < 18, out.mem (tok.handle + j) = mem0 (tok.handle + j)
  table : ∀ j ≤ cfg.P.d, out.mem (tok.table + j) = mem0 (tok.table + j)
  metaCells :
    out.mem (solverN0Addr tok.table cfg.P.d) = mem0 (solverN0Addr tok.table cfg.P.d) ∧
    (∀ j < cfg.P.d, out.mem (solverLvlMAddr tok.table cfg.P.d + j) =
      mem0 (solverLvlMAddr tok.table cfg.P.d + j)) ∧
    out.mem (solverSelectHeapAddr tok.table cfg.P.d) =
      mem0 (solverSelectHeapAddr tok.table cfg.P.d) ∧
    out.mem (solverSelectBlocksAddr tok.table cfg.P.d) =
      mem0 (solverSelectBlocksAddr tok.table cfg.P.d)
  fresh :
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    FreshTablesAt out.mem tok.forward tok.inverse tok.freshCounter m tok.intCap
      tr.2.1 tr.2.2.1 tr.2.2.2.1
  frameMem : ∀ a < heap,
    ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
    out.mem a = mem a

/-- **The model and the kept words of Branch B.** For every run of Branch B with its
parts, the fields `names`, `frPos`, `link`, `newForest`, `newSub`, `sched`, `slotModel`,
`rootDir`, `header`, `table`, `metaCells`, `fresh` and `frameMem` of `BranchBSufOutKFBL` hold at
the final state. -/
@[expose] def BranchBModelGoalKFBL : Prop :=
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
    BranchBModelFieldsKFBL (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp) (vCap := vCap)
      (eCap := eCap) (reembFn := reembFn) coreSpace coreFixed toolMul treeMul root uIntBuf heap
      mem0 mem model tok U (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ) B R H.heap2
      (H.sE.regs 4) H.hT (H.sX.regs 4) H.fr H.levelU H.levelUS H.D H.tokN H.vcL H.ecL H.termTokN
      H.curTree H.curTreeTok H.offCnt H.canonVal H.out H.nextHeap H.cost

end MinCostFlow.MinRatio
