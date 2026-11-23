module

public import MinCostFlow.MinRatio.WireChainCoreCostBaseKFBL
public import MinCostFlow.MinRatio.OrdSolverToolMono
public import MinCostFlow.MinRatio.WireChainCoreBranchBRunKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBSufOutKFBL

/-!
# The cost of Branch B as a proposition (`WireChainCoreBranchBCostGoalKFBL`)

The field `costLe` of `BranchBSufOutKFBL`: the cost of the run of the core plus the potentials of
the tree, the cores and the off-ready list at the end is at most the budget of the core plus the
potential of the solver rep at the start. `BranchBCostGoalKFBL` states it for every run of Branch B
with its parts (`BranchBRunKFBL`). Its proof uses the cost bounds of the parts (`c0 ≤ 210`, the
bound of the prefix in `BranchBPrefixFactsKFBL`, of the front, of the loop in
`BranchBLoopExitAtKFBL`, of the exit in `BranchBExitCaseKFBL`, of the suffix in
`BranchBSuffixFactsKFBL`, and `costLe` of `BranchBRunKFBL`), the totals
`UpdateCoreOpsHypKFBL.costTotalBranchB` of `envA.ops` (one case per exit), `branchBStepCostKFBL`,
the `ToolCostMono` clause of the loop facts, and the tree-update count of the model.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The cost field of `BranchBSufOutKFBL`. They are the fields of `BranchBSufOutKFBL` of the same
names, with the same parameters. -/
structure BranchBCostFieldsKFBL
    {w L P m V psi k epsExp drainUnit capExp vCap eCap : ℕ} {cfg : Alg2Config}
    {reembFn : ToolReembFn cfg.T} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (coreSpace coreFixed : ℕ → ℕ) (toolMul treeMul : ℕ)
    (root uIntBuf heap : ℕ) (mem0 mem : ℕ → ℕ) (model : Alg2State cfg)
    (tok : SolverToken cfg L Rcore) (U : List Update) (gVec lVec : ℕ → ℝ) (B R : ℤ)
    (heap2 hS hT hX fr : ℕ) (levelU levelUS : ℕ → List Update) (D : ℕ → LevelDiffLists)
    (tokN : ℕ → Rcore.τ) (vcL ecL termTokN : ℕ) (curTree : PathTreeState)
    (curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ) (offCnt : ℕ)
    (canonVal : ℕ → PathEdgeValue) (out : State) (nextHeap cost : ℕ) : Prop where
  costLe : cost +
      ((LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tok.treeHeap curTreeTok
          out.mem +
        (Finset.range cfg.P.d).sum
          (fun j => Rcore.phi (out.mem (tok.handle + 18 + j)) (tokN j) out.mem) +
        offCnt * drainUnit) ≤
    coreFixed U.length +
      toolMul * ((alg2PreResetState cfg model U gVec lVec).chain.totalRuntime -
        model.chain.totalRuntime) +
      treeMul * ((alg2PreResetState cfg model U gVec lVec).chain.totalTreeUpdates -
        model.chain.totalTreeUpdates) +
      40 * (Finset.range (min fr cfg.P.d)).sum (fun j => (D j).reemb.length) +
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok mem0

/-- **The cost of Branch B.** For every run of Branch B with its parts, the field
`costLe` of `BranchBSufOutKFBL` holds at the final state, when `treeMul` pays for one edit of the
tree (`updateCoreTreeMulBound L drainUnit ≤ treeMul`), the costs of the tool do not drop
(`ToolCostMono cfg.T`), and the bound `levelM j ≤ levelM 0` of the levels holds
(`γ_ℓ (M₀²) ≤ k`). -/
@[expose] def BranchBCostGoalKFBL : Prop :=
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
    updateCoreTreeMulBound L drainUnit ≤ treeMul → ToolCostMono cfg.T →
    cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k →
    BranchBCostFieldsKFBL (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp) (vCap := vCap)
      (eCap := eCap) (reembFn := reembFn) coreSpace coreFixed toolMul treeMul root uIntBuf heap
      mem0 mem model tok U (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ) B R H.heap2
      (H.sE.regs 4) H.hT (H.sX.regs 4) H.fr H.levelU H.levelUS H.D H.tokN H.vcL H.ecL H.termTokN
      H.curTree H.curTreeTok H.offCnt H.canonVal H.out H.nextHeap H.cost

end MinCostFlow.MinRatio
