module

public import MinCostFlow.MinRatio.WireChainCoreCostBaseKFBL
public import MinCostFlow.MinRatio.OrdSolverToolMono
public import MinCostFlow.MinRatio.WireChainCoreBranchBExitLayGoalKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBPrefixKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBFrontLoopKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBSuffixKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBShrinkKFBL
public import MinCostFlow.MinRatio.WireChainCoreSpecProofKFBL

/-!
# The top theorem of Branch B as a proposition (`WireChainCoreBranchBTopGoalKFBL`)

Branch B of the chain core is the statement `wireBranchBKFBL`: the prefix (Sync 1 and the
refresh of level `0`), the front, the loop of plain steps, the exit (the interior rebuild when the
loop stops below `d`, the terminal step otherwise), and the suffix (Sync 2a, the load of
`firstReb`, Sync 2b, the push and the return). It is the statement `dryInnerCoreBranchB` of the
dry program at the procedure indices of `dryInnerCoreProcsOf`.

`BranchBTopGoalKFBL` is the top theorem of `hB`: for the body `ordChainUpdateCoreBodyKFBL` with
Branch A and this Branch B, the post `OrdChainCoreBranchBPostKFBL`. The facts on the program are in
two environments: `BranchAEnvKFBL` (shared with Branch A: the tree, the cores, the last level, the
numeric helpers and the budget forms) and `BranchBEnvKFBL` (the loop environment and the helper
procedures of Branch B). The other premises are the two exit goals, the tool step fact, the shrink
fact, the handle fact, the validity of the tool parameters, and three bounds that the cost needs:
`updateCoreTreeMulBound L drainUnit ≤ treeMul`, `ToolCostMono cfg.T` and
`cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k`. All of them hold at the dry values.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- Branch B of the chain core, at the procedure indices of its helpers. -/
@[expose] def wireBranchBKFBL (collectDel emitCuts packEditsProc filterEdits zeroIns
    refreshAccountsProc updateLen0Proc copyProc updLen slotProc pushInsProc bind canonCopy isNeg
    dgApply initCore coreLenProc lastInit : ℕ) (opTree opCore : ℕ → ℕ) : Stmt :=
  wireBranchBPrefixKFBL collectDel emitCuts (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg
      zeroIns refreshAccountsProc updateLen0Proc ;;
  wireBranchBFrontKFBL copyProc ;;
  wireBranchBLoopKFBL (opCore 0) (opCore 2) dgApply copyProc updLen slotProc ;;
  .cond (.bin .lt (.reg 96) (.reg 75))
    (wireBranchBIntKFBL dgApply initCore (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit)
    (wireBranchBTermKFBL (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit ;;
      collectTermForestStmt 81) ;;
  wireBranchBSuffixKFBL emitCuts packEditsProc filterEdits (opTree 4) (opTree 1) (opTree 0) bind
    canonCopy isNeg pushInsProc

/-- The facts on the program that Branch B uses on top of `BranchAEnvKFBL`: the environment of
its loop (`BranchBLoopEnvKFBL`, at the start graphs `Ginit` of the cores) and the bodies of its
helper procedures, and the depth of the cores as Phase 0 loads it into `reg 98`. -/
structure BranchBEnvKFBL (w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
    slotProc collectProc edgeProc signExt mul intDiv copy collectDel emitCuts zeroIns filterEdits
    pushInsProc pushProc isNeg : ℕ) (fmt : Num.Format w) (cfg : Alg2Config)
    (Psc : SparseCoreOrdParams) (alloc : ℕ → List ℕ → ℕ) (Ginit : ℕ → MGraph)
    (reembFn : ToolReembFn cfg.T) (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (opCore : ℕ → ℕ) : Prop where
  loop : BranchBLoopEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
    slotProc collectProc edgeProc signExt mul intDiv copy fmt cfg Psc alloc Ginit reembFn Rcore p
    opCore
  collectP : p.procs[collectDel]? = some wireCollectDeletedEdgesBody
  emitP : p.procs[emitCuts]? = some wireEmitTreeCutsBody
  zeroP : p.procs[zeroIns]? = some wireZeroInsertSlotsBody
  filterP : p.procs[filterEdits]? = some wireFilterPresentEditsBody
  pushInsP : p.procs[pushInsProc]? = some (wirePushInsertedBody pushProc)
  pushP : p.procs[pushProc]? = some (offTreePushBody isNeg)
  depthEq : depth = Expander.chosenL (cfg.P.M₀ ^ 2)

/-- **The top theorem of `hB`.** For the body of the chain core with Branch A and
Branch B (`wireBranchBKFBL`), the post `OrdChainCoreBranchBPostKFBL`, from the two environments,
the two exit goals, the tool step fact, the shrink fact `BranchBForestShrinkKFBL`, the handle fact
(a core handle lies in its own footprint), the validity of the tool parameters, and the three
bounds of the cost (`treeMul`, `ToolCostMono`, `γ_ℓ (M₀²) ≤ k`). -/
@[expose] def BranchBTopGoalKFBL : Prop :=
  ∀ {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
      canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
      collectDel emitCuts zeroIns filterEdits pushInsProc pushProc : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul treeMul : ℕ} {B_bound R_bound : ℤ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {stepCap : ℕ → ℕ → ℕ},
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
    BranchBIntExitLayGoalKFBL →
    BranchBTermExitLayGoalKFBL →
    (∀ ch, ShiftLoopChainInv cfg ch → BranchBToolStepKFBL cfg stepCap ch) →
    BranchBForestShrinkKFBL cfg →
    (∀ b s x mem, Rcore.rep b s x mem → Rcore.foot b x b) →
    cfg.TP.Valid →
    updateCoreTreeMulBound L drainUnit ≤ treeMul → ToolCostMono cfg.T →
    cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k →
    OrdChainCoreBranchBPostKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      wordExp stretchPrec intCapMax forestEdgeCap vCap eCap cfg G reembFn Rcore p coreSpace
      coreFixed toolMul treeMul B_bound R_bound (ordChainUpdateCoreBodyKFBL
        (wireBranchAKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg
          refreshAccountsProc dgApply updateLen0Proc (opCore 2) renameProc compactProc
          sortedEndsProc initCore (opCore 3) coreLenProc (opCore 5) lastInit rebuildOffReadyProc)
        (wireBranchBKFBL collectDel emitCuts packEditsProc filterEdits zeroIns
          refreshAccountsProc updateLen0Proc copyProc updLen slotProc pushInsProc bind canonCopy
          isNeg dgApply initCore coreLenProc lastInit opTree opCore))

end MinCostFlow.MinRatio
