module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunHeadKFBL

/-!
# Two parts of the tail of the run of Branch B (`WireChainCoreBranchBRunTailGoalsKFBL`)

The tail goal `BranchBRunTailGoalKFBL` (`WireChainCoreBranchBRunHeadKFBL.lean`) builds a full run
`BranchBRunKFBL` from a head `BranchBRunHeadKFBL`. Two of the fields that it adds read only the
head and do not use the suffix. They are stated here as propositions, so that they can be proved
on their own.

* `BranchBTailSplitGoalKFBL`: the field `split` of `BranchBRunKFBL` (the split of the chain tree
  before Sync 2a), for the sets `Fp`, `oldFs`, `newFs` of the fields `Fp_eq`, `oldFs_eq`,
  `newFs_eq`.
* `BranchBTailPhaseGoalKFBL`: the field `phaseX` of `BranchBRunKFBL` (the tree state on the new
  root graph, at the memory after the exit).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- **The split of the chain tree at the end of the exit.** The field `split` of
`BranchBRunKFBL` from a head of the run. -/
@[expose] def BranchBTailSplitGoalKFBL : Prop :=
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
    (Hd : BranchBRunHeadKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
        intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
        bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
        dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
        edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
        collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
        coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
        allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
        editsPtr editWords g l heap pos ω mem0 mem model tok U B R),
    ∀ (Fp : Finset ℕ) (oldFs newFs : List MGraph),
    Fp = (Finset.range Hd.fr).biUnion (fun j => (Hd.X.toTreeChain.activeLSF j).F.F.E) →
    oldFs = (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.st0 Hd.fr else []) →
    newFs = (if Hd.fr ≤ cfg.P.d then chainSuffixForests Hd.X Hd.fr else []) →
    (∀ Y : Finset ℕ,
      (∀ e, e ∈ Y ↔ (∃ j < min Hd.fr cfg.P.d, e ∈ (Hd.D j).fDel) ∧ e ∈ Hd.G1.E) →
      Hd.F1 \ Y = Fp ∪ (graphListEdgeUnion oldFs ∩ Hd.G1.E)) ∧
    (∀ j < min Hd.fr cfg.P.d, ∀ e ∈ (Hd.D j).fDel, e ∈ Hd.G1.E → e ∈ Hd.F1) ∧
    (∀ e ∈ Fp, e ∉ graphListEdgeUnion oldFs) ∧ (∀ e ∈ Fp, e ∉ graphListEdgeUnion newFs) ∧
    Fp ∪ graphListEdgeUnion newFs = Hd.X.toTreeChain.chainTree.E ∧
    ((List.range (min Hd.fr cfg.P.d)).flatMap fun j => (Hd.D j).fDel).Nodup

/-- **The tree state on the new root graph after the exit.** The field `phaseX` of
`BranchBRunKFBL` from a head of the run. -/
@[expose] def BranchBTailPhaseGoalKFBL : Prop :=
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
    (Hd : BranchBRunHeadKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
        intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
        bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
        dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
        edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
        collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
        coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
        allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
        editsPtr editWords g l heap pos ω mem0 mem model tok U B R),
    TreeSyncPhaseAt L tok root uIntBuf (Hd.sX.regs 4) tok.rootGraph Hd.G1 Hd.F1 Hd.canonVal B R
      (Hd.G1.E \ (model.chain.G 0).E) Hd.curTree1 Hd.curTreeTok1 Hd.offCnt1 Hd.sX.mem

end MinCostFlow.MinRatio

end
