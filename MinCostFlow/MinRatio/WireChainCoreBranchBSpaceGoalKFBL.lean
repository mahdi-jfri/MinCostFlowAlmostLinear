module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBSufOutKFBL

/-!
# The space and the places of Branch B as a proposition (`WireChainCoreBranchBSpaceGoalKFBL`)

The fields `heaps`, `space`, `zero`, `treeFoot`, `coreFoot`, `coreHandleLoc`, `lastFoot`,
`metaKeep`, `metaNew` and `slots` of `BranchBSufOutKFBL`: the cuts of the heap, the bound of the
heap by `coreSpace`, and where the words of the tree, the cores, the last level, the level blocks
and the select data lie. `BranchBSpaceGoalKFBL` states them for every run of Branch B with its parts
(`BranchBRunKFBL`). Its proof uses the heap bounds of the parts, `spaceTotalBranchB` of `envA.ops`,
the places `BranchBExitLayKFBL` of `exitOut` (`hTle`, `zone`, `newCores`, `lastLoc`, `metaKeep`,
`metaNew`), the frame of the suffix, the handle fact `handleFoot` (for `coreHandleLoc`) and
`branchBSufSlots_level`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The space and place fields of `BranchBSufOutKFBL`. They are the fields of `BranchBSufOutKFBL` of
the same names, with the same parameters. -/
structure BranchBSpaceFieldsKFBL
    {w L P m V psi k epsExp drainUnit capExp vCap eCap : ℕ} {cfg : Alg2Config}
    {reembFn : ToolReembFn cfg.T} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (coreSpace coreFixed : ℕ → ℕ) (toolMul treeMul : ℕ)
    (root uIntBuf heap : ℕ) (mem0 mem : ℕ → ℕ) (model : Alg2State cfg)
    (tok : SolverToken cfg L Rcore) (U : List Update) (gVec lVec : ℕ → ℝ) (B R : ℤ)
    (heap2 hS hT hX fr : ℕ) (levelU levelUS : ℕ → List Update) (D : ℕ → LevelDiffLists)
    (tokN : ℕ → Rcore.τ) (vcL ecL termTokN : ℕ) (curTree : PathTreeState)
    (curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ) (offCnt : ℕ)
    (canonVal : ℕ → PathEdgeValue) (out : State) (nextHeap cost : ℕ) : Prop where
  heaps : uIntBuf ≤ heap ∧ heap + 1 + 12 * cfg.P.d ≤ heap2 ∧ heap2 ≤ hS ∧ hS ≤ hT ∧ hT ≤ hX ∧
    hX ≤ nextHeap ∧ nextHeap < 2 ^ w
  space : nextHeap ≤ heap + coreSpace U.length
  zero : ZeroFrom out.mem nextHeap
  treeFoot : ∀ a,
    (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap curTreeTok a →
    (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a ∨
      (heap + 1 + 12 * cfg.P.d ≤ a ∧ a < heap2) ∨ (hX ≤ a ∧ a < nextHeap)
  coreFoot : ∀ j < cfg.P.d, ∀ a, Rcore.foot (out.mem (tok.handle + 18 + j)) (tokN j) a →
    (a < heap → tok.tag a = 21 + j) ∧ (heap ≤ a → heap2 ≤ a ∧ a < hX)
  coreHandleLoc : ∀ j < cfg.P.d,
    out.mem (tok.handle + 18 + j) = mem0 (tok.handle + 18 + j) ∨
    (hS ≤ out.mem (tok.handle + 18 + j) ∧ out.mem (tok.handle + 18 + j) < hT)
  lastFoot : ∀ a, (LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P
      ((alg2PreResetState cfg model U gVec lVec).chain.G cfg.P.d).E).foot
      (out.mem (tok.handle + 18 + cfg.P.d)) termTokN a →
    (a < heap → tok.tag a = 19) ∧ (heap ≤ a → hS ≤ a ∧ a < hT) ∧
    ∀ j < cfg.P.d, ¬ Rcore.foot (out.mem (tok.handle + 18 + j)) (tokN j) a
  metaKeep : ∀ j < min (fr + 1) cfg.P.d,
    out.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) =
      mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) ∧
    out.mem (solverLevelMetaAddr tok.table cfg.P.d + j) =
      mem0 (solverLevelMetaAddr tok.table cfg.P.d + j)
  metaNew : ∀ j, fr + 1 ≤ j → j < cfg.P.d →
    let gp := out.mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j)
    let lp := out.mem (solverLevelMetaAddr tok.table cfg.P.d + j)
    hS ≤ gp ∧ gp + dynGraphSize vCap eCap ≤ hT ∧ hS ≤ lp ∧ lp + eCap * L ≤ hT ∧
    ∀ a, ((gp ≤ a ∧ a < gp + dynGraphSize vCap eCap) ∨ (lp ≤ a ∧ a < lp + eCap * L)) →
      (∀ r < cfg.P.d, ¬ Rcore.foot (out.mem (tok.handle + 18 + r)) (tokN r) a) ∧
      ¬ (LastLevelProgram.lastLevelRepresentation vcL ecL 4 L P
        ((alg2PreResetState cfg model U gVec lVec).chain.G cfg.P.d).E).foot
        (out.mem (tok.handle + 18 + cfg.P.d)) termTokN a
  slots : ∀ j < min fr cfg.P.d,
    SelOutLevelMemAt w P (ordLevelLwMax L capExp (levelM cfg.TP cfg.P j) cfg.N₀)
      (fun x => BranchBSelZone heap2 hS hT hX x ∧
        ∀ r < cfg.P.d, ¬ Rcore.foot (out.mem (tok.handle + 18 + r)) (tokN r) x)
      (fun x => Rcore.foot (out.mem (tok.handle + 18 + j)) (tokN j) x ∨ (heap2 ≤ x ∧ x < hX))
      heap2 hX out.mem (heap + 1 + 12 * j) (D j) (model.chain.G j) (levelU j)
      ((alg2PreResetState cfg model U gVec lVec).chain.G j).E
      (cfg.T.lsfs ((alg2PreResetState cfg model U gVec lVec).chain.scState j)
        ((alg2PreResetState cfg model U gVec lVec).chain.bran j)).wstr

/-- **The space and the places of Branch B.** For every run of Branch B with its parts,
the fields `heaps`, `space`, `zero`, `treeFoot`, `coreFoot`, `coreHandleLoc`, `lastFoot`,
`metaKeep`, `metaNew` and `slots` of `BranchBSufOutKFBL` hold at the final state. -/
@[expose] def BranchBSpaceGoalKFBL : Prop :=
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
    BranchBSpaceFieldsKFBL (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp) (vCap := vCap)
      (eCap := eCap) (reembFn := reembFn) coreSpace coreFixed toolMul treeMul root uIntBuf heap
      mem0 mem model tok U (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
      (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ) B R H.heap2
      (H.sE.regs 4) H.hT (H.sX.regs 4) H.fr H.levelU H.levelUS H.D H.tokN H.vcL H.ecL H.termTokN
      H.curTree H.curTreeTok H.offCnt H.canonVal H.out H.nextHeap H.cost

end MinCostFlow.MinRatio
