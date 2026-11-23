module

public import MinCostFlow.MinRatio.WireChainCoreBodyAKFBL
import WordRAM.Tactic

/-!
# The chain-core spec from its two branches (`WireChainCoreSpecProofKFBL`)

This file proves `OrdChainUpdateCoreSpecWExtKFBL` for the chain core
`ordChainUpdateCoreBodyKFBL branchA branchB`, with Branch A the code of
`WireChainCoreBranchAKFBL`. The core tests whether level `0` must be rebuilt. When the test fires,
Branch A runs, and `ordChainUpdateCoreBodyKFBL_post_A` gives the conclusion of the spec. When it
does not fire, Branch B runs. That case is the premise `OrdChainCoreBranchBPostKFBL`: for every
start state that meets the premises of the spec and fails the test, the conclusion of the spec
holds for the core.

So `ordChainUpdateCoreSpecWExtKFBL_of_branchB` proves the spec for the core from
`OrdChainCoreBranchBPostKFBL` for the code of Branch B. The Branch B files prove that case
(`BranchBTopGoalKFBL`, `WireChainCoreBranchBTopKFBL.lean`). The three facts `hGSup`, `hGM` and
`hM0Le` are about the parameters `G`, `m` and
`mThresh` only, as in `ordChainUpdateCoreBodyKFBL_post_A`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The chain core `body` when the rebuild test at level `0` does not fire: every start state
that meets the premises of `OrdChainUpdateCoreSpecWExtKFBL` and fails the test (the threshold of
level `0` is at least the update counter of level `0` plus the length of the batch) has the
conclusion of the spec (`OrdChainCoreExtPost`). -/
@[expose] def OrdChainCoreBranchBPostKFBL
    (w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp stretchPrec intCapMax
      forestEdgeCap vCap eCap : ℕ)
    (cfg : Alg2Config) (G : MGraph) (reembFn : ToolReembFn cfg.T)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (coreSpace coreFixed : ℕ → ℕ) (toolMul treeMul : ℕ) (B_bound R_bound : ℤ)
    (body : Stmt) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∀ (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool)
    (mem0 mem : ℕ → ℕ) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore)
    (U : List Update) (B R : ℤ),
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
    let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
    let modelPre := alg2PreResetState cfg model U gVec lVec
    Rrep.rep root model tok mem0 →
    SolverLevelMetaAt P V model tok mem0 →
    SolverLevelCapsAt vCap eCap model tok mem0 →
    tok.intCap = initTargetCap cfg G →
    model.extG.m = m →
    PathTreeNumericInv tok.tree tok.trees B R →
    OffTreeRecInv model L mem0 tok.edgeRecords B →
    OffTreeRecBound model L mem0 tok.edgeRecords B →
    B ≤ B_bound → R ≤ R_bound →
    Chain.Ordered.ShiftLoopChainInv cfg model.chain →
    WireCapFacts capExp limbMul L capLimit model →
    (∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) →
    UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B →
    UpdateCoreModelInvKFBL model U gVec lVec →
    tok.intCap ≤ intCapMax →
    graphListEdgeSum (chainSuffixForests model.chain 0) +
      graphListEdgeSum (chainSuffixForests modelPre.chain 0) ≤ forestEdgeCap →
    Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L →
    2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) →
    (∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a) →
    FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
      tr.2.1 tr.2.2.1 tr.2.2.2.1 →
    tr.2.2.2.1 ≤ tok.intCap →
    BatchAt mem uIntBuf tr.2.2.2.2 →
    SmallBatchAt mem uIntBuf (model.chain.G 0) tr.2.2.2.2 (editsPtr - cfg.P.d - uIntBuf) →
    OrdEditsAt mem editsPtr (batchToOrdEdits tr.2.2.2.2) editWords →
    (∀ j < editWords, mem (editsPtr + j) < 2 ^ w) →
    editsPtr + editWords = heap →
    RefreshBatch model.extG U →
    (∀ a, Rrep.foot root tok a → a < uIntBuf) →
    g + m * L ≤ uIntBuf → l + m * L ≤ uIntBuf →
    uIntBuf + cfg.P.d ≤ editsPtr →
    ZeroFrom mem heap →
    heap + coreSpace U.length < 2 ^ w →
    ¬ intRebuildThreshold cfg.P cfg.N₀ 0 < model.chain.updCount 0 + tr.2.2.2.2.length →
    OrdChainCoreExtPost w L P m V psi k epsExp drainUnit capExp vCap eCap cfg reembFn Rcore p
      coreSpace coreFixed toolMul treeMul B_bound R_bound body root uIntBuf editsPtr editWords
      g l heap pos ω mem0 mem model tok U

/-- `OrdChainUpdateCoreSpecWExtKFBL` for the chain core at `ordChainCoreProc`, with Branch A the
code of `wireBranchAKFBL` and any `branchB` whose case meets `OrdChainCoreBranchBPostKFBL`. The
case where the test fires is `ordChainUpdateCoreBodyKFBL_post_A`. -/
theorem ordChainUpdateCoreSpecWExtKFBL_of_branchB
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
      forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind
      canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc ordChainCoreProc : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul treeMul : ℕ} {B_bound R_bound : ℤ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {branchB : Stmt}
    {stepCap : ℕ → ℕ → ℕ}
    (E : BranchAEnvKFBL w L P m capExp capLimit fcap lastMul intCapMax forestEdgeCap drainUnit
      edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy isNeg
      refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply updateLen0Proc
      initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc signExt mul
      intDiv lastInit rebuildOffReadyProc coreSpace coreFixed toolMul fmt cfg G Psc levelSpace
      levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Rcore p opTree opCore
      opLast stepCap)
    (hProc : p.procs[ordChainCoreProc]? = some (ordChainUpdateCoreBodyKFBL
      (wireBranchAKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg
        refreshAccountsProc dgApply updateLen0Proc (opCore 2) renameProc compactProc
        sortedEndsProc initCore (opCore 3) coreLenProc (opCore 5) lastInit rebuildOffReadyProc)
      branchB))
    (hGSup : G.E.sup id ≤ G.m) (hGM : G.m = m) (hM0Le : cfg.P.M₀ ≤ m + mThresh)
    (hB : OrdChainCoreBranchBPostKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      wordExp stretchPrec intCapMax forestEdgeCap vCap eCap cfg G reembFn Rcore p coreSpace
      coreFixed toolMul treeMul B_bound R_bound (ordChainUpdateCoreBodyKFBL
        (wireBranchAKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg
          refreshAccountsProc dgApply updateLen0Proc (opCore 2) renameProc compactProc
          sortedEndsProc initCore (opCore 3) coreLenProc (opCore 5) lastInit rebuildOffReadyProc)
        branchB)) :
    OrdChainUpdateCoreSpecWExtKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      wordExp stretchPrec intCapMax forestEdgeCap vCap eCap cfg G reembFn Rcore p
      ordChainCoreProc coreSpace coreFixed toolMul treeMul B_bound R_bound := by
  refine ⟨_, hProc, ?_⟩
  intro root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok U B R tr gVec lVec
    modelPre hRep0 hMeta0 hCaps0 hIntCapEq hExtM hNum0 hOffInv0 hOffBd0 hBle hRle hShift hWire
    hBran hModelInv hModelInvKFBL hIntCapMax hForestCap hLogW hCapT hMemEq hFresh hTrNf hBatch
    hSmall hEdits hEditsW hEdHeap hRef hFootLt hGLt hLLt hULe hz0 hRoom
  by_cases hFire :
      intRebuildThreshold cfg.P cfg.N₀ 0 < model.chain.updCount 0 + tr.2.2.2.2.length
  · exact ordChainUpdateCoreBodyKFBL_post_A (pos := pos) (ω := ω) (treeMul := treeMul)
      (B_bound := B_bound) (R_bound := R_bound) (reembFn := reembFn) (V := V) (psi := psi)
      (k := k) (epsExp := epsExp) E hExtM hGSup hGM hM0Le hRep0 hMeta0 hCaps0 hIntCapEq hNum0
      hOffInv0 hOffBd0 hBle hRle hModelInv hModelInvKFBL hIntCapMax hForestCap hLogW hCapT
      hMemEq hFresh hTrNf hBatch hSmall hEdHeap hRef hFootLt hGLt hLLt hULe hz0 hRoom hFire
  · exact hB root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok U B R hRep0 hMeta0
      hCaps0 hIntCapEq hExtM hNum0 hOffInv0 hOffBd0 hBle hRle hShift hWire hBran hModelInv
      hModelInvKFBL hIntCapMax hForestCap hLogW hCapT hMemEq hFresh hTrNf hBatch hSmall hEdits
      hEditsW hEdHeap hRef hFootLt hGLt hLLt hULe hz0 hRoom hFire

end MinCostFlow.MinRatio
