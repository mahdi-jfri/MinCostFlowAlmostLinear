module

public import MinCostFlow.MinRatio.WireChainCoreBodyKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchAAllKFBL
import WordRAM.Tactic

/-!
# The chain core when level `0` is rebuilt (`WireChainCoreBodyAKFBL`)

This file proves the conclusion of `OrdChainUpdateCoreSpecWExtKFBL` (as
`OrdChainCoreExtPost`) for the chain core `ordChainUpdateCoreBodyKFBL`, in the case where the
rebuild test at level `0` fires. Phase 0 and the test (`ordChainUpdateCoreBodyKFBL_dispatch`)
lead to the state from which Branch A runs (`wireBranchAKFBL_runs`). Branch A rebuilds every
level, so the first rebuilt level is `0`, no level forwards a batch, and the bounds `B` and `R`
do not change.

The cost of Branch A is at most the left side of `costTotalBranchA` less `1000`, and Phase 0
with the test takes at most `210` steps. The field `costTotalBranchA` needs
`model.extG.m = m`, which the premises of `OrdChainUpdateCoreSpecWExtKFBL` do not give. So the
result takes it as a premise, along with three facts on the
parameters `G`, `m` and `mThresh`. The only result used later is
`ordChainUpdateCoreBodyKFBL_post_A`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The cost bound of the whole core in Branch A, over plain numbers: Phase 0 and the test take
`c0 ≤ 210` steps, Branch A leaves `1000` steps of the bound `X`, and `X ≤ Y`. -/
private theorem coreA_cost_arith {c0 cost phi' X phi0 Y Z S : ℕ} (hc0 : c0 ≤ 210)
    (h1 : cost + phi' + 1000 ≤ X + phi0) (h2 : X ≤ Y) (hS : S = 0) :
    c0 + cost + phi' ≤ Y + Z + 40 * S + phi0 := by
  subst hS; omega

/-- The first loop step of `UpdateLoopModelInv` keeps the update counter of level `0`, plus the
length of the batch, below `2 ^ w`. -/
theorem updateLoopModelInv_sum_lt {w L P wordExp stretchPrec : ℕ} {cfg : Alg2Config}
    {vcOf ecOf : ℕ → ℕ} {origLen : ℕ → ℕ → ℝ} {ℓ' g' : ℕ → ℝ} {st : ChainState cfg.T cfg.P}
    {curG : MGraph} {curU : List Update} {curEnc : ℕ} {oldOrd : ℕ → List End}
    (hd : 0 < cfg.P.d)
    (h : UpdateLoopModelInv w L P wordExp stretchPrec vcOf ecOf origLen ℓ' g' cfg.P.d 0 st curG
      curU curEnc oldOrd) :
    st.updCount 0 + curU.length < 2 ^ w := by
  obtain ⟨d', hd'⟩ : ∃ d', cfg.P.d = d' + 1 := ⟨cfg.P.d - 1, by omega⟩
  rw [hd'] at h
  unfold UpdateLoopModelInv at h
  exact h.1

/-- The chain core with Branch A, when the rebuild test at level `0` fires: the conclusion of
`OrdChainUpdateCoreSpecWExtKFBL` holds with `B' = B`, `R' = R` and first rebuilt level `0`.
The premises are those of `OrdChainUpdateCoreSpecWExtKFBL` that Branch A reads, the test
outcome `hFire`, and the facts `hExtM`, `hGSup`, `hGM`, `hM0Le` that `costTotalBranchA` needs. -/
theorem ordChainUpdateCoreBodyKFBL_post_A
    {w L P m V psi k epsExp drainUnit capExp capLimit fcap lastMul intCapMax forestEdgeCap edMul
      mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy isNeg
      refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc root uIntBuf editsPtr editWords g l heap
      pos : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul treeMul : ℕ} {B_bound R_bound : ℤ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ} {branchB : Stmt}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}
    {stepCap : ℕ → ℕ → ℕ}
    (E : BranchAEnvKFBL w L P m capExp capLimit fcap lastMul intCapMax forestEdgeCap drainUnit
      edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy isNeg
      refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply updateLen0Proc
      initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc signExt mul
      intDiv lastInit rebuildOffReadyProc coreSpace coreFixed toolMul fmt cfg G Psc levelSpace
      levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Rcore p opTree opCore
      opLast stepCap)
    (hExtM : model.extG.m = m) (hGSup : G.E.sup id ≤ G.m) (hGM : G.m = m)
    (hM0Le : cfg.P.M₀ ≤ m + mThresh)
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hIntCapEq : tok.intCap = initTargetCap cfg G)
    (hNum0 : PathTreeNumericInv tok.tree tok.trees B R)
    (hOffInv0 : OffTreeRecInv model L mem0 tok.edgeRecords B)
    (hOffBd0 : OffTreeRecBound model L mem0 tok.edgeRecords B)
    (hBle : B ≤ B_bound) (hRle : R ≤ R_bound)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B)
    (hModelInvKFBL :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      UpdateCoreModelInvKFBL model U gVec lVec)
    (hIntCapMax : tok.intCap ≤ intCapMax)
    (hForestCap :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      graphListEdgeSum (chainSuffixForests model.chain 0) +
        graphListEdgeSum (chainSuffixForests modelPre.chain 0) ≤ forestEdgeCap)
    (hLogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hCapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hMemEq : ∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a)
    (hFreshMem :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
        tr.2.1 tr.2.2.1 tr.2.2.2.1)
    (hTrNfLe :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      tr.2.2.2.1 ≤ tok.intCap)
    (hBatchMem :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      BatchAt mem uIntBuf tr.2.2.2.2)
    (hSmallMem :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      SmallBatchAt mem uIntBuf (model.chain.G 0) tr.2.2.2.2 (editsPtr - cfg.P.d - uIntBuf))
    (hEdHeap : editsPtr + editWords = heap)
    (hRef : RefreshBatch model.extG U)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hGLt : g + m * L ≤ uIntBuf) (hLLt : l + m * L ≤ uIntBuf)
    (hULeEd : uIntBuf + cfg.P.d ≤ editsPtr)
    (hz0 : ZeroFrom mem heap) (hRoom : heap + coreSpace U.length < 2 ^ w)
    (hFire :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      intRebuildThreshold cfg.P cfg.N₀ 0 < model.chain.updCount 0 + tr.2.2.2.2.length) :
    OrdChainCoreExtPost w L P m V psi k epsExp drainUnit capExp vCap eCap cfg reembFn Rcore p
      coreSpace coreFixed toolMul treeMul B_bound R_bound
      (ordChainUpdateCoreBodyKFBL
        (wireBranchAKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg
          refreshAccountsProc dgApply updateLen0Proc (opCore 2) renameProc compactProc
          sortedEndsProc initCore (opCore 3) coreLenProc (opCore 5) lastInit
          rebuildOffReadyProc)
        branchB)
      root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok U := by
  unfold OrdChainCoreExtPost
  dsimp only at hModelInvKFBL hForestCap hFreshMem hTrNfLe hBatchMem hSmallMem hFire ⊢
  have hModelInv_keep := hModelInv
  obtain ⟨⟨hdPos, _⟩, ⟨hN0Eq, _, hRootCapLe⟩, _, _, _, _, _, _, ⟨_, _, _, _, _, hLoop⟩, _⟩ :=
    hModelInv
  have hFreshInv0 := hRep0.2.2.2.2.1
  have hOver : intRebuildThreshold cfg.P model.chain.N₀ 0 < model.chain.updCount 0 +
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2.length :=
    by rw [hN0Eq]; exact hFire
  have hSumW := updateLoopModelInv_sum_lt hdPos hLoop
  have hSpB := E.ops.spaceTotalBranchB U.length
  have hHeapW : heap + (1 + 12 * cfg.P.d) + 3 * (cfg.P.d + 1) + 4 < 2 ^ w := by omega
  -- Phase 0 and the test
  obtain ⟨st, c0, hStMem, hc0, hRegs, -, hRun⟩ :=
    ordChainUpdateCoreBodyKFBL_dispatch (p := p) (ω := ω) (pos := pos) (editWords := editWords)
      (branchA := wireBranchAKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy
        isNeg refreshAccountsProc dgApply updateLen0Proc (opCore 2) renameProc compactProc
        sortedEndsProc initCore (opCore 3) coreLenProc (opCore 5) lastInit rebuildOffReadyProc)
      (branchB := branchB)
      hRep0 hMeta0 hMemEq hFootLt hSmallMem hdPos E.w18 (by omega) hHeapW hSumW
  -- Branch A
  obtain ⟨nextHeap, cost, out, tok', levelU, levelUS, diffLists, hRunA, hLo, hHi, hLE, hIC, hRE,
    hTab, hRep, hMeta, hCaps, hLmd, hNum, hOffInv, hOffBd, hSH, hSB, hSel, hZ, hFr, hFoot,
    hCost, _⟩ :=
    wireBranchAKFBL_runs E hRep0 hMeta0 hCaps0 hNum0 hOffInv0 hOffBd0 hModelInv_keep
      hModelInvKFBL hIntCapMax hForestCap hLogW hCapT hMemEq hFreshMem hTrNfLe hBatchMem
      hSmallMem hRef hFootLt hGLt hLLt hULeEd (by omega) hz0 hRoom hOver hStMem hRegs
  obtain ⟨-, hRenTrue⟩ := branchA_modelPre_chain_eq model U
    (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
    (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ) hdPos hN0Eq hOver
  have hFirst : firstRebuiltLevel cfg.P.d model.chain.rebuildCount
      (alg2PreResetState cfg model U
        (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
        (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ)).chain.rebuildCount
      = some 0 := by
    unfold level0Rebuilt at hRenTrue; exact of_decide_eq_true hRenTrue
  have hCostA := E.ops.costTotalBranchA model U
    (updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg)
    (updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ) tok.intCap
    tok.rootECap hdPos hOver hFreshInv0 hRef hModelInvKFBL hExtM hRootCapLe (le_of_eq hIntCapEq)
    hGSup hGM hM0Le
  refine ⟨nextHeap, c0 + cost, out, tok', B, R, 0, levelU, levelUS, diffLists,
    (hRun _ _ _).1 hFire hRunA, hLo, hHi, hLE, hIC, hRE, hTab, hBle, hRle, hRep, hMeta, hCaps,
    hLmd, hNum, hOffInv, hOffBd, hSH, hSB, ?_, hSel, hZ, hFr, hFoot,
    coreA_cost_arith hc0 hCost hCostA (by simp)⟩
  -- the level link at first rebuilt level `0`
  exact ⟨by omega, fun _ => hFirst, fun h => absurd h (by omega), fun h => absurd h (by omega),
    fun j hj => absurd hj (by simp), fun h => absurd h (by omega)⟩

/-- **The level-metadata disjointness clause on the end state of Branch A.** When the rebuild
test at level `0` fires, every run of the chain core `ordChainUpdateCoreBodyKFBL` with Branch A
`wireBranchAKFBL`
ends in a state whose level graph and length blocks are pairwise disjoint
(`SolverLevelMetaDisjAt vCap eCap tok' out.mem`) for any token `tok'` with `tok'.table = tok.table`. -/
theorem ordChainUpdateCoreBodyKFBL_metaDisj_A
    {w L P m V psi k epsExp drainUnit capExp capLimit fcap lastMul intCapMax forestEdgeCap edMul
      mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy isNeg
      refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
      updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
      signExt mul intDiv lastInit rebuildOffReadyProc root uIntBuf editsPtr editWords g l heap
      pos nextHeap cost : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opTree opCore opLast : ℕ → ℕ}
    {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ} {branchB : Stmt} {out : State}
    {model : Alg2State cfg} {tok tok' : SolverToken cfg L Rcore} {U : List Update} {B R : ℤ}
    {stepCap : ℕ → ℕ → ℕ}
    (E : BranchAEnvKFBL w L P m capExp capLimit fcap lastMul intCapMax forestEdgeCap drainUnit
      edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy isNeg
      refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply updateLen0Proc
      initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc signExt mul
      intDiv lastInit rebuildOffReadyProc coreSpace coreFixed toolMul fmt cfg G Psc levelSpace
      levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Rcore p opTree opCore
      opLast stepCap)
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hNum0 : PathTreeNumericInv tok.tree tok.trees B R)
    (hOffInv0 : OffTreeRecInv model L mem0 tok.edgeRecords B)
    (hOffBd0 : OffTreeRecBound model L mem0 tok.edgeRecords B)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B)
    (hModelInvKFBL :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      UpdateCoreModelInvKFBL model U gVec lVec)
    (hIntCapMax : tok.intCap ≤ intCapMax)
    (hForestCap :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      graphListEdgeSum (chainSuffixForests model.chain 0) +
        graphListEdgeSum (chainSuffixForests modelPre.chain 0) ≤ forestEdgeCap)
    (hLogW : Nat.log 2 (2 * model.extG.n + 1) ≤ 4 * L)
    (hCapT : 2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hMemEq : ∀ a < uIntBuf, tok.tag a ≠ 6 → tok.tag a ≠ 7 → tok.tag a ≠ 8 → mem a = mem0 a)
    (hFreshMem :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      FreshTablesAt mem tok.forward tok.inverse tok.freshCounter m tok.intCap
        tr.2.1 tr.2.2.1 tr.2.2.2.1)
    (hTrNfLe :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      tr.2.2.2.1 ≤ tok.intCap)
    (hBatchMem :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      BatchAt mem uIntBuf tr.2.2.2.2)
    (hSmallMem :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      SmallBatchAt mem uIntBuf (model.chain.G 0) tr.2.2.2.2 (editsPtr - cfg.P.d - uIntBuf))
    (hEdHeap : editsPtr + editWords = heap)
    (hRef : RefreshBatch model.extG U)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < uIntBuf)
    (hGLt : g + m * L ≤ uIntBuf) (hLLt : l + m * L ≤ uIntBuf)
    (hULeEd : uIntBuf + cfg.P.d ≤ editsPtr)
    (hz0 : ZeroFrom mem heap) (hRoom : heap + coreSpace U.length < 2 ^ w)
    (hFire :
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      intRebuildThreshold cfg.P cfg.N₀ 0 < model.chain.updCount 0 + tr.2.2.2.2.length)
    (hRunOut : Runs w p ω
      (ordChainUpdateCoreBodyKFBL
        (wireBranchAKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg
          refreshAccountsProc dgApply updateLen0Proc (opCore 2) renameProc compactProc
          sortedEndsProc initCore (opCore 3) coreLenProc (opCore 5) lastInit
          rebuildOffReadyProc)
        branchB)
      (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
      (.returned nextHeap) out cost)
    (htab : tok'.table = tok.table) :
    SolverLevelMetaDisjAt vCap eCap tok' out.mem := by
  dsimp only at hModelInvKFBL hForestCap hFreshMem hTrNfLe hBatchMem hSmallMem hFire
  have hModelInv_keep := hModelInv
  obtain ⟨⟨hdPos, _⟩, ⟨hN0Eq, _, _⟩, _, _, _, _, _, _, ⟨_, _, _, _, _, hLoop⟩, _⟩ := hModelInv
  have hOver : intRebuildThreshold cfg.P model.chain.N₀ 0 < model.chain.updCount 0 +
      (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2.length :=
    by rw [hN0Eq]; exact hFire
  have hSumW := updateLoopModelInv_sum_lt hdPos hLoop
  have hSpB := E.ops.spaceTotalBranchB U.length
  have hHeapW : heap + (1 + 12 * cfg.P.d) + 3 * (cfg.P.d + 1) + 4 < 2 ^ w := by omega
  obtain ⟨st, _, hStMem, _, hRegs, -, hRun⟩ :=
    ordChainUpdateCoreBodyKFBL_dispatch (p := p) (ω := ω) (pos := pos) (editWords := editWords)
      (branchA := wireBranchAKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy
        isNeg refreshAccountsProc dgApply updateLen0Proc (opCore 2) renameProc compactProc
        sortedEndsProc initCore (opCore 3) coreLenProc (opCore 5) lastInit rebuildOffReadyProc)
      (branchB := branchB)
      hRep0 hMeta0 hMemEq hFootLt hSmallMem hdPos E.w18 (by omega) hHeapW hSumW
  obtain ⟨nextHeap₁, cost₁, out₁, tok₁, _, _, _, hRunA, _, _, _, _, _, hTab₁, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, hMetaDisj₁⟩ :=
    wireBranchAKFBL_runs (reembFn := reembFn) E hRep0 hMeta0 hCaps0 hNum0 hOffInv0 hOffBd0
      hModelInv_keep hModelInvKFBL hIntCapMax hForestCap hLogW hCapT hMemEq hFreshMem hTrNfLe
      hBatchMem hSmallMem hRef hFootLt hGLt hLLt hULeEd (by omega) hz0 hRoom hOver hStMem hRegs
  have hOutEq : out₁ = out := (Runs.det ((hRun _ _ _).1 hFire hRunA) hRunOut).2.1
  rw [← hOutEq]
  exact hMetaDisj₁.of_agree (htab.trans hTab₁.symm) (fun _ _ => rfl)

end MinCostFlow.MinRatio
