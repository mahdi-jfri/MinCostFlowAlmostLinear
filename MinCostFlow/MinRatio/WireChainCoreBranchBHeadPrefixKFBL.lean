module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunHeadKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBFrontRepKFBL
import MinCostFlow.MinRatio.WireChainCoreBodyKFBL
import WordRAM.Tactic

/-!
# The dispatch and the prefix of the head of Branch B (`WireChainCoreBranchBHeadPrefixKFBL`)

The first part of a head of a run of Branch B (`BranchBRunHeadKFBL`): Phase 0 and the test
(`ordChainUpdateCoreBodyKFBL_dispatch`), and the prefix (Sync 1 and the refresh of level `0`,
`wireBranchBPrefixKFBL_runs`) at the edge cap `ec0 := eCap` of the level graphs.
`branchBHead_prefix` gives the state `st` after the test with its registers, the Branch B case of
the dispatch as a run of the whole core, and the facts after the prefix `BranchBPrefixFactsKFBL`.
The test does not fire (`noFire` of the start), so the core runs Branch B.

The premises of the prefix come from the start (`BranchBStartKFBL`): the caps of level `0`
(`dynGraphAt_caps_eq`), the tags of the length block of level `0`, the pointers to the old last
forest (`branchBOldTermForest_of_rep`), and the room from `spaceTotalBranchB`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The prefix of Branch B at `ec0 := eCap`, from the state `st` after the test. -/
private theorem branchBHead_prefixRun
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
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
    (EA : BranchAEnvKFBL w L P m capExp capLimit fcap lastMul intCapMax forestEdgeCap drainUnit
      edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy isNeg
      refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply updateLen0Proc
      initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc signExt mul
      intDiv lastInit rebuildOffReadyProc coreSpace coreFixed toolMul fmt cfg G Psc levelSpace
      levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Rcore p opTree opCore
      opLast stepCap)
    (EB : BranchBEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc collectProc edgeProc signExt mul intDiv copy collectDel emitCuts zeroIns
      filterEdits pushInsProc pushProc isNeg fmt cfg Psc allocation Ginit reembFn Rcore p opCore)
    (S : BranchBStartKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp
      stretchPrec intCapMax forestEdgeCap vCap eCap cfg G Rcore coreSpace root uIntBuf editsPtr
      editWords g l heap mem0 mem model tok U B R)
    {st : State} (hStMem : st.mem = mem)
    (hRegs : st.regs 4 = heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ∧
      st.regs 70 = root ∧ st.regs 71 = 0 ∧ st.regs 73 = tok.handle ∧ st.regs 75 = cfg.P.d ∧
      st.regs 77 = tok.handle + 18 ∧ st.regs 78 = tok.handle + 18 + (cfg.P.d + 1) ∧
      st.regs 80 = heap + 1 + 12 * cfg.P.d ∧
      st.regs 83 = solverLevelMetaAddr tok.table cfg.P.d ∧ st.regs 87 = uIntBuf ∧
      st.regs 90 = g ∧ st.regs 91 = l ∧ st.regs 94 = L) :
      ∃ (sP : State) (cP hS1 heap2 : ℕ) (memS1 : ℕ → ℕ) (curTree1 : PathTreeState)
      (curTreeTok1 : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ) (offCnt1 : ℕ)
      (canonVal0 canonVal : ℕ → PathEdgeValue),
      BranchBPrefixFactsKFBL w L P m drainUnit collectDel emitCuts bind canonCopy isNeg zeroIns
        refreshAccountsProc updateLen0Proc root uIntBuf g l heap eCap
        (mem0 (mem0 (tok.termHandle + 1 + model.chain.lastBran) + 1)) p opTree ω mem0 mem st
        model tok U B R sP cP hS1 heap2 memS1 curTree1 curTreeTok1 offCnt1 canonVal0
        canonVal := by
  have hdPos : 0 < cfg.P.d := S.modelInv.1.1
  have hUH : uIntBuf ≤ heap := by have := S.uLe; have := S.edHeap; omega
  have hSpB := EA.ops.spaceTotalBranchB U.length
  have hRoomH := S.room
  -- the premises of the prefix
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hWire0, hTags0⟩ := S.rep0
  obtain ⟨hOwn, _, _, _, hT4, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hTags0
  have hLt {x : ℕ} (ht : tok.tag x ≠ 0) : x < uIntBuf := S.footLt x (Or.inl (hOwn x ht))
  set lm := solverLevelMetaAddr tok.table cfg.P.d
  set tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  obtain ⟨_, _, _, _, _, _, _, _, ⟨hRootEq, vcOf, ecOf, hLev, _, _⟩, hBatchCaps, hG0'Cap, _⟩ :=
    S.modelInv
  have hCap0 : vcOf 0 = vCap ∧ ecOf 0 = eCap :=
    dynGraphAt_caps_eq (hLev 0 hdPos).1 (S.caps0 0 hdPos)
  have hRootCap : model.extG.n = vCap ∧ tok.rootECap = eCap := by
    have hDG0 := S.caps0 0 hdPos
    rw [hRootEq] at hDG0
    exact dynGraphAt_caps_eq hWire0.2.1 hDG0
  have hTagL0 : ∀ x, mem0 lm ≤ x → x < mem0 lm + eCap * L → tok.tag x = 23 + cfg.P.d := by
    intro x h1 h2
    have hL := (hLev 0 hdPos).2.2.2.1
    rw [add_zero, hCap0.2] at hL
    exact hL x h1 h2
  have hLevel0Meta :
      EdgeValuesAt mem0 (mem0 lm) 4 L P (model.chain.G 0).E
        (model.chain.toTreeChain.chainLen model.chain.ℓ 0) ∧
      (∀ x, mem0 lm ≤ x → x < mem0 lm + eCap * L → tok.tag x = 23 + cfg.P.d) ∧
      (∀ e ∈ (model.chain.G 0).E, e < eCap) ∧
      (∀ e ∈ ((model.chain.G 0).applyBatch tr.2.2.2.2).E, e < eCap) ∧
      (∀ u ∈ tr.2.2.2.2, match u with | .insert ei _ _ => ei < eCap | _ => True) := by
    refine ⟨by simpa [lm] using (hLev 0 hdPos).2.1, hTagL0, (S.caps0 0 hdPos).2.2.1,
      fun e he => by rw [← hRootCap.2]; exact (hG0'Cap e he).1, fun u hu => ?_⟩
    have hU := hBatchCaps u hu
    cases u with
    | insert ei _ _ => rw [← hRootCap.2]; exact hU
    | delete _ => trivial
    | split _ _ _ _ => trivial
  have hOldT := branchBOldTermForest_of_rep S.rep0 S.modelInv
  dsimp only at hOldT
  obtain ⟨hTermH0, hTermB0, hTagT1, hTagT2, _, _⟩ := hOldT
  set lsfHdr := mem0 (tok.termHandle + 1 + model.chain.lastBran)
  set forestPtr := mem0 (lsfHdr + 1)
  have hHB0Lt : tok.handle + 18 + cfg.P.d < uIntBuf :=
    hLt (by rw [hT4 cfg.P.d (by omega)]; decide)
  have hBB0Lt : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d < uIntBuf := by
    have h1 : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d = tok.handle + 18 + (2 * cfg.P.d + 1) := by
      omega
    rw [h1]
    exact hLt (by rw [hT4 (2 * cfg.P.d + 1) (by omega)]; decide)
  have hTermHMem : mem (tok.handle + 18 + cfg.P.d) = tok.termHandle := by
    rw [S.memEq _ hHB0Lt (by rw [hT4 cfg.P.d (by omega)]; decide)
      (by rw [hT4 cfg.P.d (by omega)]; decide) (by rw [hT4 cfg.P.d (by omega)]; decide)]
    exact hTermH0
  have hTermBMem : mem (tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d) = model.chain.lastBran := by
    have h1 : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d = tok.handle + 18 + (2 * cfg.P.d + 1) := by
      omega
    rw [S.memEq _ hBB0Lt (by rw [h1, hT4 (2 * cfg.P.d + 1) (by omega)]; decide)
      (by rw [h1, hT4 (2 * cfg.P.d + 1) (by omega)]; decide)
      (by rw [h1, hT4 (2 * cfg.P.d + 1) (by omega)]; decide)]
    exact hTermB0
  have hT1Lt : tok.termHandle + 1 + model.chain.lastBran < uIntBuf :=
    hLt (by rw [hTagT1]; decide)
  have hT2Lt : lsfHdr + 1 < uIntBuf := hLt (by rw [hTagT2]; decide)
  have hLsfHdrMem : mem (tok.termHandle + 1 + model.chain.lastBran) = lsfHdr :=
    (S.memEq _ hT1Lt (by rw [hTagT1]; decide) (by rw [hTagT1]; decide)
      (by rw [hTagT1]; decide))
  have hForestPtrMem : mem (lsfHdr + 1) = forestPtr :=
    (S.memEq _ hT2Lt (by rw [hTagT2]; decide) (by rw [hTagT2]; decide)
      (by rw [hTagT2]; decide))
  have hRoomPre : heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 + 3 * U.length +
      U.length * wireTreeSyncEditSpace L + 1 + 3 * L + U.length * wireRefreshOneSpace L <
      2 ^ w := by
    omega
  exact wireBranchBPrefixKFBL_runs (ec0 := eCap) (termHandle := tok.termHandle)
      (lastBran := model.chain.lastBran) (lsfHdr := lsfHdr) (forestPtr := forestPtr)
      EB.collectP EB.emitP EB.zeroP EA.refAccP EA.refOneP EA.updLen0P
      EA.four EA.lPos EA.pW EA.w18 EA.treeImpl EA.bindC EA.canonC
      EA.isNegC EA.shiftC EA.divC EA.addC EA.subC EA.negC EA.copyC
      S.rep0 S.meta0 S.num0 S.offInv0 S.offBd0 S.modelInv
      S.logW S.capT S.refresh S.memEq S.fresh S.trNf
      S.batch S.small S.footLt S.gLt S.lLt S.uLe S.edHeap
      hLevel0Meta S.zero hStMem
      hRegs
      hTermHMem hTermBMem hLsfHdrMem hForestPtrMem (by omega) (by omega) (by omega) hRoomPre


/-- **The dispatch and the prefix of Branch B.** From the environments and the start, the state
`st` after Phase 0 and the test with its registers, the Branch B case of the dispatch, and the
facts after the prefix at `ec0 := eCap`, with the pointer `forestPtr` to the old last forest. -/
theorem branchBHead_prefix
    {w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
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
    (EA : BranchAEnvKFBL w L P m capExp capLimit fcap lastMul intCapMax forestEdgeCap drainUnit
      edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy isNeg
      refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply updateLen0Proc
      initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc signExt mul
      intDiv lastInit rebuildOffReadyProc coreSpace coreFixed toolMul fmt cfg G Psc levelSpace
      levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Rcore p opTree opCore
      opLast stepCap)
    (EB : BranchBEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc collectProc edgeProc signExt mul intDiv copy collectDel emitCuts zeroIns
      filterEdits pushInsProc pushProc isNeg fmt cfg Psc allocation Ginit reembFn Rcore p opCore)
    (S : BranchBStartKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp
      stretchPrec intCapMax forestEdgeCap vCap eCap cfg G Rcore coreSpace root uIntBuf editsPtr
      editWords g l heap mem0 mem model tok U B R) :
    ∃ (st : State) (c0 : ℕ),
      (st.mem = mem ∧ c0 ≤ 210 ∧
        (st.regs 4 = heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ∧ st.regs 70 = root ∧
          st.regs 71 = 0 ∧ st.regs 72 = heap ∧ st.regs 73 = tok.handle ∧ st.regs 75 = cfg.P.d ∧
          st.regs 76 = cfg.P.k ∧ st.regs 77 = tok.handle + 18 ∧
          st.regs 78 = tok.handle + 18 + (cfg.P.d + 1) ∧ st.regs 79 = cfg.P.d + 1 ∧
          st.regs 80 = heap + 1 + 12 * cfg.P.d ∧
          st.regs 81 = heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) ∧
          st.regs 82 = solverLvlMAddr tok.table cfg.P.d ∧
          st.regs 83 = solverLevelMetaAddr tok.table cfg.P.d ∧
          st.regs 85 = tok.levelsEnd + 3 * (cfg.P.d + 1) ∧
          st.regs 86 = tok.levelsEnd + 2 * (cfg.P.d + 1) ∧ st.regs 87 = uIntBuf ∧
          st.regs 90 = g ∧ st.regs 91 = l ∧
          st.regs 92 = heap + 1 + 12 * cfg.P.d + 2 * (cfg.P.d + 1) ∧
          st.regs 93 = heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) ∧ st.regs 94 = L ∧
          st.regs 95 = P ∧ st.regs 98 = Expander.chosenL (cfg.P.M₀ ^ 2)) ∧
        (st.regs 74 = tok.table ∧ st.regs 84 = tok.levelsEnd ∧ st.regs 88 = editsPtr ∧
          st.regs 89 = editWords)) ∧
      (∀ (o : Outcome) (out : State) (c : ℕ),
        Runs w p ω (wireBranchBKFBL collectDel emitCuts packEditsProc filterEdits zeroIns
          refreshAccountsProc updateLen0Proc copyProc updLen slotProc pushInsProc bind canonCopy
          isNeg dgApply initCore coreLenProc lastInit opTree opCore) st o out c →
        Runs w p ω (ordChainUpdateCoreBodyKFBL
          (wireBranchAKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg
            refreshAccountsProc dgApply updateLen0Proc (opCore 2) renameProc compactProc
            sortedEndsProc initCore (opCore 3) coreLenProc (opCore 5) lastInit rebuildOffReadyProc)
          (wireBranchBKFBL collectDel emitCuts packEditsProc filterEdits zeroIns
            refreshAccountsProc updateLen0Proc copyProc updLen slotProc pushInsProc bind canonCopy
            isNeg dgApply initCore coreLenProc lastInit opTree opCore))
          (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos) o out (c0 + c)) ∧
      ∃ (sP : State) (cP hS1 heap2 : ℕ) (memS1 : ℕ → ℕ) (curTree1 : PathTreeState)
        (curTreeTok1 : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ) (offCnt1 : ℕ)
        (canonVal0 canonVal : ℕ → PathEdgeValue),
        BranchBPrefixFactsKFBL w L P m drainUnit collectDel emitCuts bind canonCopy isNeg zeroIns
          refreshAccountsProc updateLen0Proc root uIntBuf g l heap eCap
          (mem0 (mem0 (tok.termHandle + 1 + model.chain.lastBran) + 1)) p opTree ω mem0 mem st
          model tok U B R sP cP hS1 heap2 memS1 curTree1 curTreeTok1 offCnt1 canonVal0
          canonVal := by
  have hdPos : 0 < cfg.P.d := S.modelInv.1.1
  have hUH : uIntBuf ≤ heap := by have := S.uLe; have := S.edHeap; omega
  have hSpB := EA.ops.spaceTotalBranchB U.length
  have hRoomH := S.room
  -- Phase 0 and the test
  have hModelInv := S.modelInv
  obtain ⟨_, _, _, _, _, _, _, _, ⟨_, _, _, _, _, hLoop⟩, _⟩ := hModelInv
  have hSumW := updateLoopModelInv_sum_lt hdPos hLoop
  have hHeapW : heap + (1 + 12 * cfg.P.d) + 3 * (cfg.P.d + 1) + 4 < 2 ^ w := by omega
  obtain ⟨st, c0, hStMem, hc0, hRegs, hRegs2, hRun⟩ :=
    ordChainUpdateCoreBodyKFBL_dispatch (p := p) (ω := ω) (pos := pos) (editWords := editWords)
      (branchA := wireBranchAKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy
        isNeg refreshAccountsProc dgApply updateLen0Proc (opCore 2) renameProc compactProc
        sortedEndsProc initCore (opCore 3) coreLenProc (opCore 5) lastInit rebuildOffReadyProc)
      (branchB := wireBranchBKFBL collectDel emitCuts packEditsProc filterEdits zeroIns
        refreshAccountsProc updateLen0Proc copyProc updLen slotProc pushInsProc bind canonCopy
        isNeg dgApply initCore coreLenProc lastInit opTree opCore)
      S.rep0 S.meta0 S.memEq S.footLt S.small hdPos EA.w18 hUH hHeapW hSumW
  refine ⟨st, c0, ⟨hStMem, hc0, hRegs, hRegs2⟩,
    fun o out c h => (hRun o out c).2 S.noFire h, ?_⟩
  obtain ⟨r4, r70, r71, _, r73, r75, _, r77, r78, _, r80, _, _, r83, _, _, r87, r90, r91, _, _,
    r94, _, _⟩ := hRegs
  exact branchBHead_prefixRun (pos := pos) (ω := ω) EA EB S hStMem
    ⟨r4, r70, r71, r73, r75, r77, r78, r80, r83, r87, r90, r91, r94⟩
end MinCostFlow.MinRatio
