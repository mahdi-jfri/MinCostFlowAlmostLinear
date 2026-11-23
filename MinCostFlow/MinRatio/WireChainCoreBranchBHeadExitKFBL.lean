module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunHeadKFBL

/-!
# The head of Branch B in two parts (`WireChainCoreBranchBHeadExitKFBL`)

The head of a run of Branch B (`BranchBRunHeadKFBL`) ends after the exit of the loop. This file
cuts it at the start of the exit.

* `BranchBRunPreExitKFBL`: the run up to the exit of the loop of plain steps: the fields of
  `BranchBRunHeadKFBL` up to `loop` (same names, same parameters), and `ec0_eq`, `levelU0` and
  `dispatchRuns`.
* `BranchBHeadExitGoalKFBL`: from the four exit goals and such a run, the exit: the
  state `sX` after it with the facts `BranchBExitOutKFBL` and `BranchBExitCaseKFBL`, the model `X`
  after the update equal to the chain of `alg2PreResetState`, the places of the forests
  (`BranchBExitForestLocKFBL`) and the order of the rebuilt blocks at `sX`.
* `BranchBRunPreExitGoalKFBL`: from the premises of the run goal, every start state
  has such a run.
* `branchBRunHeadGoal_of_preExit_exit` (proved): the head goal from the two.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- The run of Branch B up to the exit of the loop: the fields of `BranchBRunHeadKFBL` up to
`loop`, with `ec0_eq`, `levelU0` and `dispatchRuns`. -/
structure BranchBRunPreExitKFBL (w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
    lastMul
    intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
    bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
    dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
    edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
    collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc : ℕ)
    (coreSpace coreFixed : ℕ → ℕ) (toolMul : ℕ) (fmt : Num.Format w) (cfg : Alg2Config)
    (G : MGraph) (Psc : SparseCoreOrdParams) (levelSpace : ℕ → ℕ)
    (levelCost : ChainState cfg.T cfg.P → ℕ → ℕ) (updStepSpace : ℕ → ℕ → ℕ)
    (lastSpace termUpdSpace : ℕ) (allocation lastAlloc : ℕ → List ℕ → ℕ) (Ginit : ℕ → MGraph)
    (reembFn : ToolReembFn cfg.T) (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (p : Program)
    (opTree opCore opLast : ℕ → ℕ) (stepCap : ℕ → ℕ → ℕ)
    (root uIntBuf editsPtr editWords g l heap pos : ℕ) (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ)
    (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (U : List Update) (B R : ℤ) :
    Type where
  -- the environments and the tool facts
  envA : BranchAEnvKFBL w L P m capExp capLimit fcap lastMul intCapMax forestEdgeCap drainUnit
    edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy isNeg
    refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply updateLen0Proc
    initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc signExt mul
    intDiv lastInit rebuildOffReadyProc coreSpace coreFixed toolMul fmt cfg G Psc levelSpace
    levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Rcore p opTree opCore
    opLast stepCap
  envB : BranchBEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
    slotProc collectProc edgeProc signExt mul intDiv copy collectDel emitCuts zeroIns filterEdits
    pushInsProc pushProc isNeg fmt cfg Psc allocation Ginit reembFn Rcore p opCore
  toolStep : ∀ ch, ShiftLoopChainInv cfg ch → BranchBToolStepKFBL cfg stepCap ch
  shrink : BranchBForestShrinkKFBL cfg
  handleFoot : ∀ b s x mem, Rcore.rep b s x mem → Rcore.foot b x b
  tpValid : cfg.TP.Valid
  start : BranchBStartKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp
    stretchPrec intCapMax forestEdgeCap vCap eCap cfg G Rcore coreSpace root uIntBuf editsPtr
    editWords g l heap mem0 mem model tok U B R
  -- names for the batch, the new vectors and the new root graph
  Uint : List Update
  Uint_eq :
    Uint = (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.2.2
  gVec : ℕ → ℝ
  gVec_eq : gVec = updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
  lVec : ℕ → ℝ
  lVec_eq : lVec = updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
  ℓ' : ℕ → ℝ
  ℓ'_eq : ℓ' = fun e' =>
    lVec ((translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.1 e')
  g' : ℕ → ℝ
  g'_eq : g' = fun e' =>
    gVec ((translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).2.2.1 e')
  G1 : MGraph
  G1_eq : G1 = (model.chain.G 0).applyBatch Uint
  F1 : Finset ℕ
  F1_eq : F1 = model.chain.toTreeChain.chainTree.E \ (batchDeletedEdges Uint).toFinset
  -- Phase 0 and the test (`ordChainUpdateCoreBodyKFBL_dispatch`)
  st : State
  c0 : ℕ
  dispatch : st.mem = mem ∧ c0 ≤ 210 ∧
    (st.regs 4 = heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) + 4 ∧ st.regs 70 = root ∧
      st.regs 71 = 0 ∧ st.regs 72 = heap ∧ st.regs 73 = tok.handle ∧ st.regs 75 = cfg.P.d ∧
      st.regs 76 = cfg.P.k ∧ st.regs 77 = tok.handle + 18 ∧
      st.regs 78 = tok.handle + 18 + (cfg.P.d + 1) ∧ st.regs 79 = cfg.P.d + 1 ∧
      st.regs 80 = heap + 1 + 12 * cfg.P.d ∧
      st.regs 81 = heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1) ∧
      st.regs 82 = solverLvlMAddr tok.table cfg.P.d ∧
      st.regs 83 = solverLevelMetaAddr tok.table cfg.P.d ∧
      st.regs 85 = tok.levelsEnd + 3 * (cfg.P.d + 1) ∧
      st.regs 86 = tok.levelsEnd + 2 * (cfg.P.d + 1) ∧ st.regs 87 = uIntBuf ∧ st.regs 90 = g ∧
      st.regs 91 = l ∧ st.regs 92 = heap + 1 + 12 * cfg.P.d + 2 * (cfg.P.d + 1) ∧
      st.regs 93 = heap + 1 + 12 * cfg.P.d + 3 * (cfg.P.d + 1) ∧ st.regs 94 = L ∧
      st.regs 95 = P ∧ st.regs 98 = Expander.chosenL (cfg.P.M₀ ^ 2)) ∧
    (st.regs 74 = tok.table ∧ st.regs 84 = tok.levelsEnd ∧ st.regs 88 = editsPtr ∧
      st.regs 89 = editWords)
  -- the prefix (`wireBranchBPrefixKFBL_runs`)
  ec0 : ℕ
  forestPtr : ℕ
  sP : State
  cP : ℕ
  hS1 : ℕ
  heap2 : ℕ
  memS1 : ℕ → ℕ
  curTree1 : PathTreeState
  curTreeTok1 : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ
  offCnt1 : ℕ
  canonVal0 : ℕ → PathEdgeValue
  canonVal : ℕ → PathEdgeValue
  pre : BranchBPrefixFactsKFBL w L P m drainUnit collectDel emitCuts bind canonCopy isNeg zeroIns
    refreshAccountsProc updateLen0Proc root uIntBuf g l heap ec0 forestPtr p opTree ω mem0 mem st
    model tok U B R sP cP hS1 heap2 memS1 curTree1 curTreeTok1 offCnt1 canonVal0 canonVal
  -- the front (`wireBranchBFrontLoopKFBL_runs`)
  sF0 : State
  cF : ℕ
  front : Runs w p ω (wireBranchBFrontKFBL copyProc) sP .normal sF0 cF ∧
    cF ≤ 20 * (editsPtr - cfg.P.d - uIntBuf) + 60 ∧
    sF0.regs 4 = heap2 + (editsPtr - cfg.P.d - uIntBuf) ∧ (∀ a < heap2, sF0.mem a = sP.mem a) ∧
    (∀ r, r ≠ 4 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 30 → r ≠ 96 → r ≠ 97 → r ≠ 99 →
      sF0.regs r = sP.regs r)
  -- the loop (`wireBranchBFrontLoopKFBL_runs`, `BranchBLoopExitKFBL.exists_at`)
  st0 : ChainState cfg.T cfg.P
  st0_eq : st0 = { model.chain with
    recUpdates := fun j =>
      if j = 0 then model.chain.recUpdates 0 + Uint.length else model.chain.recUpdates j }
  A : BranchBAddrs
  A_eq : A = branchBAddrsOf tok mem0 heap heap2
  C : ℕ → ℕ × ℕ × ℕ
  C_eq : C = branchBTraceCaps edMul
    (fun j => SparseCore.bundleLogFactor (levelM cfg.TP cfg.P j) cfg.N₀)
    (editsPtr - cfg.P.d - uIntBuf) editWords Uint.length
    (branchBStepData cfg ℓ' g' cfg.P.d 0 st0 G1 Uint ((model.chain.G 0).batchEnc Uint))
  levelUS0 : ℕ → List Update
  D0 : ℕ → LevelDiffLists
  i₀ : ℕ
  sE : State
  sL : State
  cL : ℕ
  chE : ChainState cfg.T cfg.P
  curGE : MGraph
  curUE : List Update
  curEditsE : List OrdEdit
  curEncE : ℕ
  oldOrdE : ℕ → List End
  tokE : ℕ → Rcore.τ
  bE : ℕ
  bWE : ℕ
  eE : ℕ
  eWE : ℕ
  levelU : ℕ → List Update
  levelUS : ℕ → List Update
  D : ℕ → LevelDiffLists
  loop : BranchBLoopExitAtKFBL w L P depth vCap eCap capExp dgApply copyProc updLen slotProc
    wordExp stretchPrec cfg.N₀ fmt cfg Psc reembFn Rcore
    (LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
      (model.chain.G cfg.P.d).E) p opCore ω A
    (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ j) ℓ' g'
    (fun j => (C j).1) (fun j => (C j).2.1) (fun j => (C j).2.2)
    (fun j => updStepSpace j U.length) st0 tok.termTok cfg.P.d 0 st0 G1 Uint
    ((model.chain.G 0).batchEnc Uint) sF0 tok.coreTok levelUS0 D0 i₀ sE sL cL chE curGE curUE
    curEditsE curEncE oldOrdE tokE bE bWE eE eWE levelU levelUS D
  -- the edge cap of the prefix is the edge cap of the level graphs
  ec0_eq : ec0 = eCap
  -- the loop does not change the batch of level `0`
  levelU0 : levelU 0 = Uint
  -- the Branch B case of the dispatch: a run of Branch B from `st` is a run of the core
  dispatchRuns : ∀ (o : Outcome) (out : State) (c : ℕ),
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
      (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos) o out (c0 + c)

/-- **The exit of the loop of Branch B.** From the four exit goals and a run up to the
exit of the loop, the exit ends in a state `sX` with the facts of the head: `BranchBExitOutKFBL`,
`BranchBExitCaseKFBL`, the model after the update, the places of the forests and the order of
the rebuilt blocks. Proof route: the case split of `BranchBExitCaseKFBL` on `i₀` and `curUE`
(the loop facts give `i₀ ≤ d` and the test), `BranchBExitOutKFBL.of_int_lay` with
`BranchBIntExitLayGoalKFBL` and `BranchBIntExitForestLocGoalKFBL` (interior),
`BranchBExitOutKFBL.of_base_lay` with `BranchBTermExitLayGoalKFBL` and
`BranchBTermExitForestLocGoalKFBL` (terminal with a batch), `wireBranchBTermEmpty_exitOut` and
`BranchBExitForestLocKFBL.of_nil` (empty batch); the model from `branchBUpdateLoop_int`,
`branchBUpdateLoop_term` and the `updateLoop` equation of the loop facts; the order from
`wireBranchBIntKFBL_exit_rebuiltOrd` (empty at the terminal exits, `fr + 1 > d`). -/
@[expose] def BranchBHeadExitGoalKFBL : Prop :=
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
    BranchBIntExitLayGoalKFBL → BranchBTermExitLayGoalKFBL →
    BranchBIntExitForestLocGoalKFBL → BranchBTermExitForestLocGoalKFBL →
    ∀ (H : BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
        lastMul
        intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
        bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
        dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
        edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
        collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
        coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
        allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
        editsPtr editWords g l heap pos ω mem0 mem model tok U B R),
    ∃ (sX : State) (cX fr vcL ecL termTokN hT : ℕ) (tokN : ℕ → Rcore.τ)
      (X : ChainState cfg.T cfg.P),
      (BranchBExitOutKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
        (capExp := capExp) H.A vcL ecL (heap + 1 + 12 * cfg.P.d)
        (heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1)) tok.intCap fr H.st0 H.chE X H.levelU H.D H.sE sX
            H.tokE tokN
        termTokN hT) ∧
      (BranchBExitCaseKFBL w L P vCap eCap capExp capLimit lastMul lastSpace dgApply
        initCore coreLenProc lastInit cfg Psc Rcore p opCore ω levelSpace levelCost tok H.A H.ℓ'
            H.g' H.i₀ H.sE
        H.sL H.chE H.curGE H.curUE H.curEncE H.bWE H.tokE sX cX fr vcL ecL termTokN hT tokN X) ∧
      (X = (alg2PreResetState cfg model U H.gVec H.lVec).chain) ∧
      (BranchBExitForestLocKFBL
        (RL := LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
          (model.chain.G cfg.P.d).E) H.A (heap + 1 + 12 * cfg.P.d)
        (heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1)) fr
        (if fr ≤ cfg.P.d then chainSuffixForests H.st0 fr else [])
        (if fr ≤ cfg.P.d then chainSuffixForests X fr else []) H.tokE tok.termTok sX) ∧
      (BranchBRebuiltOrdKFBL (solverLevelMetaAddr tok.table cfg.P.d) cfg.P.d (fr + 1)
        heap vCap eCap L sX.mem)

/-- **The run of Branch B up to the exit of the loop.** From the premises of
`BranchBRunGoalKFBL`, every start state has a run up to the exit of the loop. -/
@[expose] def BranchBRunPreExitGoalKFBL : Prop :=
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
    Nonempty (BranchBRunPreExitKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap
        lastMul
        intCapMax forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree
        bind canonCopy isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy
        dgApply updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc
        edgeProc signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc
        collectProc collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace
        coreFixed toolMul fmt cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace
        allocation lastAlloc Ginit reembFn Rcore p opTree opCore opLast stepCap root uIntBuf
        editsPtr editWords g l heap pos ω mem0 mem model tok U B R)

/-- **The head goal of Branch B from its two parts.** -/
theorem branchBRunHeadGoal_of_preExit_exit (hPre : BranchBRunPreExitGoalKFBL)
    (hExit : BranchBHeadExitGoalKFBL) : BranchBRunHeadGoalKFBL := by
  intro w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
    forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy
    isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
    updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
    signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
    collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace coreFixed toolMul fmt
    cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Ginit
    reembFn Rcore p opTree opCore opLast stepCap root uIntBuf editsPtr editWords g l heap pos ω
    mem0 mem model tok U B R EA EB hInt hTerm hIntF hTermF hTS hShr hHF hTP S
  obtain ⟨H⟩ := hPre EA EB hInt hTerm hIntF hTermF hTS hShr hHF hTP S
  obtain ⟨sX, cX, fr, vcL, ecL, termTokN, hT, tokN, X, hOut, hCase, hModel, hLoc, hOrd⟩ :=
    hExit hInt hTerm hIntF hTermF H
  exact ⟨{ H with
    sX := sX, cX := cX, fr := fr, vcL := vcL, ecL := ecL, termTokN := termTokN, hT := hT,
    tokN := tokN, X := X, exitOut := hOut, exitCase := hCase, modelEq := hModel,
    forestLoc := hLoc, rebuiltOrdX := hOrd }⟩

end MinCostFlow.MinRatio
