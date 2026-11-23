module

public import MinCostFlow.MinRatio.WireChainCoreBranchBPartsKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBMetaDisjKFBL

/-!
# One run of Branch B with the facts after each part (`WireChainCoreBranchBRunKFBL`)

`BranchBRunKFBL` holds a run of the chain core that takes Branch B, from a start state that meets
`BranchBStartKFBL`, split into its parts: Phase 0 and the test (the dispatch), the prefix, the
front, the loop of plain steps, the exit, and the suffix. For each part it holds the witnesses of
its run lemma and the facts at them (the definitions of `WireChainCoreBranchBPartsKFBL`), and the
data that the later parts read: the start chain `st0` of the loop, the addresses `A`, the trace
caps `C`, the forest lists of the suffix and the split of the chain tree before Sync 2a.

The structure is the common premise of the three goals of the fields of `BranchBSufOutKFBL`
(`BranchBCostGoalKFBL`, `BranchBSpaceGoalKFBL`, `BranchBModelGoalKFBL`). The top theorem of
Branch B builds it from the run lemmas, and the fields of `BranchBSufOutKFBL` are read at:
`heap2`, `hS := sE.regs 4`, `hT`, `hX := sX.regs 4`, `fr`, `levelU`, `levelUS`, `D`, `tokN`,
`vcL`, `ecL`, `termTokN`, `curTree`, `curTreeTok`, `offCnt`, `canonVal`, `out`, `nextHeap` and
`cost`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- A run of the chain core through Branch B from the start state at `root`, `uIntBuf`,
`editsPtr`, `editWords`, `g`, `l`, `heap`, `pos`, with the facts after each of its parts. The
parameters are those of `BranchBTopGoalKFBL` and the start state. -/
structure BranchBRunKFBL (w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul
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
  -- the exit (the two exit goals, `wireBranchBTermEmpty_exitOut`)
  sX : State
  cX : ℕ
  fr : ℕ
  vcL : ℕ
  ecL : ℕ
  termTokN : ℕ
  hT : ℕ
  tokN : ℕ → Rcore.τ
  X : ChainState cfg.T cfg.P
  exitOut : BranchBExitOutKFBL (w := w) (L := L) (P := P) (vCap := vCap) (eCap := eCap)
    (capExp := capExp) A vcL ecL (heap + 1 + 12 * cfg.P.d)
    (heap + 1 + 12 * cfg.P.d + (cfg.P.d + 1)) tok.intCap fr st0 chE X levelU D sE sX tokE tokN
    termTokN hT
  exitCase : BranchBExitCaseKFBL w L P vCap eCap capExp capLimit lastMul lastSpace dgApply
    initCore coreLenProc lastInit cfg Psc Rcore p opCore ω levelSpace levelCost tok A ℓ' g' i₀ sE
    sL chE curGE curUE curEncE bWE tokE sX cX fr vcL ecL termTokN hT tokN X
  modelEq : X = (alg2PreResetState cfg model U gVec lVec).chain
  -- the split of the chain tree before Sync 2a (`branchBSplit`)
  Fp : Finset ℕ
  Fp_eq : Fp = (Finset.range fr).biUnion fun j => (X.toTreeChain.activeLSF j).F.F.E
  oldFs : List MGraph
  oldFs_eq : oldFs = if fr ≤ cfg.P.d then chainSuffixForests st0 fr else []
  newFs : List MGraph
  newFs_eq : newFs = if fr ≤ cfg.P.d then chainSuffixForests X fr else []
  split :
    (∀ Y : Finset ℕ, (∀ e, e ∈ Y ↔ (∃ j < min fr cfg.P.d, e ∈ (D j).fDel) ∧ e ∈ G1.E) →
      F1 \ Y = Fp ∪ (graphListEdgeUnion oldFs ∩ G1.E)) ∧
    (∀ j < min fr cfg.P.d, ∀ e ∈ (D j).fDel, e ∈ G1.E → e ∈ F1) ∧
    (∀ e ∈ Fp, e ∉ graphListEdgeUnion oldFs) ∧ (∀ e ∈ Fp, e ∉ graphListEdgeUnion newFs) ∧
    Fp ∪ graphListEdgeUnion newFs = X.toTreeChain.chainTree.E ∧
    ((List.range (min fr cfg.P.d)).flatMap fun j => (D j).fDel).Nodup
  -- the tree state on the new root graph (`branchBTreePhase_newRoot`)
  phaseX : TreeSyncPhaseAt L tok root uIntBuf (sX.regs 4) tok.rootGraph G1 F1 canonVal B R
    (G1.E \ (model.chain.G 0).E) curTree1 curTreeTok1 offCnt1 sX.mem
  -- the suffix (`wireBranchBSuffixKFBL_runs`)
  out : State
  cS : ℕ
  nextHeap : ℕ
  curTree : PathTreeState
  curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ
  offCnt : ℕ
  suf : BranchBSuffixFactsKFBL (w := w) L drainUnit emitCuts packEditsProc filterEdits bind
    canonCopy isNeg pushInsProc root uIntBuf (sX.regs 4) tok.rootGraph offCnt1 i₀ cfg.P.d fr p
    opTree ω sX tok B
    R G1 F1 Fp (G1.E \ (model.chain.G 0).E) canonVal curTreeTok1 (fun j => (D j).fDel) oldFs
    newFs Uint out cS nextHeap curTree curTreeTok offCnt
  -- the whole run
  cost : ℕ
  runs : Runs w p ω (ordChainUpdateCoreBodyKFBL
      (wireBranchAKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg
        refreshAccountsProc dgApply updateLen0Proc (opCore 2) renameProc compactProc
        sortedEndsProc initCore (opCore 3) coreLenProc (opCore 5) lastInit rebuildOffReadyProc)
      (wireBranchBKFBL collectDel emitCuts packEditsProc filterEdits zeroIns
        refreshAccountsProc updateLen0Proc copyProc updLen slotProc pushInsProc bind canonCopy
        isNeg dgApply initCore coreLenProc lastInit opTree opCore))
    (startState [root, uIntBuf, editsPtr, editWords, g, l, heap] mem pos)
    (.returned nextHeap) out cost
  costLe : cost ≤ c0 + cP + cF + cL + cX + cS + 12
  -- the order of the rebuilt level blocks at the end (`wireBranchBIntKFBL_exit_rebuiltOrd` at the
  -- interior exit and the frame of the suffix; empty at the terminal exits)
  rebuiltOrd : BranchBRebuiltOrdKFBL (solverLevelMetaAddr tok.table cfg.P.d) cfg.P.d (fr + 1) heap
    vCap eCap L out.mem
  -- the edge cap of the prefix is the edge cap of the level graphs (`wireBranchBPrefixKFBL_runs`
  -- at `ec0 := eCap`)
  ec0_eq : ec0 = eCap
  -- the loop does not change the batch of level `0` (a plain pass changes only level `idx + 1`)
  levelU0 : levelU 0 = Uint
  -- the records of the edges of the tree after Sync 1 that the suffix cuts lie in the heap of the
  -- suffix (the first conjunct of `wireBranchBSuffixKFBL_runs`)
  sufRecCut : ∀ ei ∈ G1.E, ei ∈ F1 → ei ∉ Fp ∪ graphListEdgeUnion newFs →
    sX.regs 4 ≤ out.mem (tok.edgeRecords + ei) ∧
      out.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ nextHeap

end MinCostFlow.MinRatio
