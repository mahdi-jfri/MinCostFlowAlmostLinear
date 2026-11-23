module

public import MinCostFlow.MinRatio.WireChainCoreBranchBTopKFBL
public import MinCostFlow.MinRatio.WireChainCoreMetaDisjBranchB

/-!
# The meta-disjointness clause at the end of every run of Branch B
(`WireChainCoreBranchBMetaDisjEndKFBL`)

The post of the chain core has a clause that the level graph and length blocks are pairwise
disjoint (`SolverLevelMetaDisjAt`). `branchB_metaDisj_end` proves its Branch B case
`OrdChainCoreBranchBMetaDisjKFBL`: for every start state that meets the premises and the clause at
`mem0`, every run of the core that returns ends in a state with the clause. The proof takes the run
of Branch B with its parts (`BranchBRunGoalKFBL`). The program is deterministic (`Runs.det`), so the
given run ends in the same state. There the meta words of the levels below `fr + 1` keep their
values (`metaKeep` of `BranchBSpaceGoalKFBL`) and the rebuilt blocks are in order (the field
`rebuiltOrd` of the run), so `branchB_metaDisj` gives the clause.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- **The meta-disjointness clause at the end of Branch B** (`OrdChainCoreBranchBMetaDisjKFBL`
for the chain core with Branch A and Branch B), from the run goal, the two forest place goals and
the space
goal of Branch B, with the premises of `BranchBTopGoalKFBL`. -/
theorem branchB_metaDisj_end (hRun : BranchBRunGoalKFBL)
    (hIntF : BranchBIntExitForestLocGoalKFBL) (hTermF : BranchBTermExitForestLocGoalKFBL)
    (hSpace : BranchBSpaceGoalKFBL)
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
    (EA : BranchAEnvKFBL w L P m capExp capLimit fcap lastMul intCapMax forestEdgeCap drainUnit
      edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy isNeg
      refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply updateLen0Proc
      initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc signExt mul
      intDiv lastInit rebuildOffReadyProc coreSpace coreFixed toolMul fmt cfg G Psc levelSpace
      levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Rcore p opTree opCore
      opLast stepCap)
    (EB : BranchBEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc
      collectProc edgeProc signExt mul intDiv copy collectDel emitCuts zeroIns filterEdits
      pushInsProc pushProc isNeg fmt cfg Psc allocation Ginit reembFn Rcore p opCore)
    (hInt : BranchBIntExitLayGoalKFBL)
    (hTerm : BranchBTermExitLayGoalKFBL)
    (hTS : (∀ ch, ShiftLoopChainInv cfg ch → BranchBToolStepKFBL cfg stepCap ch))
    (hShr : BranchBForestShrinkKFBL cfg)
    (hHF : (∀ b s x mem, Rcore.rep b s x mem → Rcore.foot b x b))
    (hTP : cfg.TP.Valid) :
    OrdChainCoreBranchBMetaDisjKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit
      wordExp stretchPrec intCapMax forestEdgeCap vCap eCap cfg G Rcore p coreSpace
      (ordChainUpdateCoreBodyKFBL
        (wireBranchAKFBL packEditsProc (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg
          refreshAccountsProc dgApply updateLen0Proc (opCore 2) renameProc compactProc
          sortedEndsProc initCore (opCore 3) coreLenProc (opCore 5) lastInit rebuildOffReadyProc)
        (wireBranchBKFBL collectDel emitCuts packEditsProc filterEdits zeroIns
          refreshAccountsProc updateLen0Proc copyProc updLen slotProc pushInsProc bind canonCopy
          isNeg dgApply initCore coreLenProc lastInit opTree opCore)) := by
  intro root uIntBuf editsPtr editWords g l heap pos ω mem0 mem model tok U B R tr gVec lVec
    modelPre h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34
    nextHeap cost out tok' hRuns htab
  have S : BranchBStartKFBL w L P m V psi k epsExp drainUnit capExp limbMul capLimit wordExp
      stretchPrec intCapMax forestEdgeCap vCap eCap cfg G Rcore coreSpace root uIntBuf editsPtr
      editWords g l heap mem0 mem model tok U B R :=
    ⟨h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
      h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34⟩
  obtain ⟨H⟩ := hRun (pos := pos) (ω := ω) EA EB hInt hTerm hIntF hTermF hTS hShr hHF hTP S
  obtain ⟨_, hOut, _⟩ := Runs.det hRuns H.runs
  subst hOut
  have Sp := hSpace (treeMul := 0) H
  have hUH : uIntBuf ≤ heap := by have := h31; have := h26; omega
  have hSt := (branchBStatic_of_rep (heapFloor := H.heap2) h1 h2 h3 h13 h28 hUH).1
  exact branchB_metaDisj hSt h4 htab
    (fun j hj hjd => ⟨(Sp.metaKeep j (lt_min hj hjd)).2, (Sp.metaKeep j (lt_min hj hjd)).1⟩)
    H.rebuiltOrd

end MinCostFlow.MinRatio
