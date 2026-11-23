module

public import MinCostFlow.MinRatio.WireChainCoreBranchBHeadExitKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBHeadPrefixKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBHeadLoopKFBL
import WordRAM.Tactic

/-!
# A run of Branch B up to the exit of its loop (`WireChainCoreBranchBHeadPreExitProofKFBL`)

Proves `BranchBRunPreExitGoalKFBL`: from the start of Branch B we build the parts of a run up to
the exit of the loop of plain steps (`BranchBRunPreExitKFBL`). The parts come from two lemmas.
* `branchBHead_prefix` gives the state `st` of the dispatch, the fact that a run of Branch B from
  `st` is a run of the core, and the prefix facts at `ec0 := eCap`.
* `branchBHead_frontLoop` gives the run of the front from the end state `sP` of the prefix, the
  facts at the exit of the loop, and the fact that the loop keeps the batch of level `0`.

The named values of the run (the batch `Uint`, the vectors, the graph `G1` and so on) are the
values that these lemmas use, so their equations hold by `rfl`. The start values `levelUS0` and
`D0` of the loop are not read later, so we take empty lists.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- **The run of Branch B up to the exit of its loop.** -/
theorem branchBRunPreExitGoalKFBL_proved : BranchBRunPreExitGoalKFBL := by
  intro w L P m V psi k epsExp drainUnit capExp limbMul capLimit fcap lastMul intCapMax
    forestEdgeCap edMul mThresh wordExp stretchPrec vCap eCap packEditsProc initTree bind canonCopy
    isNeg refreshAccountsProc shift negate refreshOneProc divide add sub copy dgApply
    updateLen0Proc initCore renameProc compactProc sortedEndsProc dgInit coreLenProc edgeProc
    signExt mul intDiv lastInit rebuildOffReadyProc depth copyProc updLen slotProc collectProc
    collectDel emitCuts zeroIns filterEdits pushInsProc pushProc coreSpace coreFixed toolMul fmt
    cfg G Psc levelSpace levelCost updStepSpace lastSpace termUpdSpace allocation lastAlloc Ginit
    reembFn Rcore p opTree opCore opLast stepCap root uIntBuf editsPtr editWords g l heap pos ω
    mem0 mem model tok U B R EA EB _ _ _ _ hTS hShr hHF hTP S
  obtain ⟨st, c0, hDisp, hRuns, sP, cP, hS1, heap2, memS1, curTree1, curTreeTok1, offCnt1,
    canonVal0, canonVal, hPre⟩ := branchBHead_prefix EA EB S
  obtain ⟨sF0, cF, rF, hcF, hs4, hsFr, hsRegs, i₀, sE, sL, cL, chE, curGE, curUE, curEditsE,
    curEncE, oldOrdE, tokE, bE, bWE, eE, eWE, levelU, levelUS, D, hAt, hU0⟩ :=
    branchBHead_frontLoop (pos := pos) EA EB S hTS hTP hDisp.1 hDisp.2.2.1 hDisp.2.2.2 hPre
      (fun _ => []) (fun _ => ⟨[], [], [], []⟩)
  exact ⟨{
    envA := EA, envB := EB, toolStep := hTS, shrink := hShr, handleFoot := hHF, tpValid := hTP,
    start := S,
    Uint := _, Uint_eq := rfl, gVec := _, gVec_eq := rfl, lVec := _, lVec_eq := rfl,
    ℓ' := _, ℓ'_eq := rfl, g' := _, g'_eq := rfl, G1 := _, G1_eq := rfl, F1 := _, F1_eq := rfl,
    st := st, c0 := c0, dispatch := hDisp,
    ec0 := eCap, forestPtr := _, sP := sP, cP := cP, hS1 := hS1, heap2 := heap2, memS1 := memS1,
    curTree1 := curTree1, curTreeTok1 := curTreeTok1, offCnt1 := offCnt1,
    canonVal0 := canonVal0, canonVal := canonVal, pre := hPre,
    sF0 := sF0, cF := cF, front := ⟨rF, hcF, hs4, hsFr, hsRegs⟩,
    st0 := _, st0_eq := rfl, A := _, A_eq := rfl, C := _, C_eq := rfl,
    levelUS0 := fun _ => [], D0 := fun _ => ⟨[], [], [], []⟩,
    i₀ := i₀, sE := sE, sL := sL, cL := cL, chE := chE, curGE := curGE, curUE := curUE,
    curEditsE := curEditsE, curEncE := curEncE, oldOrdE := oldOrdE, tokE := tokE, bE := bE,
    bWE := bWE, eE := eE, eWE := eWE, levelU := levelU, levelUS := levelUS, D := D,
    loop := hAt, ec0_eq := rfl, levelU0 := hU0, dispatchRuns := hRuns }⟩

/-- **The head goal of Branch B from its exit goal.** -/
theorem branchBRunHeadGoal_of_exit (hExit : BranchBHeadExitGoalKFBL) :
    BranchBRunHeadGoalKFBL :=
  branchBRunHeadGoal_of_preExit_exit branchBRunPreExitGoalKFBL_proved hExit

end MinCostFlow.MinRatio
