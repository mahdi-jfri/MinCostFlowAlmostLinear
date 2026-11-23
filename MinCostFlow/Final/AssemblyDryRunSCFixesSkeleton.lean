module

public import MinCostFlow.Final.AssemblyDryRunSCBounds
public import MinCostFlow.MinRatio.SolverSelectState
public import MinCostFlow.MinRatio.WireSelectSpec
public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
import Mathlib.Tactic

/-!
# `SolverInnerCode` with the Init and Term code as parameters, and concrete-`B` assembly helpers

Provides the shared definitions and proved helper theorems used by the unified Theorem 1.1
assembly theorem `theorem_1_1_skeleton_kfbl_sel` (`Final/AssemblyDryRunSCDeepCode.lean`):
* `dryInnerSizesWithSelect_capSimpleBounds`, `dryAllocCoeffConcrete`, `dryAllocDegConcrete`;
* `dryInnerCodeSel` (concrete deterministic `evalCycleBody` at offset `0`, and the parameters `initCode`,
  `coreCode`, `selectCode`, `termCode`, `deepCode`), `dryInnerCodeSel_isDeterministic`,
  `dryInnerCodeSel_hasEval`, and `dryInnerCodeSel_hEval_proved` (`OrdCycleRouteEvalSpecW` at
  `drySCRep`);
* `dry_solverSelectHeapAddr_eq`: verifies `solverSelectHeapAddr table d = table + 4 * d + 2`,
  matching `(dMul, kOff) = (4, 2)` in `OrdCycleRouteSelectSpecHeap` and `solverStateRepSel`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-- `dryInnerSizesWithSelect` satisfies `DryCapSimpleBounds` from the single route-length bound
`openSz.maxEdges + openSz.maxPaths < 2 ^ (3 * F.rangeExponent + 20)`. -/
theorem dryInnerSizesWithSelect_capSimpleBounds (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (selSz : DrySelectRebuildSizes) (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (hMaxEP : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB)
      fun source J hw =>
        let I := solverConnectedAugmented J
        let V := solverPenalty J.m
        let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) I.m
        let F := ipmQualityMinRatioFormat I.m V k hw
        openSz.maxEdges source J + openSz.maxPaths source J < 2 ^ (3 * F.rangeExponent + 20)) :
    DryCapSimpleBounds B hB (dryInnerSizesWithSelect Psc openSz selSz) := by
  refine ⟨fun source J hJn hJm hCost hCap hw => ?_⟩
  have hE100 : 100 ≤ ipmQualityRangeExponent (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) := by
    unfold ipmQualityRangeExponent; omega
  have hpow : (2 : ℤ) ^ (ipmQualityPrecision (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) +
      2 * ipmQualityRangeExponent (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) + 1) ≤
    (2 : ℤ) ^ (ipmQualityPrecision (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) +
      80 * ipmQualityRangeExponent (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m)) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  exact ⟨le_refl _, hpow, hpow, le_refl _, le_refl _, hMaxEP source J hJn hJm hCost hCap hw⟩

/-- Allocation coefficient for `dryInnerBounds Psc openSz hOpen selSz hSel`. -/
def dryAllocCoeffConcrete (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (hOpen : DryOpenSizeBounds openSz) (selSz : DrySelectRebuildSizes)
    (hSel : DrySelectRebuildSizeBounds selSz) : ℕ :=
  dryAllocCoeffFull (dryInnerBounds Psc openSz hOpen selSz hSel)
    (dryInnerBounds_hyp Psc openSz hOpen selSz hSel)

/-- Allocation degree for `dryInnerBounds Psc openSz hOpen selSz hSel`. -/
def dryAllocDegConcrete (Psc : DrySparseCorePieces) (openSz : DryOpenSizes)
    (hOpen : DryOpenSizeBounds openSz) (selSz : DrySelectRebuildSizes)
    (hSel : DrySelectRebuildSizeBounds selSz) : ℕ :=
  dryAllocDeg (dryInnerBounds Psc openSz hOpen selSz hSel)
    (dryInnerBounds_hyp Psc openSz hOpen selSz hSel)

/-! ## Open-Init / Open-Term `SolverInnerCode` with concrete `evalCycle` -/

/-- Relocatable `SolverInnerCode` for the select-heap solver: installs the concrete deterministic
`evalCycleBody` at offset `0` and leaves all five select-region-aware procedures (`initConcrete`,
`ordChainCore`, `selectRoute`, `shiftTermChain`, `shiftDeepChain`) as parameter
`SolverInnerSubCode` blocks. -/
def dryInnerCodeSel (initCode coreCode selectCode termCode deepCode : SolverInnerSubCode) :
    SolverInnerCode where
  procs env :=
    let b := env.innerBase
    let ops := env.opsBase
    [evalCycleBody (dryPathTreeOp ops 3) (ops + 2) (ops + 6)] ++
      (initCode.procs { env with innerBase := b + 1 } ++
      (coreCode.procs { env with innerBase := b + 1 + initCode.len } ++
      (selectCode.procs { env with innerBase := b + 1 + initCode.len + coreCode.len } ++
      (termCode.procs { env with innerBase := b + 1 + initCode.len + coreCode.len + selectCode.len } ++
       deepCode.procs { env with
         innerBase := b + 1 + initCode.len + coreCode.len + selectCode.len + termCode.len }))))
  evalCycleOff := 0
  initConcreteOff := 1 + initCode.off
  ordChainCoreOff := 1 + initCode.len + coreCode.off
  selectRouteOff := 1 + initCode.len + coreCode.len + selectCode.off
  shiftTermChainOff := 1 + initCode.len + coreCode.len + selectCode.len + termCode.off
  shiftDeepChainOff := 1 + initCode.len + coreCode.len + selectCode.len + termCode.len + deepCode.off

/-- Determinism of `dryInnerCodeSel` from determinism of its five parameter blocks. -/
theorem dryInnerCodeSel_isDeterministic
    (initCode coreCode selectCode termCode deepCode : SolverInnerSubCode) :
    (dryInnerCodeSel initCode coreCode selectCode termCode deepCode).IsDeterministic := by
  intro env s hs
  unfold dryInnerCodeSel at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | h1 | h2 | h3 | h4 | h5
  · exact evalCycleBody_noRand _ _ _
  · exact initCode.hnoRand _ s h1
  · exact coreCode.hnoRand _ s h2
  · exact selectCode.hnoRand _ s h3
  · exact termCode.hnoRand _ s h4
  · exact deepCode.hnoRand _ s h5

/-- Placement of `evalCycleBody` inside `dryLinkedProgram` with `dryInnerCodeSel`. -/
theorem dryInnerCodeSel_hasEval (Psc : DrySparseCorePieces)
    (initCode coreCode selectCode termCode deepCode : SolverInnerSubCode) :
    let inner := dryInnerCodeSel initCode coreCode selectCode termCode deepCode
    let p := dryLinkedProgram dryWitnessUsed Psc.sc inner
    let lay := dryTailLay Psc.sc inner
    let ops := mrdsCycleBase
    p.procs[lay.evalCycle]? =
      some (evalCycleBody (dryPathTreeOp ops 3) (ops + 2) (ops + 6)) := by
  intro inner p lay ops
  have hInner := dryInner_hasAt (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed)
    (mrdsSolverDispatch solverCycleInit (solverOpsDispatch mrdsCycleBase)
      (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length)
    Psc.sc inner
    (dynLctForestBodies 4 (mrdsCycleBase +
      (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length))
  have hEvalIdx : lay.evalCycle = lay.innerBase := by
    change lay.innerBase + 0 = lay.innerBase
    omega
  rw [hEvalIdx]
  exact hInner.head

/-- Automatic proof of `OrdCycleRouteEvalSpecW` at `drySCRep` and `dryInnerSizesWithSelect`
inside `dryLinkedProgram` with `dryInnerCodeSel`. -/
theorem dryInnerCodeSel_hEval_proved (Psc : DrySparseCorePieces)
    (initCode coreCode selectCode termCode deepCode : SolverInnerSubCode)
    (openSz : DryOpenSizes) (hOpen : DryOpenSizeBounds openSz)
    (selSz : DrySelectRebuildSizes) (hSel : DrySelectRebuildSizeBounds selSz) :
    let inner := dryInnerCodeSel initCode coreCode selectCode termCode deepCode
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
      let s := dryInnerSizesWithSelect Psc openSz selSz source J
      OrdCycleRouteEvalSpecW
        (dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
          (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
        F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k (k + Num.IPM.alphaExponent I.m V + 10)
        (detectOffTreeDrainUnit F.limbs) cfg Rcore
        (dryLinkedProgram dryWitnessUsed Psc.sc inner)
        (dryTailLay Psc.sc inner).evalCycle
        s.evalSpace s.evalBudget s.maxEdges s.maxPaths := by
  intro inner source J hJn hJm hCost hCap hw
  dsimp only
  let I := solverConnectedAugmented J
  let V := solverPenalty J.m
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let F := ipmQualityMinRatioFormat I.m V k hw
  have hw14 : 14 ≤ dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source :=
    (ipm_quality_parameter_words_fit I.m V k hw).1
  have hOps := solverOpsProcs_evalTermHelpers (L := F.limbs) (fmt := F.fmt) hw14 rfl
    (solverOps_hasAt (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed)
      (mrdsSolverDispatch solverCycleInit (solverOpsDispatch mrdsCycleBase)
        (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length)
      Psc.sc inner
      (dynLctForestBodies 4 (mrdsCycleBase +
        (dryCycle (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner).length)))
  have hEvalAt := dryInnerCodeSel_hasEval Psc initCode coreCode selectCode termCode deepCode
  exact evalCycleBody_meets_spec
    (w := dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source)
    (L := F.limbs) (P := F.fmt.precision) (m := I.m) (V := V)
    (psi := ⌈(concreteCirculationCfgWithLast dryWitnessUsed J).Ψ⌉₊) (k := k)
    (epsExp := k + Num.IPM.alphaExponent I.m V + 10) (drainUnit := detectOffTreeDrainUnit F.limbs)
    (initTree := mrdsCycleBase + 81) (opTree := dryPathTreeOp mrdsCycleBase)
    (numAdd := mrdsCycleBase + 2) (numSub := mrdsCycleBase + 6)
    (maxEdges := (dryInnerSizesWithSelect Psc openSz selSz source J).maxEdges)
    (maxPaths := (dryInnerSizesWithSelect Psc openSz selSz source J).maxPaths)
    (fmt := F.fmt) (cfg := concreteCirculationCfgWithLast dryWitnessUsed J)
    (Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw)
    (drySCRep_local Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw)
    rfl (le_trans (by decide : 10 ≤ 14) hw14) hEvalAt hOps.2.2.2.2.2 hOps.2.1 hOps.2.2.2.1

/-- `solverSelectHeapAddr table d` equals `table + 4 * d + 2`, matching `(dMul, kOff) = (4, 2)`
in `OrdCycleRouteSelectSpecHeap` and `solverStateRepSel`. -/
theorem dry_solverSelectHeapAddr_eq (table d : ℕ) :
    solverSelectHeapAddr table d = table + 4 * d + 2 := by
  unfold solverSelectHeapAddr solverLevelMetaAddr solverLvlMAddr solverN0Addr
  omega

end MinCostFlow.Final.DryRun

end
