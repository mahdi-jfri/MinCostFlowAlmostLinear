module

public import MinCostFlow.Final.Theorem11Parts
public import MinCostFlow.Final.AssemblyDryRunSCInnerEnv
public import MinCostFlow.Final.AssemblyDryRunSCInnerAsymp
public import MinCostFlow.MinRatio.WireChainCoreBranchBTopGoalKFBL
import MinCostFlow.Final.AssemblyDryRunSCInnerExtEnv
import MinCostFlow.Final.AssemblyDryRunSCToolStep
import MinCostFlow.Final.AssemblyDryRunSCHandle
import MinCostFlow.Final.AssemblyDryRunSCDeepGrid
import MinCostFlow.MinRatio.WireChainCoreBranchBExitLayInt
import MinCostFlow.MinRatio.WireChainCoreBranchBExitLayTerm
import Mathlib.Tactic

/-!
# The Ext spec of the inner chain core at the dry values (`AssemblyDryRunSCInnerExt`)

The first part of `DryCoreOpenParts` (`Final/Theorem11Parts.lean`) is the Ext spec of the inner
chain-core block: `OrdChainUpdateCoreSpecWExtKFBL` at every budget. The lemma
`dryInnerCore_extSpec_of_branchB` (`AssemblyDryRunSCInnerEnv.lean`) gives it from the post of
Branch B. The top theorem of Branch B is the goal `BranchBTopGoalKFBL`
(`MinRatio/WireChainCoreBranchBTopGoalKFBL.lean`). It gives the post from its premises, and here
each premise is a fact at the dry values:
* `BranchAEnvKFBL`: `dryInnerCore_branchAEnvKFBL`;
* `BranchBEnvKFBL`: `dryInnerCore_branchBEnvKFBL`, at empty start graphs `Ginit`;
* the two exit goals: `branchBIntExitLayGoalKFBL_proved`, `branchBTermExitLayGoalKFBL_proved`;
* the tool step fact: `dryTool_branchBToolStepKFBL`;
* the shrink fact: `branchBForestShrink_of_progTool`, since the tool of the dry run is the tool
  of the program and its LSF init is valid;
* the handle fact: `drySCRep_handle_mem_foot`;
* `cfg.TP.Valid` and `γ_ℓ (M₀²) ≤ k`: from `concreteCirculationCfgWithLast_validOrdNoHidden`;
* `updateCoreTreeMulBound L drainUnit ≤ treeMul`: equality, since the dry `treeMul` is this bound;
* `ToolCostMono cfg.T`: `drySC_toolCostMono`.

The Branch B statement of the goal, at the procedure indices of `dryInnerCoreProcsOf`, is
`dryInnerCoreBranchB` by `rfl`. So the post that the goal gives is the premise of
`dryInnerCore_extSpec_of_branchB` at `mkBranchB := dryInnerCoreBranchB`.

* `dryInnerCore_extParts_of_topGoal`: from `BranchBTopGoalKFBL` alone, the first part of
  `DryCoreOpenParts Psc dryInnerCoreCode (dryInnerCoreSizes Psc) (dryInnerCoreSizeBounds Psc)`,
  for every `Psc`.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM IPM.Machine SparseCore
  SparseCore.Program Scaling Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-- The empty graph, used as the start graph of the cores in `BranchBEnvKFBL`. -/
private def extEmptyGraph : MGraph := ⟨∅, ∅, fun _ => 0, fun _ => 0⟩

/-- **The Ext spec of the inner chain core at the dry values.** For every `Psc`, from the named
goal `BranchBTopGoalKFBL`, the first conjunct of the body of `DryCoreOpenParts Psc
dryInnerCoreCode (dryInnerCoreSizes Psc) (dryInnerCoreSizeBounds Psc)`: for every input of the
dry run and every budget, `OrdChainUpdateCoreSpecWExtKFBL` at the entry of the inner block. -/
theorem dryInnerCore_extParts_of_topGoal (Psc : DrySparseCorePieces)
    (hTop : BranchBTopGoalKFBL) :
    let innerCoreCode := dryInnerCoreCode
    let innerSz := dryInnerCoreSizes Psc
    let hInnerSz := dryInnerCoreSizeBounds Psc
    let coreSz := dryCoreSelectSizes Psc innerSz
    let hCoreSz := dryCoreSelectSizeBounds Psc hInnerSz
    let openSz := coreSz.toDryOpenSizes
    let hOpen := hCoreSz.toDryOpenSizeBounds
    let selSz := mkDrySelectRebuildSizes (dryInitSelectSizes Psc) (dryShiftSelectSizes Psc)
    let hSel := mkDrySelectRebuildSizeBounds (dryInitSelectSizeBounds Psc)
      (dryShiftSelectSizeBounds Psc)
    let inner := dryInnerCodeSel (dryInitCode (dryParamCode Psc))
      (dryCoreSelectCode innerCoreCode) drySelectRouteCode dryTermSelectCode dryDeepSelectCode
    ForAllDryInputs dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
      (dryAllocDegConcrete Psc openSz hOpen selSz hSel) fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      let limbMul := concreteReadout2LimbMul dryWitnessUsed
      let PscP := drySCParams Psc dryCapExp limbMul
      let Rcore := drySCRep Psc (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source J hw
      let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner drySelInitCode
      let lay := dryTailLay Psc.sc inner
      let w := dryWordSize dryWitnessUsed (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
        (dryAllocDegConcrete Psc openSz hOpen selSz hSel) source
      ∀ Bb Rb : ℤ,
        OrdChainUpdateCoreSpecWExtKFBL w F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k
          (k + Num.IPM.alphaExponent I.m V + 10) (detectOffTreeDrainUnit F.limbs) dryCapExp
          limbMul (dryCapLimit dryWitnessUsed J) PscP.wordExp (dryLastStretchP J)
          (dryDeepIntCapMax J) (dryDeepForestEdgeCap J) G.n (initTargetCap cfg G)
          cfg G (dryReembFn J) Rcore p (lay.ordChainCore + 1 + innerCoreCode.off)
          (innerSz.coreSpace source J) (innerSz.coreFixed source J)
          (innerSz.coreToolMul source J) (innerSz.coreTreeMul source J) Bb Rb := by
  intro innerCoreCode innerSz hInnerSz coreSz hCoreSz openSz hOpen selSz hSel inner
    source J hJn hJm _ hCap hw I V k F cfg G limbMul PscP Rcore p lay w Bb Rb
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  have hWordCoeff : Classical.choose (concrete_solver_word_bounds_poly dryWitnessUsed) ≤
      dryAllocCoeffConcrete Psc openSz hOpen selSz hSel :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hE := dryInnerCore_branchAEnvKFBL Psc (dryInitCode (dryParamCode Psc))
    drySelectRouteCode dryTermSelectCode dryDeepSelectCode drySelInitCode dryInnerCoreBranchB
    dryInnerCoreBranchB_noRand (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel) hWordCoeff source J hJn hJm hCap1 hw
  have hBEnv := dryInnerCore_branchBEnvKFBL Psc (dryInitCode (dryParamCode Psc))
    drySelectRouteCode dryTermSelectCode dryDeepSelectCode drySelInitCode dryInnerCoreBranchB
    dryInnerCoreBranchB_noRand (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel) hWordCoeff source J hJn hJm hCap1 hw
    (fun _ => extEmptyGraph) (fun _ => by simp [extEmptyGraph, MGraph.n, MGraph.m])
    (fun _ => by simp [extEmptyGraph, MGraph.m])
  have hT : cfg.T = sparseCoreProgTool (dryLSFInitUsed F.limbs F.fmt.precision) dryCLsstUsed
      (Expander.chosenL (cfg.P.M₀ ^ 2)) sparsifyImplUsed :=
    concreteCirculationCfgWithLast_T_eq_progTool dryWitnessUsed sparsifyImplUsed rfl rfl rfl J hw
  have hShrink : BranchBForestShrinkKFBL cfg :=
    branchBForestShrink_of_progTool hT
      (fun j hj => dryLSFInitUsed_isValidLSFInitFor F.limbs F.fmt.precision cfg.P.k j hj)
  have hTP : cfg.TP.Valid :=
    (concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap1).hTP
  have hB := hTop hE hBEnv branchBIntExitLayGoalKFBL_proved branchBTermExitLayGoalKFBL_proved
    (fun ch hInv => dryTool_branchBToolStepKFBL J hJn hJm hCap1 hInv) hShrink
    (drySCRep_handle_mem_foot Psc _ _ source J hw) hTP le_rfl (drySC_toolCostMono J)
    (concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap1).hγk
    (V := V) (psi := ⌈cfg.Ψ⌉₊) (k := k) (epsExp := k + Num.IPM.alphaExponent I.m V + 10)
    (limbMul := limbMul) (treeMul := innerSz.coreTreeMul source J) (B_bound := Bb) (R_bound := Rb)
  exact dryInnerCore_extSpec_of_branchB Psc (dryInitCode (dryParamCode Psc)) drySelectRouteCode
    dryTermSelectCode dryDeepSelectCode drySelInitCode dryInnerCoreBranchB
    dryInnerCoreBranchB_noRand (dryAllocCoeffConcrete Psc openSz hOpen selSz hSel)
    (dryAllocDegConcrete Psc openSz hOpen selSz hSel) hWordCoeff source J hJn hJm hCap1 hw Bb Rb
    hB

end MinCostFlow.Final.DryRun

end
