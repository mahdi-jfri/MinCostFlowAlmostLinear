module

public import MinCostFlow.Final.Theorem11Parts
public import MinCostFlow.Final.AssemblyDryRunSCFirstStep
public import MinCostFlow.Final.AssemblyDryRunSCFirstStepCost
public import MinCostFlow.Final.AssemblyDryRunSCInnerAsymp
public import MinCostFlow.Final.AssemblyDryRunSCInnerCode
public import MinCostFlow.Final.AssemblyDryRunSCInnerExt
public import MinCostFlow.Final.AssemblyDryRunSCCoreMetaDisj

/-!
# Theorem 1.1 from two parts of the chain core (`Theorem11Core`)

The first step of a branch of the sparse core is proved (`dryFirstStep_hFirstStep`,
`dryFirstStep_cost`), and so is its init (`drySC_hFirstInit`). `dryPscFinal` is the record of the
sparse-core pieces of the dry run with both plugged in. `theorem_1_1_of_core` is
`theorem_1_1_of_parts` at these pieces and at the inner chain-core block of the dry run
(`dryInnerCoreCode`, `dryInnerCoreSizes`, `dryInnerCoreSizeBounds`). Its only hypothesis is
`DryCoreOpenParts` there: the Ext spec of the inner block, and the disjointness clause of the
core. `theorem_1_1_of_branchB` reduces both to two facts on Branch B of the chain core.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM IPM.Machine SparseCore
  SparseCore.Program Scaling Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-- **The sparse-core pieces of the dry run**, with the first phases of the step
(`asmFsStepCode`) and of the init (`dryFirstInit`) of a branch, and the constants
`dryFirstConsts dryFsStepMul`. -/
noncomputable def dryPscFinal : DrySparseCorePieces :=
  mkDrySparseCorePieces asmFsStepCode dryFirstInit (dryFirstConsts dryFsStepMul)
    (dryFirstConsts_hC dryFsStepMul)
    (dryFirstStep_hFirstStep dryFsStepMul dryFirstStep_cost)
    (drySC_hFirstInit dryCompCode dryCFS asmFsStepCode (dryFirstConsts dryFsStepMul)
      (dryFirstConsts_initMul dryFsStepMul) (dryFirstConsts_initSpace dryFsStepMul))

/-- **Theorem 1.1 (page 2) from two parts of the chain core**: the Ext spec of the inner
chain-core block of the dry run and the disjointness clause of the core, at the sparse-core pieces
`dryPscFinal`. -/
theorem theorem_1_1_of_core
    (hParts : DryCoreOpenParts dryPscFinal dryInnerCoreCode (dryInnerCoreSizes dryPscFinal)
      (dryInnerCoreSizeBounds dryPscFinal)) :
    MinCostFlowStatement :=
  theorem_1_1_of_parts asmFsStepCode (dryFirstConsts dryFsStepMul)
    (dryFirstConsts_hC dryFsStepMul) (dryFirstConsts_initMul dryFsStepMul)
    (dryFirstConsts_initSpace dryFsStepMul)
    (dryFirstStep_hFirstStep dryFsStepMul dryFirstStep_cost)
    dryInnerCoreCode (dryInnerCoreSizes dryPscFinal) (dryInnerCoreSizeBounds dryPscFinal) hParts

/-- **Theorem 1.1 (page 2) from two facts on Branch B of the chain core**: the top goal
`BranchBTopGoalKFBL` (the post of Branch B), and the disjointness clause on the end state
of Branch B at the dry values (`DryInnerCoreBranchBMetaDisj`). The two parts of `DryCoreOpenParts`
are `dryInnerCore_extParts_of_topGoal` and `dryInnerCore_openPart2`. -/
theorem theorem_1_1_of_branchB (hTop : BranchBTopGoalKFBL)
    (hDisj : DryInnerCoreBranchBMetaDisj dryPscFinal) :
    MinCostFlowStatement :=
  theorem_1_1_of_core fun source J hJn hJm hCost hCap hw =>
    ⟨dryInnerCore_extParts_of_topGoal dryPscFinal hTop source J hJn hJm hCost hCap hw,
      dryInnerCore_openPart2 dryPscFinal hDisj source J hJn hJm hCost hCap hw⟩

end MinCostFlow.Final.DryRun
