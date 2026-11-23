module

public import MinCostFlow.MinRatio.WireChainCoreBranchBCostGoalKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBCostProof

/-!
# The cost goal of Branch B (`WireChainCoreBranchBCostProved`)

`BranchBCostGoalKFBL` from `branchBCostFieldsKFBL_of_hyps`
(`WireChainCoreBranchBCostProof.lean`) and the field `ec0_eq` of the run.
-/

public section

namespace MinCostFlow.MinRatio

/-- **The cost goal of Branch B.** -/
theorem branchBCostGoalKFBL_proved : BranchBCostGoalKFBL :=
  fun H hTreeMul hMono hγk => branchBCostFieldsKFBL_of_hyps H hTreeMul hMono hγk H.ec0_eq

end MinCostFlow.MinRatio

end
