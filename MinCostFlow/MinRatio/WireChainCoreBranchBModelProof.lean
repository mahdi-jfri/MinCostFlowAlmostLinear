module

public import MinCostFlow.MinRatio.WireChainCoreBranchBModelGoalKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBModelProofBase
import MinCostFlow.MinRatio.WireChainCoreBranchBModelProofKeep
import MinCostFlow.MinRatio.WireChainCoreBranchBModelProofLink

/-!
# Proof of `BranchBModelGoalKFBL` (`WireChainCoreBranchBModelProof`)

Assembles `branchBModelGoalKFBL_proved : BranchBModelGoalKFBL` from the field proofs in
`WireChainCoreBranchBModelProofBase`, `WireChainCoreBranchBModelProofKeep`, and
`WireChainCoreBranchBModelProofLink`.
-/

public section

namespace MinCostFlow.MinRatio

/-- **Proof of `BranchBModelGoalKFBL`**: for every run `H : BranchBRunKFBL` of Branch B of the
chain core, all 13 model and kept-word fields of `BranchBModelFieldsKFBL` hold at the final state
`H.out`. -/
theorem branchBModelGoalKFBL_proved : BranchBModelGoalKFBL :=
  fun H =>
    { names := branchBModel_names H
      frPos := branchBModel_frPos H
      link := branchBModel_link H
      newForest := branchBModel_newForest H
      newSub := branchBModel_newSub H
      sched := branchBModel_sched H
      slotModel := branchBModel_slotModel H
      rootDir := branchBModel_rootDir H
      header := branchBModel_header H
      table := branchBModel_table H
      metaCells := branchBModel_metaCells H
      fresh := branchBModel_fresh H
      frameMem := branchBModel_frameMem H }

end MinCostFlow.MinRatio
