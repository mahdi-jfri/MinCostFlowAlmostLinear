module

public import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailRoomKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailRunsKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBRunTailSplitKFBL

/-!
# The tail goal of Branch B (`WireChainCoreBranchBRunTailProvedKFBL`)

`branchBRunTailGoal_of_goals` proves the tail goal `BranchBRunTailGoalKFBL` from the split goal
and the phase goal of the cut of the tail: the room and the run goals of the tail are proved
(`branchBTailRoomGoalKFBL_proved`, `branchBTailRunsGoalKFBL_proved`), and
`branchBRunTailGoal_of_parts` assembles the run. With the two goals of the cut proved
(`branchBTailSplitGoalKFBL_proved`, `branchBTailPhaseGoalKFBL_proved`), the tail goal holds
(`branchBRunTailGoalKFBL_proved`).
-/

public section

namespace MinCostFlow.MinRatio

/-- **The tail goal of Branch B from the split goal and the phase goal.** -/
theorem branchBRunTailGoal_of_goals (hS : BranchBTailSplitGoalKFBL)
    (hP : BranchBTailPhaseGoalKFBL) : BranchBRunTailGoalKFBL :=
  branchBRunTailGoal_of_parts hS hP branchBTailRoomGoalKFBL_proved
    branchBTailRunsGoalKFBL_proved

/-- **The tail goal of Branch B holds.** -/
theorem branchBRunTailGoalKFBL_proved : BranchBRunTailGoalKFBL :=
  branchBRunTailGoal_of_goals branchBTailSplitGoalKFBL_proved branchBTailPhaseGoalKFBL_proved

end MinCostFlow.MinRatio

end
