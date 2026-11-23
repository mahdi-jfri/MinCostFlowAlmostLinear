module

public import MinCostFlow.MinRatio.WireChainCoreBranchBHeadExitCasesKFBL
import MinCostFlow.MinRatio.WireChainCoreBranchBHeadExitBaseKFBL

/-!
# The exit goal of the head of Branch B from its three exits (`WireChainCoreBranchBHeadExitAllKFBL`)

The loop of plain steps of Branch B stops at a level `i₀` with `0 < i₀ ≤ d`
(`BranchBRunPreExitKFBL.exit_cases`). So the exit is interior (`i₀ < d`), terminal with a batch,
or terminal with an empty batch. Each case is one proposition of
`WireChainCoreBranchBHeadExitCasesKFBL`, and `branchBHeadExitGoal_of_cases` proves
`BranchBHeadExitGoalKFBL` from the three by this case split.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- **The exit goal of the head of Branch B from its three exits.** The exit level `i₀` of a run
up to the exit satisfies `0 < i₀ ≤ d` (`BranchBRunPreExitKFBL.exit_cases`), and each of the three
cases is one of the goals. -/
theorem branchBHeadExitGoal_of_cases (hI : BranchBHeadExitIntGoalKFBL)
    (hT : BranchBHeadExitTermGoalKFBL) (hE : BranchBHeadExitEmptyGoalKFBL) :
    BranchBHeadExitGoalKFBL :=
  fun hInt hTerm hIntF hTermF H =>
    match H.exit_cases with
    | .inl ⟨h0, h1⟩ => hI hInt hTerm hIntF hTermF H h0 h1
    | .inr (.inl ⟨h0, h1⟩) => hT hInt hTerm hIntF hTermF H h0 h1
    | .inr (.inr ⟨h0, h1⟩) => hE hInt hTerm hIntF hTermF H h0 h1

end MinCostFlow.MinRatio
