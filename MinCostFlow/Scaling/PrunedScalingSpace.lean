module

public import MinCostFlow.Scaling.PrunedScalingContract
import Mathlib.Tactic.Ring

/-!
# Pruned scaling space in the original dimensions

Pruning retains the vertex set and only removes edge slots. The augmented
capacity budget and cost-round number base can therefore only decrease.
The original cost-scaling reserve covers the nested compacted solve, while
compaction, conversion, and scatter add at most `2+10*m` cells.
-/

public section
namespace MinCostFlow.Scaling.Machine

/-- Deleting zero-capacity slots cannot enlarge the complete nested
cost-scaling workspace, including its augmented capacity budget. -/
theorem withoutZeroEdges_costScalingSpace_le (J : Circulation) (C U : ℕ) :
    costScalingSpace J.withoutZeroEdges C (max U (2*J.withoutZeroEdges.m+1))≤
      costScalingSpace J C (max U (2*J.m+1)) := by
  let K := J.withoutZeroEdges
  have hm : K.m≤J.m := J.positiveEdges_length_le
  have hn : K.n=J.n := rfl
  have hV : max U (2*K.m+1)≤max U (2*J.m+1) := max_le_max le_rfl (by omega)
  have hp := Nat.pow_le_pow_left (show K.m+K.m≤J.m+J.m by omega) 10
  have hD : costStepNumberBase K C (max U (2*K.m+1))≤
      costStepNumberBase J C (max U (2*J.m+1)) := by
    unfold costStepNumberBase
    rw [hn]
    omega
  have hN := Nat.pow_le_pow_left hD 524
  have hc := Nat.mul_le_mul_left (costRounds J.n C+2) hN
  have hlenK := K.solverWords_length
  have hlenJ := J.solverWords_length
  change costScalingSpace K C (max U (2*K.m+1))≤_
  unfold costScalingSpace
  rw [hn,hlenK,hlenJ]
  omega

/-- Original dimensions cover the pruned solve and every linear adapter
allocation together. -/
theorem prunedScalingSpace_le (J : Circulation) (C U : ℕ) :
    prunedScalingSpace J C U≤2+10*J.m+costScalingSpace J C (max U (2*J.m+1)) := by
  have hm := J.positiveEdges_length_le
  have hs := withoutZeroEdges_costScalingSpace_le J C U
  change J.withoutZeroEdges.m≤J.m at hm
  unfold prunedScalingSpace
  omega

end MinCostFlow.Scaling.Machine
