module

public import MinCostFlow.Scaling.CostCapacityModel

/-!
# The measured scaling model pays for constant entry overhead

The empty graph has work one. Every nonempty branch includes a positive
setup charge before any called procedure's nonnegative work. Thus the
complete model always pays for at least one operation, which covers a
constant capacity-budget augmentation entry.
-/

public section
namespace MinCostFlow.Scaling.Machine

/-- Every measured cost-scaling branch has positive model work. -/
theorem costScalingMeasured_work_pos
    (inner : (K : Circulation) → CallResult (Fin K.m → ℤ)) (J : Circulation) (C : ℕ) :
    1≤(costScalingMeasured inner J C).work := by
  unfold costScalingMeasured
  split
  · exact le_rfl
  · dsimp only
    split <;> dsimp only <;> omega

/-- The complete cost-capacity model always pays for constant entry work. -/
theorem costCapacityModel_work_pos (solve : (J : Circulation) → Fin J.m → ℤ)
    (J : Circulation) (C U : ℕ) : 1≤(costCapacityModel solve J C U).work :=
  costScalingMeasured_work_pos _ _ _

end MinCostFlow.Scaling.Machine
