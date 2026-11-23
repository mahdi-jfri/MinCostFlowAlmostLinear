module

public import MinCostFlow.Scaling.MeasuredCostScaling

/-!
# The measured cost loop pays for round control

The counted loop adds one work unit after every step, regardless of the
step's own work. Induction therefore bounds its length by its work. This
pays for logarithmic round counting and constant initialization overhead
when the complete machine entry is composed.
-/

public section
namespace MinCostFlow.Scaling.Machine

private theorem rounds_le_work {α : Type} (step : α → CallResult α) (fuel : ℕ) (a : α) :
    fuel≤(CallResult.forRounds step fuel a).work := by
  induction fuel with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
    change fuel+1≤(CallResult.forRounds step fuel a).work+
      ((step (CallResult.forRounds step fuel a).value).work+1)
    omega

/-- Every measured cost prefix pays for at least one control operation
per prescribed round. -/
theorem costMeasuredPrefix_rounds_le_work
    (inner : (K : Circulation) → CallResult (Fin K.m → ℤ)) (J : Circulation) (C fuel : ℕ) :
    fuel≤(CallResult.forRounds (CostState.stepMeasured inner C) fuel (CostState.initial J)).work :=
  rounds_le_work _ _ _

/-- The complete measured cost loop's work covers its exact round count. -/
theorem costLoopMeasured_rounds_le_work
    (inner : (K : Circulation) → CallResult (Fin K.m → ℤ)) (J : Circulation) (C : ℕ) :
    costRounds J.n C≤(costLoopMeasured inner J C).work := rounds_le_work _ _ _

end MinCostFlow.Scaling.Machine
