module

public import MinCostFlow.Scaling.BottleneckSearch

/-!
# Interval bounds for the concrete bottleneck search

The model chooses the midpoint of a half-open candidate interval. A
nonempty interval gives a valid candidate index, and either acceptance
branch leaves a valid interval. These arithmetic facts justify the
machine's indexed candidate read and its next iteration.
-/

public section
namespace MinCostFlow.Scaling

/-- Midpoint arithmetic for a nonempty candidate interval. -/
theorem bottleneck_mid_bounds {lower upper count : ℕ} (hl : lower<upper) (hu : upper≤count) :
    lower≤(lower+upper)/2 ∧ (lower+upper)/2<upper ∧ (lower+upper)/2<count := by
  omega

/-- Every actual model step preserves the interval endpoints' range. -/
theorem bottleneckStep_interval (solve : (J : Circulation) → Fin J.m → ℤ)
    {J : Circulation} (candidates : List ℕ) (s : BottleneckState J) (count : ℕ)
    (hl : s.lower≤s.upper) (hu : s.upper≤count) :
    (BottleneckState.step solve candidates s).value.lower≤
      (BottleneckState.step solve candidates s).value.upper ∧
      (BottleneckState.step solve candidates s).value.upper≤count := by
  unfold BottleneckState.step
  split
  · rename_i hactive
    have hm := bottleneck_mid_bounds hactive hu
    dsimp only
    split <;> dsimp only <;> omega
  · exact ⟨hl,hu⟩

/-- A nonempty model step performs exactly the signed acceptance update
on the flow returned by its own threshold solve. -/
theorem bottleneckStep_value_active (solve : (J : Circulation) → Fin J.m → ℤ)
    {J : Circulation} (candidates : List ℕ) (s : BottleneckState J) (ha : s.lower<s.upper) :
    (BottleneckState.step solve candidates s).value =
      let mid := (s.lower+s.upper)/2
      let u := candidates.getD mid 0
      let K := J.bottleneckGraph u
      let flow := Circulation.solveWithZeroCapacities solve K
      if K.integerObjective flow<0 then ⟨mid+1,s.upper,some (u,flow)⟩ else {s with upper:=mid} := by
  simp only [BottleneckState.step,ha,↓reduceIte]

/-- Empty intervals leave the model state unchanged and make no solve. -/
theorem bottleneckStep_value_inactive (solve : (J : Circulation) → Fin J.m → ℤ)
    {J : Circulation} (candidates : List ℕ) (s : BottleneckState J) (ha : ¬s.lower<s.upper) :
    (BottleneckState.step solve candidates s).value=s := by
  simp only [BottleneckState.step,ha,↓reduceIte]

end MinCostFlow.Scaling
