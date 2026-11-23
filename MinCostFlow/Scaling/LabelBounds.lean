module

public import MinCostFlow.Scaling.LabelTraversal

/-!
# Integer bounds for the counted label traversal

A newly reached vertex receives its parent's label minus one edge cost.
Thus one step increases the maximum label magnitude by at most the maximum
cost magnitude. A run of `fuel` steps needs only the initial bound plus
`fuel` times that cost bound. These estimates supply the machine traversal's
signed-arithmetic budgets.
-/

public section
namespace MinCostFlow.Scaling.Circulation.LabelState

/-- One label step increases the uniform magnitude bound by at most one
edge-cost bound. -/
theorem step_labels_bound {J : Circulation} (s : LabelState J) (B C : ℕ)
    (hl : ∀ v, (s.labels v).natAbs ≤ B) (hc : ∀ e, (J.cost e).natAbs ≤ C) :
    ∀ v, (s.step.1.labels v).natAbs ≤ B+C := by
  intro v
  cases hp : s.pending with
  | nil =>
    simpa only [step, hp] using (hl v).trans (Nat.le_add_right B C)
  | cons e rest =>
    simp only [step, hp]
    split
    · exact (hl v).trans (Nat.le_add_right B C)
    · by_cases hv : v = J.head e
      · subst v
        simp only [Function.update_self]
        exact (Int.natAbs_sub_le _ _).trans (Nat.add_le_add (hl _) (hc e))
      · simp only [Function.update_of_ne hv]
        exact (hl v).trans (Nat.le_add_right B C)

/-- Every label after a counted run fits the initial bound plus one cost
bound per allowed step. -/
theorem run_labels_bound {J : Circulation} (fuel : ℕ) (s : LabelState J) (B C : ℕ)
    (hl : ∀ v, (s.labels v).natAbs ≤ B) (hc : ∀ e, (J.cost e).natAbs ≤ C) :
    ∀ v, ((run fuel s).1.labels v).natAbs ≤ B+fuel*C := by
  induction fuel generalizing s B with
  | zero => simpa only [run, Nat.zero_mul, Nat.add_zero] using hl
  | succ fuel ih =>
    rw [run]
    split
    · intro v
      exact (hl v).trans (Nat.le_add_right _ _)
    · have h := ih s.step.1 (B+C) (step_labels_bound s B C hl hc)
      intro v
      have hv := h v
      dsimp only
      rw [Nat.succ_mul]
      omega

end MinCostFlow.Scaling.Circulation.LabelState
