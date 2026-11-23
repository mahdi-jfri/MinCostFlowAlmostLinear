module

public import MinCostFlow.IPM.Definitions
import Mathlib.Tactic.Linarith

/-!
# A bounded interval for the optimal-cost search

Section 4 of Chen et al., arXiv:2203.00671v2 (page 24), proposes binary
search for the unknown optimal cost. Every feasible flow has cost in
`[-m U², m U²]` when all costs and capacities have absolute value at most
`U`. Applying this bound to the augmented instance of Lemma 4.12 gives
a finite initial search interval.
-/

public section
namespace MinCostFlow.IPM

/-- Feasible coordinates lie in the same absolute-value bound as the
integral lower and upper capacities. -/
theorem feasible_abs_le (I : Instance) (U : ℝ) (hnums : NumbersBounded I U)
    (f : Fin I.m → ℝ) (hf : I.IsFeasible f) (e : Fin I.m) : |f e| ≤ U := by
  apply abs_le.mpr
  exact ⟨(abs_le.mp (hnums.2 e).1).1.trans (hf.2 e).1,
    (hf.2 e).2.trans (abs_le.mp (hnums.2 e).2.1).2⟩

/-- The initial bounded interval for the optimal-cost search of Section 4
(page 24). This holds for every feasible real flow, including an optimum. -/
theorem feasible_cost_abs_le (I : Instance) (U : ℝ) (hU : 0 ≤ U)
    (hnums : NumbersBounded I U) (f : Fin I.m → ℝ) (hf : I.IsFeasible f) :
    |I.cost f| ≤ I.m*U^2 := by
  calc
    |I.cost f| ≤ ∑ e, |((I.edge e).cost : ℝ)*f e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin I.m, U^2 := by
      apply Finset.sum_le_sum
      intro e _
      rw [abs_mul, pow_two]
      exact mul_le_mul (hnums.2 e).2.2 (feasible_abs_le I U hnums f hf e)
        (abs_nonneg _) hU
    _ = I.m*U^2 := by simp [mul_comm]

end MinCostFlow.IPM
