module

public import MinCostFlow.Scaling.ResidualReduction
public import MinCostFlow.Scaling.SolverAdapter
import Mathlib.Tactic.Linarith

/-!
# Bounds on residual solver instances

The scaling reductions in Appendix C of Chen et al., arXiv:2203.00671v2, call
solvers on residual graphs. A residual graph has twice as many edge slots,
unchanged absolute costs, and capacities no larger than the original capacity
bound. These facts also hold when inactive slots are replaced by the dummy loops
of the bounded-solver adapter.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Reversing an arc changes the sign but not the absolute value of its cost. -/
theorem residual_costsBounded (I : Circulation) (f : Fin I.m → ℤ) (C : ℕ)
    (hc : I.CostsBounded C) : (I.residual f).CostsBounded C := by
  intro a
  refine Fin.addCases (fun e => ?_) (fun e => ?_) a
  · simpa only [Fin.addCases_left] using hc e
  · simpa only [Fin.addCases_right, Int.natAbs_neg] using hc e

/-- Residual capacities are bounded by `U` when the original capacities are.
Both directions use the original flow's capacity constraints. -/
theorem residual_capacities_le (I : Circulation) (f : Fin I.m → ℤ)
    (hf : ∀ e, 0 ≤ (f e : ℝ) ∧ (f e : ℝ) ≤ I.capacity e)
    (U : ℕ) (hu : ∀ e, I.capacity e ≤ U) :
    ∀ a, (I.residual f).capacity a ≤ U := by
  intro a
  refine Fin.addCases (fun e => ?_) (fun e => ?_) a
  · have hcap := (I.residual_capacity_cast f hf e).1
    have hc : (I.capacity e : ℝ) ≤ U := by exact_mod_cast hu e
    have hb : ((I.residual f).capacity (Fin.castAdd I.m e) : ℝ) ≤ U := by
      rw [hcap]
      linarith only [hc, (hf e).1]
    exact_mod_cast hb
  · have hcap := (I.residual_capacity_cast f hf e).2
    have hc : (I.capacity e : ℝ) ≤ U := by exact_mod_cast hu e
    have hb : ((I.residual f).capacity (Fin.natAdd I.m e) : ℝ) ≤ U := by
      rw [hcap]
      exact le_trans (hf e).2 hc
    exact_mod_cast hb

/-- The polynomial-cost requirement is still valid when the edge count doubles. -/
theorem residual_polynomialCosts (I : Circulation) (f : Fin I.m → ℤ)
    (hc : I.CostsBounded (I.m ^ 10)) :
    (I.residual f).CostsBounded ((I.residual f).m ^ 10) := by
  intro e
  have h := I.residual_costsBounded f _ hc e
  exact le_trans h (Nat.pow_le_pow_left (Nat.le_add_right _ _) 10)

end MinCostFlow.Scaling.Circulation
