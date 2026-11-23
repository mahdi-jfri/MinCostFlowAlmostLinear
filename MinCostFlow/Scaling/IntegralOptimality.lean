module

public import MinCostFlow.Scaling.FiniteIntegralMinimum
public import MinCostFlow.Scaling.CycleSum
public import MinCostFlow.Scaling.CycleScatter
public import MinCostFlow.Scaling.ResidualGap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Integral minima are exact real minima

The integral optimum used in Appendix C of Chen et al., arXiv:2203.00671v2,
can be obtained without assuming a solver. A minimum among bounded integer
tables has no improving unit augmentation along a simple residual cycle.
Decomposing any residual circulation into simple cycles then proves that its
cost is nonnegative. The residual difference of any real competitor therefore
cannot improve the integer minimum.
-/

public section
namespace MinCostFlow.Scaling.Circulation

/-- Minimizing over feasible integral flows already minimizes over feasible
real flows. Integer capacities make each simple residual cycle an admissible
unit augmentation. No algorithmic hypothesis is needed. -/
theorem optimal_of_integer_minimum (I : Circulation) (f : Fin I.m → ℤ)
    (hf : I.Feasible (fun e => (f e : ℝ)))
    (hmin : ∀ g : Fin I.m → ℤ, I.Feasible (fun e => (g e : ℝ)) →
      I.integerObjective f ≤ I.integerObjective g) :
    I.Optimal (fun e => (f e : ℝ)) := by
  let R := I.residual f
  have hcycle (v : Fin R.n) (p : R.DirectedWalk v v) (hp : ∀ e, p.count e ≤ 1) : 0 ≤ p.cost := by
    let g : Fin R.m → ℤ := fun e => (p.count e : ℤ)
    have hg : R.Feasible (fun e => (g e : ℝ)) := by
      have hh := p.scaled_counts_feasible hp 1 (fun e he => p.active_of_count_pos e he)
      simpa only [g, Int.cast_natCast, Nat.cast_one, one_mul] using hh
    let next : Fin I.m → ℤ := fun e => f e + g (Fin.castAdd I.m e) - g (Fin.natAdd I.m e)
    have hcast : (fun e => (next e : ℝ)) = I.augment f (fun e => (g e : ℝ)) := by
      funext e
      simp only [next, augment, project, Int.cast_add, Int.cast_sub]
      ring
    have hnext : I.Feasible (fun e => (next e : ℝ)) := by
      rw [hcast]
      exact I.augment_feasible f hf _ hg
    have hcmp := (Int.cast_le (R := ℝ)).mpr (hmin next hnext)
    rw [I.integerObjective_cast, I.integerObjective_cast, hcast, I.augment_objective] at hcmp
    have hcost : R.objective (fun e => (g e : ℝ)) = (p.cost : ℝ) := by
      simpa only [g, Int.cast_natCast] using p.objective_count
    rw [hcost] at hcmp
    have hh : (0 : ℝ) ≤ p.cost := by linarith only [hcmp]
    exact_mod_cast hh
  have hzero : R.Optimal (fun _ => 0) := by
    refine ⟨R.zero_feasible, ?_⟩
    intro g hg
    obtain ⟨terms, _, ht, hsum⟩ := R.exists_cycle_decomposition g hg
    rw [← hsum, R.cycleSum_objective]
    have hh : (0 : ℝ) ≤ (terms.map (fun t => t.amount * (t.walk.cost : ℝ))).sum := by
      apply List.sum_nonneg
      intro a ha
      obtain ⟨t, hmem, rfl⟩ := List.mem_map.mp ha
      exact mul_nonneg (ht t hmem).1.le (Int.cast_nonneg_iff.mpr (hcycle t.vertex t.walk (ht t hmem).2.2))
    simpa only [objective, mul_zero, Finset.sum_const_zero] using hh
  exact I.optimal_of_zero_residual_optimum f hf hzero

/-- Every integral-capacity circulation has an integral optimum against all
feasible real flows. This existence statement assumes no solver. -/
theorem exists_integral_optimum (I : Circulation) :
    ∃ f : Fin I.m → ℤ, I.Optimal (fun e => (f e : ℝ)) := by
  obtain ⟨f, hf, hmin⟩ := I.exists_integral_minimum
  exact ⟨f, I.optimal_of_integer_minimum f hf hmin⟩

end MinCostFlow.Scaling.Circulation
