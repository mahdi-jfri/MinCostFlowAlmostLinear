module

public import MinCostFlow.Scaling.FiniteIntegralMinimum
public import MinCostFlow.Scaling.ApproximationCorrectness
public import MinCostFlow.Scaling.ResidualOptimality
import MinCostFlow.Scaling.ResidualBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The integral optimum used by the capacity-scaling gap proof

The proof of Lemma C.9 of Chen et al., arXiv:2203.00671v2, Appendix C,
uses an integral optimum to make the final gap either zero or at least one.
Choose a least-cost feasible integer flow from the finite set of bounded
tables. Applying the proved C.10 routine to its residual graph cannot return
a negative integral augmentation, since that would improve this minimum.
Its magnitude is therefore zero, certifying real optimality. This uses only
the bounded primal procedure already assumed in C.9.
-/

public section
namespace MinCostFlow.Scaling.Circulation

/-- Under the source's bounded solver hypothesis, an integer minimum is a
minimum against all feasible real flows as well. -/
theorem integral_minimum_optimal
    (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) (hc : I.CostsBounded (I.m ^ 10)) (f : Fin I.m → ℤ)
    (hf : I.Feasible (fun e => (f e : ℝ)))
    (hmin : ∀ g : Fin I.m → ℤ, I.Feasible (fun e => (g e : ℝ)) →
      I.integerObjective f ≤ I.integerObjective g) : I.Optimal (fun e => (f e : ℝ)) := by
  let R := I.residual f
  let r := (polyApproxModel solve R).value
  have hr := lemma_C_10 solve hsolve R (I.residual_polynomialCosts f hc)
  change R.Feasible (fun e => (r.flow e : ℝ)) ∧
    R.objective (fun e => (r.flow e : ℝ)) = -(r.magnitude : ℝ) ∧ _ at hr
  let next : Fin I.m → ℤ := fun e => f e + r.flow (Fin.castAdd I.m e) - r.flow (Fin.natAdd I.m e)
  have hcast : (fun e => (next e : ℝ)) = I.augment f (fun e => (r.flow e : ℝ)) := by
    funext e
    simp only [next, augment, project, Int.cast_add, Int.cast_sub]
    ring
  have hnext : I.Feasible (fun e => (next e : ℝ)) := by
    rw [hcast]
    exact I.augment_feasible f hf _ hr.1
  have hcmp := (Int.cast_le (R := ℝ)).mpr (hmin next hnext)
  rw [I.integerObjective_cast, I.integerObjective_cast, hcast, I.augment_objective, hr.2.1] at hcmp
  have hzero : r.magnitude = 0 := by
    have hnon : (0 : ℝ) ≤ r.magnitude := Nat.cast_nonneg _
    have heq : (r.magnitude : ℝ) = 0 := by linarith only [hcmp, hnon]
    exact_mod_cast heq
  have hopt := hr.2.2.2 hzero
  have hcost : R.objective (fun e => (r.flow e : ℝ)) = 0 := by rw [hr.2.1, hzero, Nat.cast_zero, neg_zero]
  have hRzero : R.Optimal (fun _ => 0) := by
    refine ⟨R.zero_feasible, ?_⟩
    intro g hg
    have hh := hopt.2 g hg
    rw [hcost] at hh
    simpa only [objective, mul_zero, Finset.sum_const_zero] using hh
  exact I.optimal_of_residual_closed_nonneg f hf (fun _ p => p.cost_nonneg_of_zero_optimal hRzero)

/-- The given bounded solver suffices to justify the integral optimum used
in the proof of Lemma C.9, without assuming another integrality theorem. -/
theorem exists_integral_optimum_of_bounded_solver
    (solve : (J : Circulation) → Fin J.m → ℤ)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (I : Circulation) (hc : I.CostsBounded (I.m ^ 10)) :
    ∃ f : Fin I.m → ℤ, I.Optimal (fun e => (f e : ℝ)) := by
  obtain ⟨f, hf, hmin⟩ := I.exists_integral_minimum
  exact ⟨f, I.integral_minimum_optimal solve hsolve hc f hf hmin⟩

end MinCostFlow.Scaling.Circulation
