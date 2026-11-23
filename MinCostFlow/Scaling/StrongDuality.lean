module

public import MinCostFlow.Scaling.DualCertificate
public import MinCostFlow.Scaling.ResidualReduction
public import MinCostFlow.Scaling.ResidualPotential
import Mathlib.Tactic.Linarith

/-!
# Strong duality at an integral optimum

Appendix C of Chen et al., arXiv:2203.00671v2, uses strong duality for integral
primal optima returned by circulation solvers. At such an optimum the residual
problem has zero as an optimum. Closed residual walks therefore have nonnegative
cost. Their shortest-walk labels give a potential, and its reduced-cost slacks
have dual objective equal to the primal objective.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- An optimal integral circulation admits an integral potential satisfying the
forward and reverse reduced-cost inequalities of its residual graph. -/
theorem exists_optimal_residual_potential (I : Circulation) (f : Fin I.m → ℤ)
    (hf : I.Optimal (fun e => (f e : ℝ))) :
    ∃ y : Fin I.n → ℤ,
      (∀ e, (f e : ℝ) < I.capacity e →
        0 ≤ I.reducedCost (fun v => (y v : ℝ)) e) ∧
      (∀ e, 0 < (f e : ℝ) → I.reducedCost (fun v => (y v : ℝ)) e ≤ 0) := by
  have hzero := I.zero_residual_optimal f hf
  have hclosed : ∀ v : Fin I.n, ∀ p : (I.residual f).DirectedWalk v v,
      0 ≤ p.cost := fun _ p => p.cost_nonneg_of_zero_optimal hzero
  obtain ⟨y, hy⟩ := (I.residual f).exists_potential_of_closed_nonneg hclosed
  refine ⟨y, ?_, ?_⟩
  · intro e he
    have hint : f e < (I.capacity e : ℤ) := by
      apply (Int.cast_lt (R := ℝ)).mp
      simpa only [Int.cast_natCast] using he
    have ha : 0 < (I.residual f).capacity (Fin.castAdd I.m e) := by
      simp only [Fin.addCases_left]
      exact Int.lt_toNat.mpr (sub_pos.mpr hint)
    have h := (Int.cast_le (R := ℝ)).mpr (hy (Fin.castAdd I.m e) ha)
    simp only [Fin.addCases_left, Int.cast_sub] at h
    exact sub_nonneg.mpr h
  · intro e he
    have hint : 0 < f e := (Int.cast_pos (R := ℝ)).mp he
    have ha : 0 < (I.residual f).capacity (Fin.natAdd I.m e) := by
      simp only [Fin.addCases_right]
      exact Int.lt_toNat.mpr hint
    have h := (Int.cast_le (R := ℝ)).mpr (hy (Fin.natAdd I.m e) ha)
    simp only [Fin.addCases_right, Int.cast_sub, Int.cast_neg] at h
    dsimp only [reducedCost, potentialDifference]
    linarith only [h]

/-- Strong duality for the integral primal optima used in Appendix C: there
exists a feasible dual solution with equal objective. The potential can be
chosen integral, and no assumption about a dual solver is needed. -/
theorem strong_duality (I : Circulation) (f : Fin I.m → ℤ)
    (hf : I.Optimal (fun e => (f e : ℝ))) :
    ∃ y : Fin I.n → ℤ, ∃ lower upper : Fin I.m → ℝ,
      I.DualFeasible (fun v => (y v : ℝ)) lower upper ∧
      I.objective (fun e => (f e : ℝ)) = I.dualObjective upper := by
  obtain ⟨y, hforward, hreverse⟩ := I.exists_optimal_residual_potential f hf
  exact ⟨y, I.lowerSlack (fun v => (y v : ℝ)),
    I.upperSlack (fun v => (y v : ℝ)),
    I.slacks_dualFeasible _,
    I.dual_equality_of_residual_potential _ hf.1 _ hforward hreverse⟩

end MinCostFlow.Scaling.Circulation
