module

public import MinCostFlow.Scaling.StrongDuality
import Mathlib.Tactic.Linarith

/-!
# Optimality from residual cycles

The stopping argument of Lemma C.5 in Appendix C of Chen et al.,
arXiv:2203.00671v2, excludes negative residual cycles. Shortest-walk labels
then give a dual certificate with the same objective as the feasible flow.
This file supplies that implication without assuming an optimal primal flow.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Nonnegative closed residual walks certify optimality of an integral flow
against every feasible real circulation. -/
theorem optimal_of_residual_closed_nonneg (I : Circulation) (f : Fin I.m → ℤ)
    (hf : I.Feasible (fun e => (f e : ℝ)))
    (hclosed : ∀ v : Fin I.n, ∀ p : (I.residual f).DirectedWalk v v, 0 ≤ p.cost) :
    I.Optimal (fun e => (f e : ℝ)) := by
  obtain ⟨y, hy⟩ := (I.residual f).exists_potential_of_closed_nonneg hclosed
  have hforward : ∀ e, (f e : ℝ) < I.capacity e →
      0 ≤ I.reducedCost (fun v => (y v : ℝ)) e := by
    intro e he
    have hint : f e < (I.capacity e : ℤ) := by
      apply (Int.cast_lt (R := ℝ)).mp
      simpa only [Int.cast_natCast] using he
    have ha : 0 < (I.residual f).capacity (Fin.castAdd I.m e) := by
      simp only [Fin.addCases_left]
      exact Int.lt_toNat.mpr (sub_pos.mpr hint)
    have h := (Int.cast_le (R := ℝ)).mpr (hy (Fin.castAdd I.m e) ha)
    simp only [Fin.addCases_left, Int.cast_sub] at h
    exact sub_nonneg.mpr h
  have hreverse : ∀ e, 0 < (f e : ℝ) →
      I.reducedCost (fun v => (y v : ℝ)) e ≤ 0 := by
    intro e he
    have hint : 0 < f e := (Int.cast_pos (R := ℝ)).mp he
    have ha : 0 < (I.residual f).capacity (Fin.natAdd I.m e) := by
      simp only [Fin.addCases_right]
      exact Int.lt_toNat.mpr hint
    have h := (Int.cast_le (R := ℝ)).mpr (hy (Fin.natAdd I.m e) ha)
    simp only [Fin.addCases_right, Int.cast_sub, Int.cast_neg] at h
    dsimp only [reducedCost, potentialDifference]
    linarith only [h]
  exact I.optimal_of_dual_equality _ _ _ _ hf (I.slacks_dualFeasible _)
    (I.dual_equality_of_residual_potential _ hf _ hforward hreverse)

end MinCostFlow.Scaling.Circulation
