module

public import MinCostFlow.Scaling.DualCertificate
import Mathlib.Tactic.Linarith

/-!
# Residual signs from a primal-dual optimum

The proof of Lemma C.7 in Appendix C of Chen et al., arXiv:2203.00671v2,
uses complementary slackness on each rounded residual arc. A nonsaturated
arc has nonnegative reduced cost and a positive-flow arc has nonpositive
reduced cost. We derive both from feasible equal-value primal and dual data.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The forward and reverse residual signs of any equal-value primal-dual pair.
This is the complementary-slackness step of Lemma C.7. -/
theorem residual_signs_of_dual_equality (I : Circulation) (f : Fin I.m → ℝ)
    (y : Fin I.n → ℝ) (lower upper : Fin I.m → ℝ)
    (hf : I.Feasible f) (hd : I.DualFeasible y lower upper)
    (heq : I.objective f = I.dualObjective upper) :
    ∀ e, (f e < I.capacity e → 0 ≤ I.reducedCost y e) ∧
      (0 < f e → I.reducedCost y e ≤ 0) := by
  have hcomp := I.complementary_slackness f hf y lower upper hd heq
  intro e
  constructor
  · intro hlt
    have hz : upper e = 0 := (mul_eq_zero.mp (hcomp e).2).resolve_right
      (ne_of_gt (sub_pos.mpr hlt))
    have he := hd.2 e
    rw [hz, sub_zero] at he
    dsimp only [reducedCost]
    linarith only [he, (hd.1 e).1]
  · intro hpos
    have hz : lower e = 0 := (mul_eq_zero.mp (hcomp e).1).resolve_right (ne_of_gt hpos)
    have he := hd.2 e
    rw [hz, add_zero] at he
    dsimp only [reducedCost]
    linarith only [he, (hd.1 e).2]

end MinCostFlow.Scaling.Circulation
