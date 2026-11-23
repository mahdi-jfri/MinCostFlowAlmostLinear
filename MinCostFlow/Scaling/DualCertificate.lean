module

public import MinCostFlow.Scaling.Circulation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Dual certificates from residual potentials

Appendix C of Chen et al., arXiv:2203.00671v2, uses strong duality and
complementary slackness. This file proves the algebraic part: a potential with
nonnegative reduced costs on residual arcs gives feasible slacks and an equal
primal and dual objective. Conversely, equality forces complementary slackness.
The potential has the incidence sign of `Instance`, positive at the tail.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The lower slack determined by a potential. -/
def lowerSlack (I : Circulation) (y : Fin I.n → ℝ) (e : Fin I.m) : ℝ :=
  max (I.reducedCost y e) 0

/-- The upper slack determined by a potential. -/
def upperSlack (I : Circulation) (y : Fin I.n → ℝ) (e : Fin I.m) : ℝ :=
  max (-I.reducedCost y e) 0

/-- Taking the positive and negative parts of reduced costs gives feasible
slacks for every potential, including edges of capacity zero. -/
theorem slacks_dualFeasible (I : Circulation) (y : Fin I.n → ℝ) :
    I.DualFeasible y (I.lowerSlack y) (I.upperSlack y) := by
  refine ⟨fun e => ⟨le_max_right _ _, le_max_right _ _⟩, ?_⟩
  intro e
  rcases le_total 0 (I.reducedCost y e) with hr | hr
  · simp only [lowerSlack, upperSlack, max_eq_left hr,
      max_eq_right (neg_nonpos.mpr hr), sub_zero]
    dsimp only [reducedCost]
    ring
  · simp only [lowerSlack, upperSlack, max_eq_right hr,
      max_eq_left (neg_nonneg.mpr hr), add_zero]
    dsimp only [reducedCost]
    ring

/-- Residual reduced-cost inequalities yield an equal primal and dual
objective, as used in the strong-duality argument of Appendix C. -/
theorem dual_equality_of_residual_potential (I : Circulation)
    (f : Fin I.m → ℝ) (hf : I.Feasible f) (y : Fin I.n → ℝ)
    (hforward : ∀ e, f e < I.capacity e → 0 ≤ I.reducedCost y e)
    (hreverse : ∀ e, 0 < f e → I.reducedCost y e ≤ 0) :
    I.objective f = I.dualObjective (I.upperSlack y) := by
  have he : ∀ e, I.reducedCost y e * f e =
      -(I.upperSlack y e * (I.capacity e : ℝ)) := by
    intro e
    rcases le_total 0 (I.reducedCost y e) with hr | hr
    · rw [upperSlack, max_eq_right (neg_nonpos.mpr hr)]
      by_cases hz : f e = 0
      · simp [hz]
      · have hp : 0 < f e := lt_of_le_of_ne (hf.2 e).1 (Ne.symm hz)
        have hc : I.reducedCost y e = 0 := le_antisymm (hreverse e hp) hr
        rw [hc]
        simp
    · rw [upperSlack, max_eq_left (neg_nonneg.mpr hr)]
      by_cases hs : f e = I.capacity e
      · rw [hs]
        ring
      · have hp : f e < I.capacity e := lt_of_le_of_ne (hf.2 e).2 hs
        have hc : I.reducedCost y e = 0 := le_antisymm hr (hforward e hp)
        rw [hc]
        simp
  rw [← I.reducedCost_objective f hf.1 y]
  simp only [he, dualObjective, Finset.sum_neg_distrib]

/-- The duality gap is the sum of the two nonnegative slack products. -/
theorem duality_gap (I : Circulation) (f : Fin I.m → ℝ) (hf : I.Conserves f)
    (y : Fin I.n → ℝ) (lower upper : Fin I.m → ℝ)
    (hd : I.DualFeasible y lower upper) :
    I.objective f - I.dualObjective upper =
      ∑ e, (lower e * f e + upper e * ((I.capacity e : ℝ) - f e)) := by
  have hp : (∑ e, I.potentialDifference y e * f e) = 0 := by
    rw [potential_pairing]
    have hz : ∀ v, I.balance f v = 0 := hf
    simp [hz]
  have he : ∀ e, lower e * f e + upper e * ((I.capacity e : ℝ) - f e) =
      (I.cost e : ℝ) * f e + upper e * (I.capacity e : ℝ) -
        I.potentialDifference y e * f e := by
    intro e
    rw [← hd.2 e]
    ring
  simp only [he, Finset.sum_sub_distrib, Finset.sum_add_distrib, hp,
    sub_zero, objective, dualObjective, sub_neg_eq_add]

/-- Complementary slackness for the primal and dual of Appendix C: equality
of feasible objectives forces both slack products to vanish at every edge. -/
theorem complementary_slackness (I : Circulation) (f : Fin I.m → ℝ)
    (hf : I.Feasible f) (y : Fin I.n → ℝ) (lower upper : Fin I.m → ℝ)
    (hd : I.DualFeasible y lower upper)
    (heq : I.objective f = I.dualObjective upper) :
    ∀ e, lower e * f e = 0 ∧ upper e * ((I.capacity e : ℝ) - f e) = 0 := by
  have hnon : ∀ e, 0 ≤ lower e * f e ∧
      0 ≤ upper e * ((I.capacity e : ℝ) - f e) := by
    intro e
    exact ⟨mul_nonneg (hd.1 e).1 (hf.2 e).1,
      mul_nonneg (hd.1 e).2 (sub_nonneg.mpr (hf.2 e).2)⟩
  have hs := I.duality_gap f hf.1 y lower upper hd
  rw [heq, sub_self] at hs
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun e (_ : e ∈ Finset.univ) => add_nonneg (hnon e).1 (hnon e).2)).mp hs.symm
  intro e
  have he := hz e (Finset.mem_univ e)
  constructor <;> linarith only [he, (hnon e).1, (hnon e).2]

end MinCostFlow.Scaling.Circulation
