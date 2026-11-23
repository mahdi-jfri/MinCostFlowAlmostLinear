module

public import MinCostFlow.Scaling.CostUpperClipping
public import MinCostFlow.Scaling.RoundedProgress
public import MinCostFlow.Scaling.DualResidualSigns
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Progress of an integer cost-scaling round

Lemma C.7 of Chen et al., arXiv:2203.00671v2, Appendix C, halves epsilon
using an optimal primal-dual solution of the rounded residual instance.
We prove it for the integer model. Its integer dual potential is measured in
rounding units, so the physical update multiplies by that unit. High costs
are clipped while their slots are kept. The high-cost cycle argument shows
that clipping does not affect any used arc, and all remaining forward
constraints retain the required one-sided error bound.
-/

@[expose] public section
namespace MinCostFlow.Scaling.CostState
variable {I : Circulation}

/-- Lemma C.7 (Appendix C), for the integer representation with retained
clipped slots: an optimal rounded primal-dual pair halves epsilon.
The physical dual update includes the cost unit used to normalize integers. -/
theorem lemma_C_7 (C : ℕ) (s : CostState I)
    (hm : 0 < I.m) (hn : I.n ≤ I.m + I.m) (hp : 0 < s.power)
    (hopt : I.EpsilonOptimalWith (fun e => (s.flow e : ℝ)) (s.epsilon C)
      (realPotential (I := I) C s))
    (g : Fin (I.m + I.m) → ℤ)
    (hg : (s.roundedInstance C).Optimal (fun e => (g e : ℝ)))
    (dy : Fin I.n → ℝ) (lower upper : Fin (I.m + I.m) → ℝ)
    (hd : (s.roundedInstance C).DualFeasible dy lower upper)
    (heq : (s.roundedInstance C).objective (fun e => (g e : ℝ)) =
      (s.roundedInstance C).dualObjective upper) :
    I.EpsilonOptimalWith (I.augment s.flow (fun e => (g e : ℝ))) (s.epsilon C / 2)
      (fun v => realPotential (I := I) C s v + s.roundingUnit C * dy v) := by
  have hunit := s.roundingUnit_pos C hm hp
  have heps : 0 < s.epsilon C / 2 := by
    have hh : (0 : ℝ) < s.epsilon C := hopt.1
    exact div_pos hh (by norm_num)
  have hsign := (s.roundedInstance C).residual_signs_of_dual_equality
    (fun e => (g e : ℝ)) dy lower upper hg.1 hd heq
  apply I.epsilonOptimalWith_augment_of_rounded_signs s.flow hopt.2.1
    (fun e => (g e : ℝ)) hg.1 (realPotential (I := I) C s)
    (fun v => s.roundingUnit C * dy v)
    (fun e => s.roundingUnit C * ((s.roundedInstance C).cost e : ℝ))
    (s.roundingUnit C) (s.epsilon C / 2) heps (s.roundingUnit_lt_half C hm hp)
  · intro e he
    refine ⟨(s.roundedInstance_lower_error C hm hp hopt e he).le, ?_⟩
    intro hpos
    have hpos' : 0 < g e := Int.cast_pos.mp hpos
    rw [s.roundedInstance_cost_eq_of_pos C hm hn hp hopt g hg e hpos']
    exact (s.roundedCost_error C hm hp e).2.le
  · intro e
    have he : (I.residual s.flow).potentialDifference (fun v => s.roundingUnit C * dy v) e =
        s.roundingUnit C * (s.roundedInstance C).potentialDifference dy e := by
      simp only [Circulation.potentialDifference]
      ring
    rw [he, ← mul_sub]
    constructor
    · intro ha
      exact mul_nonneg hunit.le ((hsign e).1 ha)
    · intro ha
      exact mul_nonpos_of_nonneg_of_nonpos hunit.le ((hsign e).2 ha)

end MinCostFlow.Scaling.CostState
