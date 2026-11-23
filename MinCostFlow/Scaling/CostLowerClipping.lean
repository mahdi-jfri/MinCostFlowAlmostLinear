module

public import MinCostFlow.Scaling.CostStateInterpretation
public import MinCostFlow.Scaling.EpsilonExactness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The lower clipping bound in a cost round

Definition C.6 of Chen et al., arXiv:2203.00671v2, Appendix C, rounds an
epsilon-optimal residual cost. Since the unrounded cost exceeds minus
epsilon, its rounded integer value is at least minus the polynomial scaling
factor. Thus the model's lower clamp does not change active arcs. This
connects the bounded-cost implementation to the rounding used in Lemma C.7.
-/

@[expose] public section
namespace MinCostFlow.Scaling.CostState
variable {I : Circulation}

/-- Epsilon optimality makes the lower integer clamp redundant on active arcs. -/
theorem roundedCost_ge_neg_bound (C : ℕ) (s : CostState I)
    (hm : 0 < I.m) (hp : 0 < s.power)
    (hopt : I.EpsilonOptimalWith (fun e => (s.flow e : ℝ)) (s.epsilon C)
      (realPotential (I := I) C s))
    (e : Fin (I.m + I.m)) (he : 0 < (I.residual s.flow).capacity e) :
    -(((I.m + I.m) ^ 8 : ℕ) : ℤ) ≤ s.roundedCost C e := by
  have ha := I.epsilonOptimalWith_residual s.flow _ _ hopt e he
  have herr := (s.roundedCost_error C hm hp e).2
  have hu := s.roundingUnit_pos C hm hp
  have hmul := s.roundingUnit_mul C hm
  have hx : s.roundingUnit C * (-((((I.m + I.m) ^ 8 : ℕ) : ℝ)) - 1) <
      s.roundingUnit C * (s.roundedCost C e : ℝ) := by
    nlinarith only [ha, herr, hmul]
  have hq := (mul_lt_mul_iff_right₀ hu).mp hx
  have hi : -(((I.m + I.m) ^ 8 : ℕ) : ℤ) - 1 < s.roundedCost C e := by exact_mod_cast hq
  omega

/-- On active arcs only the high positive-cost clipping can change the cost. -/
theorem roundedInstance_cost_eq_min (C : ℕ) (s : CostState I)
    (hm : 0 < I.m) (hp : 0 < s.power)
    (hopt : I.EpsilonOptimalWith (fun e => (s.flow e : ℝ)) (s.epsilon C)
      (realPotential (I := I) C s))
    (e : Fin (I.m + I.m)) (he : 0 < (I.residual s.flow).capacity e) :
    (s.roundedInstance C).cost e =
      min (s.roundedCost C e) (((I.m + I.m) ^ 9 : ℕ) : ℤ) := by
  have hl := s.roundedCost_ge_neg_bound C hm hp hopt e he
  change max (-(((I.m + I.m) ^ 8 : ℕ) : ℤ)) _ = _
  apply max_eq_right
  apply le_min hl
  have hn : (0 : ℤ) ≤ (((I.m + I.m) ^ 9 : ℕ) : ℤ) := Int.natCast_nonneg _
  have hp' : (0 : ℤ) ≤ (((I.m + I.m) ^ 8 : ℕ) : ℤ) := Int.natCast_nonneg _
  omega

/-- The high clamp can only improve the lower rounding-error bound. -/
theorem roundedInstance_lower_error (C : ℕ) (s : CostState I)
    (hm : 0 < I.m) (hp : 0 < s.power)
    (hopt : I.EpsilonOptimalWith (fun e => (s.flow e : ℝ)) (s.epsilon C)
      (realPotential (I := I) C s))
    (e : Fin (I.m + I.m)) (he : 0 < (I.residual s.flow).capacity e) :
    -s.roundingUnit C < (I.residual s.flow).reducedCost (realPotential (I := I) C s) e -
      s.roundingUnit C * ((s.roundedInstance C).cost e : ℝ) := by
  have herr := (s.roundedCost_error C hm hp e).1
  have hle : ((s.roundedInstance C).cost e : ℝ) ≤ (s.roundedCost C e : ℝ) := by
    exact_mod_cast (show (s.roundedInstance C).cost e ≤ s.roundedCost C e by
      rw [s.roundedInstance_cost_eq_min C hm hp hopt e he]
      exact min_le_left _ _)
  have hh := mul_le_mul_of_nonneg_left hle (s.roundingUnit_pos C hm hp).le
  linarith only [herr, hh]

end MinCostFlow.Scaling.CostState
