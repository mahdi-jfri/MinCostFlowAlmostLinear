module

public import MinCostFlow.Scaling.CostLowerClipping
public import MinCostFlow.Scaling.ExpensiveArcs
import Mathlib.Tactic.NormNum

/-!
# High-cost clipping does not affect used arcs

The remark after Definition C.6 in Chen et al., arXiv:2203.00671v2,
Appendix C, ignores very expensive arcs. The model keeps their slots and
clips their costs. Since these clipped costs are still too large for any
nonpositive cycle, every integral optimum gives them zero flow. Thus the
upper rounding-error bound holds on every arc used in the augmentation,
which is exactly where the proof of Lemma C.7 needs it.
-/

@[expose] public section
namespace MinCostFlow.Scaling.CostState
variable {I : Circulation}

/-- Every optimum assigns zero to any arc whose rounded cost exceeds the high clamp. -/
theorem roundedInstance_zero_above_bound (C : ℕ) (s : CostState I)
    (hm : 0 < I.m) (hn : I.n ≤ I.m + I.m)
    (g : Fin (I.m + I.m) → ℤ)
    (hg : (s.roundedInstance C).Optimal (fun e => (g e : ℝ)))
    (e : Fin (I.m + I.m))
    (he : (((I.m + I.m) ^ 9 : ℕ) : ℤ) < s.roundedCost C e) : g e = 0 := by
  have hb : 0 < (I.m + I.m) ^ 8 := pow_pos (by omega) _
  have hp : I.n * (I.m + I.m) ^ 8 ≤ (I.m + I.m) ^ 9 := by
    have hh := Nat.mul_le_mul_right ((I.m + I.m) ^ 8) hn
    simpa only [pow_succ, Nat.mul_comm] using hh
  have hcost : (s.roundedInstance C).cost e = (((I.m + I.m) ^ 9 : ℕ) : ℤ) := by
    change max (-(((I.m + I.m) ^ 8 : ℕ) : ℤ))
      (min (s.roundedCost C e) (((I.m + I.m) ^ 9 : ℕ) : ℤ)) = _
    rw [min_eq_right he.le]
    apply max_eq_right
    have h8 := Int.natCast_nonneg ((I.m + I.m) ^ 8)
    have h9 := Int.natCast_nonneg ((I.m + I.m) ^ 9)
    omega
  apply (s.roundedInstance C).optimal_zero_on_expensive_arc g hg
    (((I.m + I.m) ^ 8 : ℕ) : ℤ) (Int.natCast_pos.mpr hb)
  · intro a
    change -(((I.m + I.m) ^ 8 : ℕ) : ℤ) ≤ max _ _
    exact le_max_left _ _
  · rw [hcost]
    change (I.n : ℤ) * (((I.m + I.m) ^ 8 : ℕ) : ℤ) ≤ (((I.m + I.m) ^ 9 : ℕ) : ℤ)
    exact_mod_cast hp

/-- On every active arc used by an optimum, neither clamp changes the rounded cost. -/
theorem roundedInstance_cost_eq_of_pos (C : ℕ) (s : CostState I)
    (hm : 0 < I.m) (hn : I.n ≤ I.m + I.m) (hp : 0 < s.power)
    (hopt : I.EpsilonOptimalWith (fun e => (s.flow e : ℝ)) (s.epsilon C)
      (realPotential (I := I) C s))
    (g : Fin (I.m + I.m) → ℤ)
    (hg : (s.roundedInstance C).Optimal (fun e => (g e : ℝ)))
    (e : Fin (I.m + I.m)) (hpos : 0 < g e) :
    (s.roundedInstance C).cost e = s.roundedCost C e := by
  have he : 0 < (I.residual s.flow).capacity e := by
    have hh := (hg.1.2 e).2
    have hpos' : 0 < (g e : ℝ) := Int.cast_pos.mpr hpos
    have hcap : (0 : ℝ) < (s.roundedInstance C).capacity e := lt_of_lt_of_le hpos' hh
    exact_mod_cast hcap
  rw [s.roundedInstance_cost_eq_min C hm hp hopt e he]
  apply min_eq_left
  by_contra h
  have hz := s.roundedInstance_zero_above_bound C hm hn g hg e (lt_of_not_ge h)
  omega

end MinCostFlow.Scaling.CostState
