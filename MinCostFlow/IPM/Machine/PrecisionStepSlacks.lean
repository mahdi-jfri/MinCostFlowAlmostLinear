module

public import MinCostFlow.IPM.Machine.PrecisionResidual
import MinCostFlow.IPM.StepSlacks
import MinCostFlow.IPM.StepBounds
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith

/-!
# Relative slack bounds at a representable exponent

The proof of Chen et al., arXiv:2203.00671v2, Lemma 4.4 (page 25),
uses only an upper bound on the barrier exponent to bound a positive
slack power. The same argument therefore applies to `alphaPrime`,
without comparing lengths evaluated at two different exponents.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- The slack-power bound in Lemma 4.4 holds for every nonnegative
exponent at most the paper's analytic exponent. -/
theorem slack_rpow_at_exponent_le_two (I : Instance) (U a x : ℝ)
    (hsize : 2 ≤ (I.m:ℝ)*U) (ha : 0 ≤ a) (haUpper : a ≤ alpha I U)
    (hx : 0 < x) (hbound : x ≤ 2*(I.m*U)) : Real.rpow x a ≤ 2 := by
  by_cases hx1 : 1 ≤ x
  · exact (Real.rpow_le_rpow_of_exponent_le hx1 haUpper).trans
      (slack_rpow_alpha_le_two I U x hsize hx hbound)
  · have hh := Real.rpow_le_rpow_of_exponent_ge hx (le_of_not_ge hx1) ha
    simp only [Real.rpow_zero] at hh
    exact hh.trans (by norm_num)

/-- The upper and lower relative slack bounds in Lemma 4.4 (page 25),
with the barrier exponent explicitly supplied. -/
theorem step_slacks_at_exponent (I : Instance) (U a κ : ℝ) (f s : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (ha : 0 ≤ a) (haUpper : a ≤ alpha I U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f) (hκ : 0 ≤ κ)
    (hnorm : weightedLength (lengths I a f) s ≤ κ/25) (e : Fin I.m) :
    |s e| ≤ (κ/10)*((I.edge e).upper-f e) ∧
      |s e| ≤ (κ/10)*(f e-(I.edge e).lower) := by
  have hsingle : |lengths I a f e * s e| ≤
      weightedLength (lengths I a f) s :=
    Finset.single_le_sum (fun j _ => abs_nonneg (lengths I a f j * s j))
      (Finset.mem_univ e)
  rw [abs_mul, abs_of_pos (lengths_pos I a f hf e)] at hsingle
  have hp := (Real.rpow_pos_of_pos (sub_pos.mpr (hf e).2) (-1-a)).le
  have hq := (Real.rpow_pos_of_pos (sub_pos.mpr (hf e).1) (-1-a)).le
  have hlower := (abs_le.mp (hnums.2 e).1).1
  have hupper := (abs_le.mp (hnums.2 e).2.1).2
  have hm' : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
  have hsizeU : U ≤ I.m*U := by nlinarith only [hm', hU]
  have hpu : ((I.edge e).upper : ℝ)-f e ≤ 2*(I.m*U) := by
    linarith only [hlower, hupper, (hf e).1, hsizeU]
  have hpl : f e-((I.edge e).lower : ℝ) ≤ 2*(I.m*U) := by
    linarith only [hlower, hupper, (hf e).2, hsizeU]
  constructor
  · apply step_slack_le _ a _ κ (sub_pos.mpr (hf e).2) hκ
      (slack_rpow_at_exponent_le_two I U a _ hsize ha haUpper (sub_pos.mpr (hf e).2) hpu)
    dsimp only [lengths] at hsingle
    simp only [Real.rpow_eq_pow] at hsingle ⊢
    nlinarith only [hsingle, hnorm, mul_nonneg hq (abs_nonneg (s e))]
  · apply step_slack_le _ a _ κ (sub_pos.mpr (hf e).1) hκ
      (slack_rpow_at_exponent_le_two I U a _ hsize ha haUpper (sub_pos.mpr (hf e).1) hpl)
    dsimp only [lengths] at hsingle
    simp only [Real.rpow_eq_pow] at hsingle ⊢
    nlinarith only [hsingle, hnorm, mul_nonneg hp (abs_nonneg (s e))]

end MinCostFlow.IPM.Machine
