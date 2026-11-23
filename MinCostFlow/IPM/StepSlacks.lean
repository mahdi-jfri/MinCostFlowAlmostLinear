module

public import MinCostFlow.IPM.Definitions
import MinCostFlow.IPM.StepBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Capacity slack bounds for one IPM step

The proof of Lemma 4.4 (page 25) of Chen et al., arXiv:2203.00671v2, converts
the weighted length bound into a bound relative to each capacity slack.
The small power of a slack is at most two. Multiplying the weighted
coordinate bound by the inverse power gives the relative bound needed
for Taylor's theorem.
-/

public section
namespace MinCostFlow.IPM

private theorem inverse_slack_cancel (p a : ℝ) (hp : 0 < p) :
    Real.rpow p (-1-a) * (p * Real.rpow p a) = 1 := by
  simp only [Real.rpow_eq_pow]
  rw [← mul_assoc, ← Real.rpow_add_one hp.ne', show (-1-a)+1 = -a by ring,
    ← Real.rpow_add hp, neg_add_cancel, Real.rpow_zero]

/-- A single weighted coordinate bound implies a relative slack bound. -/
theorem step_slack_le (p a d κ : ℝ) (hp : 0 < p) (hκ : 0 ≤ κ)
    (hpower : Real.rpow p a ≤ 2) (hstep : Real.rpow p (-1-a) * |d| ≤ κ/25) :
    |d| ≤ (κ/10)*p := by
  have hmul := mul_le_mul_of_nonneg_right hstep
    (mul_nonneg hp.le (Real.rpow_pos_of_pos hp a).le)
  have hcancel := inverse_slack_cancel p a hp
  have hid : Real.rpow p (-1-a) * |d| * (p * Real.rpow p a) = |d| := by
    calc
      _ = |d| * (Real.rpow p (-1-a) * (p * Real.rpow p a)) := by ring
      _ = |d| := by rw [hcancel, mul_one]
  simp only [Real.rpow_eq_pow] at hid
  simp only [Real.rpow_eq_pow] at hmul
  rw [hid] at hmul
  have hcoef := mul_le_mul_of_nonneg_left hpower
    (mul_nonneg (div_nonneg hκ (by norm_num : (0 : ℝ) ≤ 25)) hp.le)
  simp only [Real.rpow_eq_pow] at hcoef
  nlinarith only [hmul, hcoef, mul_nonneg hκ hp.le]

/-- The upper and lower relative slack bounds in the proof of Lemma 4.4 (page 25). -/
theorem step_slacks (I : Instance) (U κ : ℝ) (f s : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f) (hκ : 0 ≤ κ)
    (hnorm : weightedLength (lengths I (alpha I U) f) s ≤ κ/25) (e : Fin I.m) :
    |s e| ≤ (κ/10)*((I.edge e).upper-f e) ∧
      |s e| ≤ (κ/10)*(f e-(I.edge e).lower) := by
  have hsingle : |lengths I (alpha I U) f e * s e| ≤
      weightedLength (lengths I (alpha I U) f) s :=
    Finset.single_le_sum (fun j _ => abs_nonneg (lengths I (alpha I U) f j * s j))
      (Finset.mem_univ e)
  rw [abs_mul, abs_of_pos (lengths_pos I (alpha I U) f hf e)] at hsingle
  have hp := (Real.rpow_pos_of_pos (sub_pos.mpr (hf e).2) (-1-alpha I U)).le
  have hq := (Real.rpow_pos_of_pos (sub_pos.mpr (hf e).1) (-1-alpha I U)).le
  have hlower := (abs_le.mp (hnums.2 e).1).1
  have hupper := (abs_le.mp (hnums.2 e).2.1).2
  have hm' : (1 : ℝ) ≤ I.m := Nat.one_le_cast.mpr hm
  have hsizeU : U ≤ I.m*U := by nlinarith only [hm', hU]
  have hpu : ((I.edge e).upper : ℝ)-f e ≤ 2*(I.m*U) := by
    linarith only [hlower, hupper, (hf e).1, hsizeU]
  have hpl : f e-((I.edge e).lower : ℝ) ≤ 2*(I.m*U) := by
    linarith only [hlower, hupper, (hf e).2, hsizeU]
  constructor
  · apply step_slack_le _ (alpha I U) _ κ (sub_pos.mpr (hf e).2) hκ
      (slack_rpow_alpha_le_two I U _ hsize (sub_pos.mpr (hf e).2) hpu)
    dsimp only [lengths] at hsingle
    simp only [Real.rpow_eq_pow] at hsingle ⊢
    nlinarith only [hsingle, hnorm, mul_nonneg hq (abs_nonneg (s e))]
  · apply step_slack_le _ (alpha I U) _ κ (sub_pos.mpr (hf e).1) hκ
      (slack_rpow_alpha_le_two I U _ hsize (sub_pos.mpr (hf e).1) hpl)
    dsimp only [lengths] at hsingle
    simp only [Real.rpow_eq_pow] at hsingle ⊢
    nlinarith only [hsingle, hnorm, mul_nonneg hp (abs_nonneg (s e))]

private theorem power_slack_mul (p a : ℝ) (hp : 0 < p) :
    Real.rpow p (-2-a) * p = Real.rpow p (-1-a) := by
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_add_one hp.ne', show (-2-a)+1 = -1-a by ring]

/-- The quadratic barrier term for one slack is bounded by the weighted
step length times its relative size. -/
theorem quadratic_slack_le (p a d τ : ℝ) (hp : 0 < p)
    (hd : |d| ≤ τ*p) :
    Real.rpow p (-2-a) * d^2 ≤ τ * Real.rpow p (-1-a) * |d| := by
  have hmul := mul_le_mul_of_nonneg_left hd
    (mul_nonneg (Real.rpow_pos_of_pos hp (-2-a)).le (abs_nonneg d))
  have hc := power_slack_mul p a hp
  have hid : Real.rpow p (-2-a)*|d| *(τ*p) = τ*(Real.rpow p (-2-a)*p)*|d| := by ring
  simp only [Real.rpow_eq_pow] at hid hc ⊢
  rw [hid, hc] at hmul
  simpa only [mul_assoc, ← pow_two, sq_abs] using hmul

end MinCostFlow.IPM
