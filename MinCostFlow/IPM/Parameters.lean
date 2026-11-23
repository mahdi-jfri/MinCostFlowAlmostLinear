module

public import MinCostFlow.IPM.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Bounds for the barrier exponent

Section 4 of Chen et al., arXiv:2203.00671v2, takes
`α = 1/(1000 log(mU))`. We make its nondegenerate range `mU ≥ 2`
explicit. This gives a positive exponent at most `1/500`.
-/

public section
namespace MinCostFlow.IPM

/-- The logarithm in the exponent's denominator is at least one half. -/
theorem log_size_ge_half (I : Instance) (U : ℝ) (hsize : 2 ≤ (I.m : ℝ)*U) :
    (1/2 : ℝ) ≤ Real.log (I.m*U) := by
  have ht := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at ht
  exact ht.trans (Real.log_le_log (by norm_num) hsize)

/-- The barrier exponent is positive when `mU ≥ 2`. -/
theorem alpha_pos (I : Instance) (U : ℝ) (hsize : 2 ≤ (I.m : ℝ)*U) :
    0 < alpha I U := by
  have hl := log_size_ge_half I U hsize
  unfold alpha
  apply one_div_pos.mpr
  linarith only [hl]

/-- The barrier exponent is at most `1/500` in the same range. -/
theorem alpha_le (I : Instance) (U : ℝ) (hsize : 2 ≤ (I.m : ℝ)*U) :
    alpha I U ≤ 1/500 := by
  have hl := log_size_ge_half I U hsize
  have hd : 0 < 1000 * Real.log (I.m*U) := by linarith only [hl]
  unfold alpha
  apply (div_le_iff₀ hd).mpr
  linarith only [hl]

/-- The cancellation used in the potential budget of Lemma 4.7 (page 28). -/
theorem alpha_mul_log (I : Instance) (U : ℝ) (hsize : 2 ≤ (I.m : ℝ)*U) :
    alpha I U * Real.log (I.m*U) = 1/1000 := by
  have hl := log_size_ge_half I U hsize
  have hn : Real.log (I.m*U) ≠ 0 := ne_of_gt (by linarith only [hl])
  unfold alpha
  field_simp

end MinCostFlow.IPM
