module

public import MinCostFlow.IPM.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The logarithmic Taylor bound

Lemma 4.6 (page 26) of Chen et al., arXiv:2203.00671v2, bounds `log(x+y)` for a
small relative step. As in its proof, divide by `x` and use the Taylor
series of `log(1+z)`. We keep two terms and bound the remainder.
-/

public section
namespace MinCostFlow.IPM

private theorem log_one_add_le (z : ℝ) (hz : |z| ≤ 1/10) :
    Real.log (1+z) ≤ z + z^2 := by
  have habs : |z| < 1 := lt_of_le_of_lt hz (by norm_num)
  have hd : 0 < 1 - |z| := sub_pos.mpr habs
  have h := Real.abs_log_sub_add_sum_range_le
    (x := -z) (by simpa only [abs_neg] using habs) 2
  norm_num [Finset.sum_range_succ, abs_neg] at h
  have hupper := (abs_le.mp h).2
  have hrem : |z| ^ 3 / (1 - |z|) ≤ (3/2) * z^2 := by
    apply (div_le_iff₀ hd).mpr
    have hzsq : z^2 = |z|^2 := (sq_abs z).symm
    rw [hzsq]
    have hsmall : |z| ≤ (3/2 : ℝ) * (1 - |z|) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsmall (sq_nonneg |z|)
    nlinarith only [hmul]
  have := hupper.trans hrem
  nlinarith only [this]

/-- Lemma 4.6 (page 26) (Taylor expansion for `log x`): a relative step of at most
one tenth has quadratic error at most `y²/x²`. -/
theorem lemma_4_6 (x y : ℝ) (hx : 0 < x) (hy : |y| ≤ x/10) :
    Real.log (x+y) ≤ Real.log x + y/x + y^2/x^2 := by
  have hratio : |y/x| ≤ 1/10 := by
    rw [abs_div, abs_of_pos hx]
    exact (div_le_iff₀ hx).mpr (by linarith only [hy])
  have hxy : 0 < x+y := by
    have hlo := (abs_le.mp hy).1
    linarith only [hx, hlo]
  have hlog : Real.log (1+y/x) = Real.log (x+y) - Real.log x := by
    rw [show 1+y/x = (x+y)/x by field_simp]
    exact Real.log_div hxy.ne' hx.ne'
  have h := log_one_add_le (y/x) hratio
  rw [hlog, div_pow] at h
  linarith only [h]

end MinCostFlow.IPM
