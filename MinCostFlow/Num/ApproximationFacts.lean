module

public import MinCostFlow.Num.DivisionSigns
import Mathlib.Tactic

/-!
# Fixed-point approximation bounds

The computational model on page 7 uses fixed-point arithmetic. Flooring a real
number at precision `P` loses less than one unit in the last place. This file
turns that bound into a relative reciprocal bound and proves that adding positive
approximations preserves their common relative error bound.
-/

public section
namespace MinCostFlow.Num

/-- Adding two approximations preserves a common relative error bound. In
particular this applies to the two positive terms in the IPM edge lengths. -/
theorem relative_error_add {x y u v ε : ℝ}
    (hu : |u-x| ≤ ε*x) (hv : |v-y| ≤ ε*y) :
    |(u+v)-(x+y)| ≤ ε*(x+y) := by
  calc
    |(u+v)-(x+y)| = |(u-x)+(v-y)| := by congr 1; ring
    _ ≤ |u-x|+|v-y| := abs_add_le _ _
    _ ≤ ε*x+ε*y := add_le_add hu hv
    _ = ε*(x+y) := by ring

/-- Rounding down at precision `P` loses at most one unit in the last place. -/
theorem floor_scaled_error (x : ℝ) (P : ℕ) :
    |(⌊x*(2:ℝ)^P⌋ : ℝ)/(2:ℝ)^P-x| ≤ 1/(2:ℝ)^P := by
  have hp : (0:ℝ)<(2:ℝ)^P := pow_pos (by norm_num) _
  have hlo := Int.floor_le (x*(2:ℝ)^P)
  have hhi := Int.lt_floor_add_one (x*(2:ℝ)^P)
  rw [abs_le]
  constructor
  · have hh : x*(2:ℝ)^P-1 ≤ (⌊x*(2:ℝ)^P⌋ : ℝ) := by linarith
    have hh' := div_le_div_of_nonneg_right hh (le_of_lt hp)
    rw [sub_div, mul_div_cancel_right₀ x (ne_of_gt hp)] at hh'
    linarith
  · have hh := (div_le_iff₀ hp).mpr hlo
    have hnonneg : (0:ℝ) ≤ 1/(2:ℝ)^P := le_of_lt (div_pos (by norm_num) hp)
    linarith

/-- If `P ≥ E+q`, flooring a reciprocal of an input at most `2^E`
meets relative error `2⁻q`. -/
theorem reciprocal_floor_relative {x : ℝ} {P E q : ℕ}
    (hx : 0<x) (hupper : x≤(2:ℝ)^E) (hP : E+q≤P) :
    |(⌊(1/x)*(2:ℝ)^P⌋ : ℝ)/(2:ℝ)^P-1/x| ≤
      (1/(2:ℝ)^q)/x := by
  have hpow : (2:ℝ)^(E+q)≤(2:ℝ)^P := pow_le_pow_right₀ (by norm_num) hP
  have hmul : (2:ℝ)^q*x≤(2:ℝ)^P := by
    calc
      (2:ℝ)^q*x ≤ (2:ℝ)^q*(2:ℝ)^E := mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = (2:ℝ)^(E+q) := by rw [pow_add]; ring
      _ ≤ (2:ℝ)^P := hpow
  calc
    _ ≤ 1/(2:ℝ)^P := floor_scaled_error (1/x) P
    _ ≤ (1/(2:ℝ)^q)/x := by
      rw [div_div]
      exact one_div_le_one_div_of_le (mul_pos (pow_pos (by norm_num) _) hx) hmul

end MinCostFlow.Num
