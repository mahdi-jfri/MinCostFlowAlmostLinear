module

public import MinCostFlow.LastLevelProgram.Rounding
import Mathlib.Tactic

/-!
# Integer arithmetic for the rounded weight update

For Lemma 5.5 (page 18), the model rounds the whole increment once.
The integer formula uses a product and one division, so it also
rounds only once.
-/

public section

namespace MinCostFlow.LastLevelProgram

/-- The fixed-point update with a positive integer denominator is an
integer multiply, divide, and add on the stored numerators. -/
theorem updateWeight_integer (P : ℕ) (a b d : ℤ) (hd : 0 < d) :
    updateWeight P (d : ℝ) ((a : ℝ) / (2 : ℝ)^P) ((b : ℝ) / (2 : ℝ)^P) =
      ((a + a * b / (d * (2 : ℤ)^P) : ℤ) : ℝ) / (2 : ℝ)^P := by
  have hargs :
      (a : ℝ) / (2 : ℝ)^P * (((b : ℝ) / (2 : ℝ)^P) / (d : ℝ)) * (2 : ℝ)^P =
        ((a * b : ℤ) : ℝ) / ((d * (2 : ℤ)^P : ℤ) : ℝ) := by
    push_cast
    field_simp
  have hden : 0 ≤ d * (2 : ℤ)^P := mul_nonneg hd.le (by positivity)
  rw [updateWeight, Num.dyadicFloor, hargs, Int.floor_div_cast_of_nonneg hden,
    Int.floor_intCast, Int.cast_add, add_div]

end MinCostFlow.LastLevelProgram
