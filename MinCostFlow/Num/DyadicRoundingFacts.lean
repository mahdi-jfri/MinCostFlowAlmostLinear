module

public import MinCostFlow.Num.ApproximationFacts
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Rounding real values to fixed-point precision

The real-valued rounding function below describes the integer floor used by
fixed-point arithmetic. Its error is at most one last-place unit. On
nonnegative inputs it stays between zero and the input.
-/

@[expose] public section
namespace MinCostFlow.Num

/-- Round down to a multiple of `2⁻ᴾ`. -/
noncomputable def dyadicFloor (P : ℕ) (x : ℝ) : ℝ :=
  (⌊x*(2:ℝ)^P⌋ : ℝ)/(2:ℝ)^P

/-- One rounding loses at most one last-place unit. -/
theorem dyadicFloor_error (P : ℕ) (x : ℝ) :
    |dyadicFloor P x-x|≤1/(2:ℝ)^P := floor_scaled_error x P

/-- Rounding down never increases the input. -/
theorem dyadicFloor_le (P : ℕ) (x : ℝ) : dyadicFloor P x≤x := by
  apply (div_le_iff₀ (show (0:ℝ)<(2:ℝ)^P by positivity)).mpr
  exact Int.floor_le _

/-- Rounding a nonnegative value stays nonnegative. -/
theorem dyadicFloor_nonneg {P : ℕ} {x : ℝ} (hx : 0≤x) : 0≤dyadicFloor P x := by
  have hh : (0:ℤ)≤⌊x*(2:ℝ)^P⌋ := Int.floor_nonneg.mpr (by positivity)
  exact div_nonneg (by exact_mod_cast hh) (by positivity)

/-- Rounding the product of two stored integer numerators agrees with integer
floor division by the scale. -/
theorem dyadicFloor_product (A B : ℤ) (P : ℕ) :
    dyadicFloor P ((A:ℝ)/(2:ℝ)^P*((B:ℝ)/(2:ℝ)^P))=
      ((A*B/(2:ℤ)^P:ℤ):ℝ)/(2:ℝ)^P := by
  unfold dyadicFloor
  have he : (A:ℝ)/(2:ℝ)^P*((B:ℝ)/(2:ℝ)^P)*(2:ℝ)^P=
      ((A*B:ℤ):ℝ)/((2:ℤ)^P:ℤ) := by
    push_cast
    field_simp
  rw [he,Int.floor_div_cast_of_nonneg (show (0:ℤ)≤(2:ℤ)^P by positivity),Int.floor_intCast]

/-- Rounding the reciprocal of an integer uses ordinary integer division of
the scale. -/
theorem dyadicFloor_coefficient (d P : ℕ) :
    dyadicFloor P (1/(d:ℝ))=(((2:ℤ)^P/(d:ℤ):ℤ):ℝ)/(2:ℝ)^P := by
  unfold dyadicFloor
  rw [show 1/(d:ℝ)*(2:ℝ)^P=((2:ℤ)^P:ℤ)/(d:ℤ) by push_cast; ring,
    Int.floor_div_cast_of_nonneg (Int.natCast_nonneg d),Int.floor_intCast]

/-- Fixed-point division agrees with rounding the real quotient. -/
theorem dyadicFloor_division (A B : ℤ) (P : ℕ) (hB : 0≤B) :
    dyadicFloor P (((A:ℝ)/(2:ℝ)^P)/((B:ℝ)/(2:ℝ)^P))=
      ((A*(2:ℤ)^P/B:ℤ):ℝ)/(2:ℝ)^P := by
  unfold dyadicFloor
  have he : ((A:ℝ)/(2:ℝ)^P)/((B:ℝ)/(2:ℝ)^P)*(2:ℝ)^P=
      ((A*(2:ℤ)^P:ℤ):ℝ)/(B:ℝ) := by
    push_cast
    field_simp
  rw [he,Int.floor_div_cast_of_nonneg hB,Int.floor_intCast]

/-- Dividing a stored numerator by an unscaled natural denominator gives
one further rounded fixed-point division. -/
theorem dyadicFloor_div_nat (A : ℤ) (d P : ℕ) :
    dyadicFloor P (((A:ℝ)/(2:ℝ)^P)/(d:ℝ))=
      ((A/(d:ℤ):ℤ):ℝ)/(2:ℝ)^P := by
  unfold dyadicFloor
  have he : ((A:ℝ)/(2:ℝ)^P)/(d:ℝ)*(2:ℝ)^P=(A:ℝ)/(d:ℝ) := by field_simp
  rw [he]
  change (⌊(A:ℝ)/((d:ℤ):ℝ)⌋:ℝ)/(2:ℝ)^P=_
  rw [Int.floor_div_cast_of_nonneg (Int.natCast_nonneg d),Int.floor_intCast]

/-- Dyadic flooring preserves order. -/
theorem dyadicFloor_mono (P : ℕ) {x y : ℝ} (hxy : x≤y) :
    dyadicFloor P x≤dyadicFloor P y := by
  have hp : (0:ℝ)≤(2:ℝ)^P := by positivity
  exact div_le_div_of_nonneg_right
    (Int.cast_le.mpr (Int.floor_mono (mul_le_mul_of_nonneg_right hxy hp))) hp

/-- One is represented exactly at every precision. -/
theorem dyadicFloor_one (P : ℕ) : dyadicFloor P 1=1 := by
  unfold dyadicFloor
  rw [one_mul]
  have hf : ⌊(2:ℝ)^P⌋=(2:ℤ)^P := by norm_cast; exact Int.floor_natCast _
  rw [hf]
  push_cast
  exact div_self (ne_of_gt (pow_pos (by norm_num) _))

end MinCostFlow.Num
