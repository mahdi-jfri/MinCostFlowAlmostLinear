module

public import MinCostFlow.IPM.Machine.MinRatioContract
public import MinCostFlow.Num.DivisionSigns
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rounding the multiplier used by Algorithm 2

Algorithm 2 (page 29) normalizes a successful circulation using its
gradient inner product. The IPM machine contract allows the actual
normalization to differ from the request by a factor of two. A floor
quotient on the flow grid gives a multiplier whose product with the
inner product is exact at twice the precision.
-/

public section

namespace MinCostFlow.MinRatio

open IPM.Machine

/-- A finite-precision multiplier rounded down to the flow grid yields a
factor-two normalization if the request spans at least two grid steps
of the directional inner product. -/
theorem pathFlow_floor_normalization {requested inner : ℝ} (hinner : inner < 0)
    (P : ℕ) (hstep : 2 * (-inner) ≤ requested * (2 : ℝ) ^ P) :
    let k : ℤ := ⌊requested * (2 : ℝ) ^ P / (-inner)⌋
    NormalizationWithin requested (-(((k : ℝ) / (2 : ℝ) ^ P) * inner)) := by
  dsimp only
  let scale : ℝ := (2 : ℝ) ^ P
  let x := requested * scale / (-inner)
  have hscale : 0 < scale := pow_pos (zero_lt_two : (0 : ℝ) < 2) _
  have hi : 0 < -inner := neg_pos.mpr hinner
  have hx : 2 ≤ x := (le_div_iff₀ hi).mpr hstep
  have hlo : x / 2 ≤ (⌊x⌋ : ℝ) := by
    have hf := Int.lt_floor_add_one x
    linarith only [hx, hf]
  have hhi : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have hdiv : x / scale * (-inner) = requested := by
    dsimp only [x]
    field_simp [hinner.ne, hscale.ne']
  have hlo' := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hlo hscale.le) hi.le
  have hhi' := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hhi hscale.le) hi.le
  have hr : 0 ≤ requested := by
    rw [← hdiv]
    exact mul_nonneg (div_nonneg (by linarith only [hx]) hscale.le) hi.le
  change NormalizationWithin requested (-(((⌊x⌋ : ℝ) / scale) * inner))
  rw [← mul_neg]
  constructor
  · calc
      requested / 2 = (x / 2) / scale * (-inner) := by rw [← hdiv]; ring
      _ ≤ _ := hlo'
  · rw [hdiv] at hhi'
    exact hhi'.trans (by linarith only [hr])

/-- Exponent bounds on the request and gradient sum imply the
two-grid-step condition for the quotient. -/
theorem pathFlow_precision_step {requested inner : ℝ} {E B P : ℕ}
    (hrequest : (2 : ℝ) ^ (-(E : ℤ)) ≤ requested)
    (hinner : -inner ≤ (2 : ℝ) ^ B) (hP : E + B + 1 ≤ P) :
    2 * (-inner) ≤ requested * (2 : ℝ) ^ P := by
  have hmul := mul_le_mul_of_nonneg_right hrequest
    (pow_nonneg (zero_le_two : (0 : ℝ) ≤ 2) P)
  have hexp :
      (2 : ℝ) ^ (B + 1) ≤ (2 : ℝ) ^ (-(E : ℤ)) * (2 : ℝ) ^ P := by
    rw [← zpow_natCast (2 : ℝ) P, ← zpow_natCast (2 : ℝ) (B + 1),
      ← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]
    apply zpow_le_zpow_right₀ (by norm_num)
    omega
  calc
    2 * (-inner) ≤ 2 * (2 : ℝ) ^ B := mul_le_mul_of_nonneg_left hinner zero_le_two
    _ = (2 : ℝ) ^ (B + 1) := (pow_succ' _ _).symm
    _ ≤ _ := hexp.trans hmul

/-- With dyadic gradient sum and request, the multiplier is the integer
floor division already computed by the fixed-point divider. -/
theorem pathFlow_floor_normalization_dyadic (P : ℕ) (request inner : ℤ) :
    ⌊((request : ℝ) / (2 : ℝ) ^ P) * (2 : ℝ) ^ P /
      (-((inner : ℝ) / (2 : ℝ) ^ P))⌋ =
      Num.floorDiv (request * (2 : ℤ) ^ P) (-inner) := by
  have hs : (2 : ℝ) ^ P ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [Num.floorDiv_eq_floor, div_mul_cancel₀ _ hs, ← neg_div,
    div_div_eq_mul_div, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_neg]

/-- The exact normalization uses the product of the two integer
numerators, interpreted at precision `2 * P`. -/
theorem pathFlow_actualNormalization_dyadic (P : ℕ) (multiplier inner : ℤ) :
    -(((multiplier : ℝ) / (2 : ℝ) ^ P) * ((inner : ℝ) / (2 : ℝ) ^ P)) =
      ((-(multiplier * inner) : ℤ) : ℝ) / (2 : ℝ) ^ (2 * P) := by
  rw [Int.cast_neg, Int.cast_mul, two_mul, pow_add, div_mul_div_comm, neg_div]

end MinCostFlow.MinRatio
