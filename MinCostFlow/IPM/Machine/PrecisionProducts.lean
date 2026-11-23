module

public import MinCostFlow.IPM.Machine.PrecisionCallRanges
public import MinCostFlow.Num.IPM.FixedPointFacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Signed fits for cost products and prefix sums

The cost and residual procedures use exact integer products at the shared
fixed-point scale. Every partial sum is bounded by the sum of absolute
cost contributions over all edges. This derives their signed-fit premises
from feasible flow bounds, including guesses on either side of the optimum.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- The chosen signed width covers any numerator whose represented
value is inside the common range. -/
theorem fits_chosen_scaled_bound (m U : ℕ) {N : ℤ}
    (hN : |(N:ℝ)/(2:ℝ)^(ipmPrecision m U)| ≤ (2:ℝ)^(ipmRangeExponent m U)) :
    Num.Fits 4 (ipmLimbs m U) N := by
  apply Num.IPM.fits_of_scaled_bound (P:=ipmPrecision m U) (E:=ipmRangeExponent m U)
  · have hh := (ipm_precision_margins m U).2.2.2.2.1
    omega
  · exact hN

/-- A bounded integral cost, capacity or target fits both before and
after exact loading at the selected fixed-point precision. -/
theorem fits_integer_at_chosen_precision (m U : ℕ) (n : ℤ)
    (hn : |(n:ℝ)| ≤ (2:ℝ)^(ipmRangeExponent m U)) :
    Num.Fits 4 (ipmLimbs m U) n ∧
      Num.Fits 4 (ipmLimbs m U) (n*(2:ℤ)^(ipmPrecision m U)) := by
  constructor
  · apply Num.IPM.fits_of_scaled_bound (P:=0) (E:=ipmRangeExponent m U)
    · have hh := (ipm_precision_margins m U).2.2.2.2.1
      omega
    · simpa only [pow_zero,div_one] using hn
  · apply fits_chosen_scaled_bound
    simp only [Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
    rw [mul_div_cancel_right₀ _ (by positivity)]
    exact hn

/-- The chosen signed width covers any numerator whose represented
value is inside the common range. -/
theorem fits_quality_scaled_bound (m U k : ℕ) {N : ℤ}
    (hN : |(N:ℝ)/(2:ℝ)^(ipmQualityPrecision m U k)| ≤ (2:ℝ)^(ipmQualityRangeExponent m U k)) :
    Num.Fits 4 (ipmQualityLimbs m U k) N := by
  apply Num.IPM.fits_of_scaled_bound (P:=ipmQualityPrecision m U k) (E:=ipmQualityRangeExponent m U k)
  · have hh := (ipm_quality_precision_margins m U k).2.2.2.2.1
    omega
  · exact hN

/-- A bounded integral cost, capacity or target fits both before and
after exact loading at the selected fixed-point precision. -/
theorem fits_integer_at_quality_precision (m U k : ℕ) (n : ℤ)
    (hn : |(n:ℝ)| ≤ (2:ℝ)^(ipmQualityRangeExponent m U k)) :
    Num.Fits 4 (ipmQualityLimbs m U k) n ∧
      Num.Fits 4 (ipmQualityLimbs m U k) (n*(2:ℤ)^(ipmQualityPrecision m U k)) := by
  constructor
  · apply Num.IPM.fits_of_scaled_bound (P:=0) (E:=ipmQualityRangeExponent m U k)
    · have hh := (ipm_quality_precision_margins m U k).2.2.2.2.1
      omega
    · simpa only [pow_zero,div_one] using hn
  · apply fits_quality_scaled_bound
    simp only [Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
    rw [mul_div_cancel_right₀ _ (by positivity)]
    exact hn

/-- Every subset of feasible edge-cost contributions obeys the same
absolute bound as the whole dot product. This includes every scan prefix. -/
theorem feasible_cost_subset_abs_le (I : Instance) (U : ℝ) (f : Fin I.m → ℝ)
    (hU : 0 ≤ U) (hnums : NumbersBounded I U) (hf : I.IsFeasible f)
    (S : Finset (Fin I.m)) : |∑ e ∈ S,((I.edge e).cost:ℝ)*f e| ≤ I.m*U^2 := by
  have hcard : S.card ≤ I.m := by simpa using S.card_le_univ
  calc
    _ ≤ ∑ e ∈ S,|((I.edge e).cost:ℝ)*f e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ S,U^2 := by
      apply Finset.sum_le_sum
      intro e _
      rw [abs_mul,pow_two]
      exact mul_le_mul (hnums.2 e).2.2 (feasible_abs_le I U hnums f hf e) (abs_nonneg _) hU
    _ = (S.card:ℝ)*U^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg U)

/-- Each exact scaled cost prefix fits in the chosen signed blocks. -/
theorem cost_prefix_numerator_fits (I : Instance) (U : ℕ) (f : Fin I.m → ℝ)
    (z : Fin I.m → ℤ) (S : Finset (Fin I.m)) (hm : 0 < I.m) (hU : 0 < U)
    (hnums : NumbersBounded I U) (hf : I.IsFeasible f)
    (hz : ∀ e,f e=(z e:ℝ)/(2:ℝ)^(ipmPrecision I.m U)) :
    Num.Fits 4 (ipmLimbs I.m U) (∑ e ∈ S,(I.edge e).cost*z e) := by
  apply fits_chosen_scaled_bound
  have hsum : ((∑ e ∈ S,(I.edge e).cost*z e:ℤ):ℝ)/(2:ℝ)^(ipmPrecision I.m U) =
      ∑ e ∈ S,((I.edge e).cost:ℝ)*f e := by
    simp only [Int.cast_sum,Int.cast_mul,Finset.sum_div,hz,mul_div_assoc]
  rw [hsum]
  have hh := feasible_cost_subset_abs_le I U f (Nat.cast_nonneg _) hnums hf S
  have ht := twice_search_radius_le_dyadic I.m U hm hU
  have he : slackRangeExponent I.m U ≤ ipmRangeExponent I.m U := by
    unfold ipmRangeExponent
    omega
  have hsmall : |∑ e ∈ S,((I.edge e).cost:ℝ)*f e| ≤
      (2:ℝ)^(slackRangeExponent I.m U) := by
    have hnn : (0:ℝ) ≤ I.m*(U:ℝ)^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    linarith only [hh,ht,hnn]
  exact hsmall.trans (pow_le_pow_right₀ (by norm_num) he)

/-- Every exact cost prefix also fits the widened format. -/
theorem cost_prefix_numerator_fits_widened (I : Instance) (U k : ℕ) (f : Fin I.m → ℝ)
    (z : Fin I.m → ℤ) (S : Finset (Fin I.m)) (hm : 0 < I.m) (hU : 0 < U)
    (hnums : NumbersBounded I U) (hf : I.IsFeasible f)
    (hz : ∀ e,f e=(z e:ℝ)/(2:ℝ)^(ipmQualityPrecision I.m U k)) :
    Num.Fits 4 (ipmQualityLimbs I.m U k) (∑ e ∈ S,(I.edge e).cost*z e) := by
  apply fits_quality_scaled_bound
  have hsum : ((∑ e ∈ S,(I.edge e).cost*z e:ℤ):ℝ)/(2:ℝ)^(ipmQualityPrecision I.m U k) =
      ∑ e ∈ S,((I.edge e).cost:ℝ)*f e := by
    simp only [Int.cast_sum,Int.cast_mul,Finset.sum_div,hz,mul_div_assoc]
  rw [hsum]
  have hh := feasible_cost_subset_abs_le I U f (Nat.cast_nonneg _) hnums hf S
  have ht := twice_search_radius_le_dyadic I.m U hm hU
  have hSlack := slackRangeExponent_le_qualitySlackExponent I.m U k
  have he : slackRangeExponent I.m U ≤ ipmQualityRangeExponent I.m U k := by
    unfold ipmQualityRangeExponent
    omega
  have hsmall : |∑ e ∈ S,((I.edge e).cost:ℝ)*f e| ≤
      (2:ℝ)^(slackRangeExponent I.m U) := by
    have hnn : (0:ℝ) ≤ I.m*(U:ℝ)^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    linarith only [hh,ht,hnn]
  exact hsmall.trans (pow_le_pow_right₀ (by norm_num) he)

/-- Subtracting a target in the bounded search interval also fits.
The residual may be nonpositive because rejected targets must run safely. -/
theorem residual_numerator_fits (I : Instance) (U : ℕ) (f : Fin I.m → ℝ)
    (z : Fin I.m → ℤ) (F : ℤ) (hm : 0 < I.m) (hU : 0 < U)
    (hnums : NumbersBounded I U) (hf : I.IsFeasible f)
    (hz : ∀ e,f e=(z e:ℝ)/(2:ℝ)^(ipmPrecision I.m U))
    (hF : |(F:ℝ)| ≤ I.m*(U:ℝ)^2) :
    Num.Fits 4 (ipmLimbs I.m U)
      ((∑ e,(I.edge e).cost*z e)-F*(2:ℤ)^(ipmPrecision I.m U)) := by
  apply fits_chosen_scaled_bound
  have hsum : (((∑ e,(I.edge e).cost*z e)-F*(2:ℤ)^(ipmPrecision I.m U):ℤ):ℝ)/
      (2:ℝ)^(ipmPrecision I.m U) = I.cost f-(F:ℝ) := by
    simp only [Int.cast_sub,Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,
      sub_div,Finset.sum_div,hz,Instance.cost,mul_div_assoc]
    rw [div_self (by positivity : (2:ℝ)^(ipmPrecision I.m U) ≠ 0),mul_one]
  rw [hsum]
  have hc := feasible_cost_abs_le I U (Nat.cast_nonneg _) hnums f hf
  have ht : |I.cost f-(F:ℝ)| ≤ |I.cost f|+|(F:ℝ)| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (I.cost f) (-(F:ℝ))
  have hsmall := twice_search_radius_le_dyadic I.m U hm hU
  have he : slackRangeExponent I.m U ≤ ipmRangeExponent I.m U := by
    unfold ipmRangeExponent
    omega
  have hbound : |I.cost f-(F:ℝ)| ≤ (2:ℝ)^(slackRangeExponent I.m U) := by
    linarith only [hc,hF,ht,hsmall]
  exact hbound.trans (pow_le_pow_right₀ (by norm_num) he)

end MinCostFlow.IPM.Machine
