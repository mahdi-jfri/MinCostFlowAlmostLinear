module

public import MinCostFlow.IPM.Machine.PrecisionToleranceBudget
public import MinCostFlow.IPM.GuessBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Remaining min-ratio call ranges

The common range exponent covers the quality parameter supplied to the
data structure, the dyadic requested normalization and the maintained
flow increments. These follow from the chosen binary exponents and
feasibility, rather than from a range promise on the data structure's
answers. Detect's threshold is dyadic at the same precision.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- With hidden parameter `a/8`, the quality lower endpoint required
by the machine DS contract follows from the dyadic exponent bounds. -/
theorem chosen_minRatio_quality_range (m U k : ℕ) (hsize : 2 ≤ m*U)
    (hk : k ≤ slackRangeExponent m U) :
    1/(2:ℝ)^(ipmRangeExponent m U) ≤
      (1/(2:ℝ)^k)*(Num.IPM.alphaPrime m U/8) := by
  have hlo := dyadic_quality_product_lower m U k hsize hk
  have he : 2*slackRangeExponent m U+3 ≤ ipmRangeExponent m U := by
    unfold ipmRangeExponent
    omega
  have hp := one_div_le_one_div_of_le
    (by positivity : (0:ℝ)<(2:ℝ)^(2*slackRangeExponent m U+3))
    (pow_le_pow_right₀ (by norm_num) he)
  have hdiv : 1/(2:ℝ)^(2*slackRangeExponent m U+3) =
      (1/(2:ℝ)^(2*slackRangeExponent m U))/8 := by
    rw [pow_add]
    norm_num
    ring
  rw [hdiv] at hp
  have hh := hp.trans (div_le_div_of_nonneg_right hlo (by norm_num : (0:ℝ) ≤ 8))
  convert hh using 1; ring

/-- The exact requested normalization lies in the DS's common range. -/
theorem chosen_normalization_range (m U k : ℕ) (hsize : 2 ≤ m*U)
    (hk : k ≤ slackRangeExponent m U) :
    1/(2:ℝ)^(ipmRangeExponent m U) ≤
        1/(2:ℝ)^(dyadicNormalizationExponent k (Num.IPM.alphaExponent m U)) ∧
      1/(2:ℝ)^(dyadicNormalizationExponent k (Num.IPM.alphaExponent m U)) ≤
        (2:ℝ)^(ipmRangeExponent m U) := by
  have he := selected_normalization_exponent_le_range m U k hsize hk
  constructor
  · exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) he)
  · have hp1 : (1:ℝ) ≤ (2:ℝ)^(dyadicNormalizationExponent k (Num.IPM.alphaExponent m U)) :=
      one_le_pow₀ (by norm_num)
    exact ((div_le_one (by positivity)).mpr hp1).trans (one_le_pow₀ (by norm_num))

/-- Detect's threshold is an exactly representable dyadic when quality
and the barrier exponent are dyadic. -/
theorem dyadic_detect_threshold_eq (k j : ℕ) :
    (1/(2:ℝ)^k)*(1/(2:ℝ)^j)/1024 = 1/(2:ℝ)^(k+j+10) := by
  rw [pow_add,pow_add]
  norm_num
  field_simp

/-- The chosen precision also covers the Detect threshold's set bit. -/
theorem chosen_detect_exponent_le (m U k : ℕ) (hsize : 2 ≤ m*U)
    (hk : k ≤ slackRangeExponent m U) :
    k+Num.IPM.alphaExponent m U+10 ≤ ipmPrecision m U := by
  have hh := selected_normalization_exponent_le m U k hsize hk
  unfold dyadicNormalizationExponent at hh
  omega

/-- The cumulative increment from a feasible base to a feasible current
flow has magnitude at most `2U`, inside the selected DS range. -/
theorem feasible_increment_in_chosen_range (I : Instance) (U : ℕ)
    (base current : Fin I.m → ℝ) (hm : 0 < I.m) (hU : 0 < U)
    (hnums : NumbersBounded I U) (hb : I.IsFeasible base) (hc : I.IsFeasible current)
    (e : Fin I.m) :
    |current e-base e| ≤ (2:ℝ)^(ipmRangeExponent I.m U) := by
  have hbase := feasible_abs_le I U hnums base hb e
  have hcurrent := feasible_abs_le I U hnums current hc e
  have ht : |current e-base e| ≤ |current e|+|base e| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (current e) (-(base e))
  have htwo := twice_capacity_le_dyadic I.m U hm hU
  have he : slackRangeExponent I.m U ≤ ipmRangeExponent I.m U := by
    unfold ipmRangeExponent
    omega
  have hsmall : |current e-base e| ≤ (2:ℝ)^(slackRangeExponent I.m U) := by
    linarith only [ht,hbase,hcurrent,htwo]
  exact hsmall.trans (pow_le_pow_right₀ (by norm_num) he)

/-- With hidden parameter `a/8`, the quality lower endpoint required
by the machine DS contract follows from the dyadic exponent bounds. -/
theorem widened_minRatio_quality_range (m U k : ℕ) (hsize : 2 ≤ m*U) :
    1/(2:ℝ)^(ipmQualityRangeExponent m U k) ≤
      (1/(2:ℝ)^k)*(Num.IPM.alphaPrime m U/8) := by
  have hlo := widened_dyadic_quality_product_lower m U k hsize
  have he : 2*qualitySlackExponent m U k+3 ≤ ipmQualityRangeExponent m U k := by
    unfold ipmQualityRangeExponent
    omega
  have hp := one_div_le_one_div_of_le
    (by positivity : (0:ℝ)<(2:ℝ)^(2*qualitySlackExponent m U k+3))
    (pow_le_pow_right₀ (by norm_num) he)
  have hdiv : 1/(2:ℝ)^(2*qualitySlackExponent m U k+3) =
      (1/(2:ℝ)^(2*qualitySlackExponent m U k))/8 := by
    rw [pow_add]
    norm_num
    ring
  rw [hdiv] at hp
  have hh := hp.trans (div_le_div_of_nonneg_right hlo (by norm_num : (0:ℝ) ≤ 8))
  convert hh using 1; ring

/-- The exact requested normalization lies in the DS's common range. -/
theorem widened_normalization_range (m U k : ℕ) (hsize : 2 ≤ m*U) :
    1/(2:ℝ)^(ipmQualityRangeExponent m U k) ≤
        1/(2:ℝ)^(dyadicNormalizationExponent k (Num.IPM.alphaExponent m U)) ∧
      1/(2:ℝ)^(dyadicNormalizationExponent k (Num.IPM.alphaExponent m U)) ≤
        (2:ℝ)^(ipmQualityRangeExponent m U k) := by
  have he := quality_normalization_exponent_le_range m U k hsize
  constructor
  · exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) he)
  · have hp1 : (1:ℝ) ≤ (2:ℝ)^(dyadicNormalizationExponent k (Num.IPM.alphaExponent m U)) :=
      one_le_pow₀ (by norm_num)
    exact ((div_le_one (by positivity)).mpr hp1).trans (one_le_pow₀ (by norm_num))

/-- The chosen precision also covers the Detect threshold's set bit. -/
theorem widened_detect_exponent_le (m U k : ℕ) (hsize : 2 ≤ m*U) :
    k+Num.IPM.alphaExponent m U+10 ≤ ipmQualityPrecision m U k := by
  have hh := quality_normalization_exponent_le m U k hsize
  unfold dyadicNormalizationExponent at hh
  omega

end MinCostFlow.IPM.Machine
