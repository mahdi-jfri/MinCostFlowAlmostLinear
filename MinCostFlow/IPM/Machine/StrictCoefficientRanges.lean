module

public import MinCostFlow.IPM.Machine.ComputedCoefficientRanges
import Mathlib.Tactic.NormNum

/-!
# Admissible computed coefficients pass the strict machine guards

The potential supplies the smaller slack exponent. The length and
gradient error bounds put their computed values in ranges with explicit
exponents below the selected machine exponent. Thus even endpoint
values in those smaller ranges pass the strict coefficient checks.
The gradient may use the held epoch residual.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- Stored-residual coefficients satisfying the numerical tolerances
lie strictly inside the machine range, with room on both sides. -/
theorem computed_epoch_coefficients_strict_range (I : Instance) (U : ℕ)
    (a r z ell : ℝ) (stored : Fin I.m → ℝ) (ha : 0≤a) (ha' : a≤1)
    (hnums : NumbersBounded I U) (e : Fin I.m)
    (hu : 1/(2:ℝ)^(slackRangeExponent I.m U)≤(I.edge e).upper-stored e ∧
      (I.edge e).upper-stored e≤(2:ℝ)^(slackRangeExponent I.m U))
    (hd : 1/(2:ℝ)^(slackRangeExponent I.m U)≤stored e-(I.edge e).lower ∧
      stored e-(I.edge e).lower≤(2:ℝ)^(slackRangeExponent I.m U))
    (hr : 1/(2:ℝ)^(slackRangeExponent I.m U)≤r)
    (hell : ScalarApprox 2 ell (lengths I a stored e))
    (hz : |z-gradientWithResidual I a r stored e|≤lengths I a stored e) :
    |z|<(2:ℝ)^(ipmRangeExponent I.m U) ∧
      1/(2:ℝ)^(ipmRangeExponent I.m U)<ell ∧
      ell<(2:ℝ)^(ipmRangeExponent I.m U) := by
  have hcInt := gradient_instance_coefficient_bound I U hnums e
  have hc : |20*(I.m:ℝ)*(I.edge e).cost|≤
      (2:ℝ)^(gradientCoefficientExponent I.m U) := by exact_mod_cast hcInt
  have hr' : 1/(2:ℝ)^(slackRangeExponent I.m U)≤residual I (I.cost stored-r) stored := by
    simpa only [residual,sub_sub_cancel] using hr
  have hz' : |z-gradient I a (I.cost stored-r) stored e|≤lengths I a stored e := by
    rw [gradient_at_stored_residual]
    exact hz
  have hg := stored_gradient_dyadic_bound ha ha' e hu hd hr' hc hz'
  have hl := stored_length_dyadic_range ha ha' e hu hd hell
  have hgexp : gradientCoefficientExponent I.m U+2*slackRangeExponent I.m U+3<
      ipmRangeExponent I.m U := by unfold ipmRangeExponent; omega
  have hlexp : 2*slackRangeExponent I.m U+2< ipmRangeExponent I.m U := by
    unfold ipmRangeExponent; omega
  have hlowexp : 2*slackRangeExponent I.m U+1< ipmRangeExponent I.m U := by omega
  have hgPow := pow_lt_pow_right₀ (by norm_num : (1:ℝ)<2) hgexp
  have hlPow := pow_lt_pow_right₀ (by norm_num : (1:ℝ)<2) hlexp
  have hloPow := pow_lt_pow_right₀ (by norm_num : (1:ℝ)<2) hlowexp
  exact ⟨hg.trans_lt hgPow,
    (one_div_lt_one_div_of_lt (by positivity : (0:ℝ)<2^(2*slackRangeExponent I.m U+1)) hloPow).trans_le hl.1,
    hl.2.trans_lt hlPow⟩

end MinCostFlow.IPM.Machine
