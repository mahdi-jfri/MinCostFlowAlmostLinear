module

public import MinCostFlow.IPM.Machine.PrecisionLazyStability
public import MinCostFlow.IPM.Machine.NormalizationProgram
import MinCostFlow.IPM.EpochTolerances
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Error budgets for computed epoch coefficients

The Detect threshold is rounded to the dyadic value `kappa*a/1024`.
Its eight-threshold stale-coordinate margin and the selected numerical
precision fit within the gradient tolerance for the source step parameter
`kappa*a/32`. Computed lengths retain a factor-two comparison after both
stale-coordinate and numerical approximation errors.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- The selected relative-error unit is at most `2^-20` times the
quality/exponent product whenever that product has the proved lower bound. -/
theorem selected_relative_error_le (m U : ℕ) (x : ℝ)
    (hx : 1/(2:ℝ)^(2*slackRangeExponent m U) ≤ x) :
    1/(2:ℝ)^(ipmErrorBits m U) ≤ x/1048576 := by
  have he : 2*slackRangeExponent m U+20 ≤ ipmErrorBits m U := by
    unfold ipmErrorBits ipmRangeExponent
    omega
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) he
  have hh := one_div_le_one_div_of_le
    (by positivity : (0:ℝ)<(2:ℝ)^(2*slackRangeExponent m U+20)) hp
  have hid : 1/(2:ℝ)^(2*slackRangeExponent m U+20) =
      (1/(2:ℝ)^(2*slackRangeExponent m U))/1048576 := by
    rw [pow_add]
    norm_num
    ring
  rw [hid] at hh
  exact hh.trans (div_le_div_of_nonneg_right hx (by norm_num))

/-- The stale and computed-gradient errors together fit the normalized
step's `q/16` tolerance with `q=kappa*a/32`. -/
theorem selected_gradient_tolerance_budget (m U : ℕ) (a x : ℝ)
    (ha : a ≤ 1/500) (hx : 1/(2:ℝ)^(2*slackRangeExponent m U) ≤ x) :
    8*a*(8*(x/1024))+4*(1/(2:ℝ)^(ipmErrorBits m U)) ≤ (x/32)/16 := by
  have hx0 : 0 ≤ x := (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^(2*slackRangeExponent m U)).trans hx
  have hh := mul_le_mul_of_nonneg_right ha hx0
  have hdelta := selected_relative_error_le m U x hx
  nlinarith only [hh,hdelta,hx0]

/-- Eight Detect thresholds stay within the stability lemma's `1/100`
range, and the computed coefficient error is also at most `1/100`. -/
theorem selected_epoch_error_bounds (m U : ℕ) (x : ℝ)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent m U) ≤ x) (hxhi : x ≤ 1) :
    0 ≤ 8*(x/1024) ∧ 8*(x/1024) ≤ 1/100 ∧
      0 ≤ 1/(2:ℝ)^(ipmErrorBits m U) ∧ 1/(2:ℝ)^(ipmErrorBits m U) ≤ 1/100 := by
  have hx0 : 0 ≤ x := (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^(2*slackRangeExponent m U)).trans hxlo
  have hd := selected_relative_error_le m U x hxlo
  have hd0 : 0 ≤ 1/(2:ℝ)^(ipmErrorBits m U) := by positivity
  exact ⟨by positivity,by linarith only [hxhi],hd0,by linarith only [hd,hxhi]⟩

/-- Composing numerical length error with stale-coordinate length error
still yields the factor-two bound required by the step theorem. -/
theorem computed_length_tolerance {n : ℕ} (eps delta : ℝ)
    (computed stored current : Fin n → ℝ)
    (he : 0 ≤ eps) (he' : eps ≤ 1/100) (hd : 0 ≤ delta) (hd' : delta ≤ 1/100)
    (hnum : VectorApprox (1+delta) computed stored)
    (hstale : VectorApprox (1+3*eps) stored current) :
    VectorApprox 2 computed current := by
  have hb : 0 < 1+delta := by linarith only [hd]
  have hc : 0 < 1+3*eps := by linarith only [he]
  have hprod : (1+delta)*(1+3*eps) ≤ 2 := by
    have hh := mul_le_mul (show 1+delta ≤ 101/100 by linarith only [hd'])
      (show 1+3*eps ≤ 103/100 by linarith only [he']) hc.le
      (by norm_num : (0:ℝ) ≤ 101/100)
    linarith only [hh]
  have hinv : (2:ℝ)⁻¹ ≤ ((1+delta)*(1+3*eps))⁻¹ :=
    (inv_le_inv₀ (by norm_num) (mul_pos hb hc)).mpr hprod
  intro e
  refine ⟨(hnum e).1,(hstale e).2.1,?_,?_⟩
  · have hfirst := mul_le_mul_of_nonneg_left (hstale e).2.2.1 (inv_nonneg.mpr hb.le)
    have hsecond := mul_le_mul_of_nonneg_right hinv (hstale e).2.1.le
    rw [mul_inv_rev] at hsecond
    nlinarith only [hfirst,hsecond,(hnum e).2.2.1]
  · have hh := mul_le_mul_of_nonneg_left (hstale e).2.2.2 hb.le
    have hp := mul_le_mul_of_nonneg_right hprod (hstale e).2.1.le
    nlinarith only [(hnum e).2.2.2,hh,hp]

/-- Composing numerical gradient error with Lemma 9.1's stale-gradient
error costs at most four numerical error units after residual rescaling.
The two factors come from the residual ratio and stored-length bound. -/
theorem computed_gradient_tolerance {n : ℕ} (delta tau scale : ℝ)
    (computed stored current storedLength currentLength : Fin n → ℝ)
    (hd : 0≤delta) (hscale : |scale|≤2)
    (hlength : VectorApprox 2 storedLength currentLength)
    (hnum : ∀ e,|computed e-stored e|≤delta*storedLength e)
    (hstale : GradientTolerance currentLength (fun e => scale*stored e) current tau) :
    GradientTolerance currentLength (fun e => scale*computed e) current (tau+4*delta) := by
  intro e
  have hs := (hlength e).2.2.2
  have hscaled : |scale*computed e-scale*stored e|≤4*delta*currentLength e := by
    calc
      |scale*computed e-scale*stored e|= |scale| * |computed e-stored e| := by rw [← mul_sub,abs_mul]
      _≤2*(delta*storedLength e) := mul_le_mul hscale (hnum e) (abs_nonneg _) (by norm_num)
      _≤4*delta*currentLength e := by
        have hh := mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0:ℝ)≤2) hd)
        nlinarith only [hh]
  have htriangle := abs_sub_le (scale*computed e) (scale*stored e) (current e)
  have hlpos := (hlength e).2.1
  have hstale' := hstale e
  dsimp only at hstale' ⊢
  rw [abs_div,abs_of_pos hlpos] at hstale' ⊢
  have hsbound := (div_le_iff₀ hlpos).mp hstale'
  apply (div_le_iff₀ hlpos).mpr
  nlinarith only [hscaled,htriangle,hsbound]

/-- With the selected dyadic threshold and numerical precision, stale
and computed coefficient errors meet the exact step tolerances together. -/
theorem selected_computed_epoch_tolerances {n : ℕ} (m U : ℕ) (a x scale : ℝ)
    (computedGradient storedGradient currentGradient computedLength storedLength currentLength : Fin n → ℝ)
    (ha : a≤1/500) (hxlo : 1/(2:ℝ)^(2*slackRangeExponent m U)≤x) (hxhi : x≤1)
    (hscale : |scale|≤2)
    (hnumLength : VectorApprox (1+1/(2:ℝ)^(ipmErrorBits m U)) computedLength storedLength)
    (hstaleLength : VectorApprox (1+3*(8*(x/1024))) storedLength currentLength)
    (hnumGradient : ∀ e,|computedGradient e-storedGradient e|≤
      (1/(2:ℝ)^(ipmErrorBits m U))*storedLength e)
    (hstaleGradient : GradientTolerance currentLength (fun e => scale*storedGradient e)
      currentGradient (8*a*(8*(x/1024)))) :
    VectorApprox 2 computedLength currentLength ∧
      GradientTolerance currentLength (fun e => scale*computedGradient e) currentGradient ((x/32)/16) := by
  obtain ⟨he,he',hd,hd'⟩ := selected_epoch_error_bounds m U x hxlo hxhi
  have hstored : VectorApprox 2 storedLength currentLength :=
    vectorApprox_mono (by linarith only [he]) (by linarith only [he']) hstaleLength
  refine ⟨computed_length_tolerance _ _ _ _ _ he he' hd hd' hnumLength hstaleLength,?_⟩
  have hg := computed_gradient_tolerance _ _ scale _ _ _ _ _ hd hscale hstored hnumGradient hstaleGradient
  have hbudget := selected_gradient_tolerance_budget m U a x ha hxlo
  intro e
  exact (hg e).trans hbudget

/-- The selected relative-error unit is at most `2^-20` times the
quality/exponent product whenever that product has the proved lower bound. -/
theorem widened_relative_error_le (m U k : ℕ) (x : ℝ)
    (hx : 1/(2:ℝ)^(2*qualitySlackExponent m U k) ≤ x) :
    1/(2:ℝ)^(ipmQualityErrorBits m U k) ≤ x/1048576 := by
  have he : 2*qualitySlackExponent m U k+20 ≤ ipmQualityErrorBits m U k := by
    unfold ipmQualityErrorBits ipmQualityRangeExponent
    omega
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) he
  have hh := one_div_le_one_div_of_le
    (by positivity : (0:ℝ)<(2:ℝ)^(2*qualitySlackExponent m U k+20)) hp
  have hid : 1/(2:ℝ)^(2*qualitySlackExponent m U k+20) =
      (1/(2:ℝ)^(2*qualitySlackExponent m U k))/1048576 := by
    rw [pow_add]
    norm_num
    ring
  rw [hid] at hh
  exact hh.trans (div_le_div_of_nonneg_right hx (by norm_num))

/-- The stale and computed-gradient errors together fit the normalized
step's `q/16` tolerance with `q=kappa*a/32`. -/
theorem widened_gradient_tolerance_budget (m U k : ℕ) (a x : ℝ)
    (ha : a ≤ 1/500) (hx : 1/(2:ℝ)^(2*qualitySlackExponent m U k) ≤ x) :
    8*a*(8*(x/1024))+4*(1/(2:ℝ)^(ipmQualityErrorBits m U k)) ≤ (x/32)/16 := by
  have hx0 : 0 ≤ x := (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^(2*qualitySlackExponent m U k)).trans hx
  have hh := mul_le_mul_of_nonneg_right ha hx0
  have hdelta := widened_relative_error_le m U k x hx
  nlinarith only [hh,hdelta,hx0]

/-- Eight Detect thresholds stay within the stability lemma's `1/100`
range, and the computed coefficient error is also at most `1/100`. -/
theorem widened_epoch_error_bounds (m U k : ℕ) (x : ℝ)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent m U k) ≤ x) (hxhi : x ≤ 1) :
    0 ≤ 8*(x/1024) ∧ 8*(x/1024) ≤ 1/100 ∧
      0 ≤ 1/(2:ℝ)^(ipmQualityErrorBits m U k) ∧ 1/(2:ℝ)^(ipmQualityErrorBits m U k) ≤ 1/100 := by
  have hx0 : 0 ≤ x := (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^(2*qualitySlackExponent m U k)).trans hxlo
  have hd := widened_relative_error_le m U k x hxlo
  have hd0 : 0 ≤ 1/(2:ℝ)^(ipmQualityErrorBits m U k) := by positivity
  exact ⟨by positivity,by linarith only [hxhi],hd0,by linarith only [hd,hxhi]⟩

/-- With the selected dyadic threshold and numerical precision, stale
and computed coefficient errors meet the exact step tolerances together. -/
theorem widened_computed_epoch_tolerances {n : ℕ} (m U k : ℕ) (a x scale : ℝ)
    (computedGradient storedGradient currentGradient computedLength storedLength currentLength : Fin n → ℝ)
    (ha : a≤1/500) (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent m U k)≤x) (hxhi : x≤1)
    (hscale : |scale|≤2)
    (hnumLength : VectorApprox (1+1/(2:ℝ)^(ipmQualityErrorBits m U k)) computedLength storedLength)
    (hstaleLength : VectorApprox (1+3*(8*(x/1024))) storedLength currentLength)
    (hnumGradient : ∀ e,|computedGradient e-storedGradient e|≤
      (1/(2:ℝ)^(ipmQualityErrorBits m U k))*storedLength e)
    (hstaleGradient : GradientTolerance currentLength (fun e => scale*storedGradient e)
      currentGradient (8*a*(8*(x/1024)))) :
    VectorApprox 2 computedLength currentLength ∧
      GradientTolerance currentLength (fun e => scale*computedGradient e) currentGradient ((x/32)/16) := by
  obtain ⟨he,he',hd,hd'⟩ := widened_epoch_error_bounds m U k x hxlo hxhi
  have hstored : VectorApprox 2 storedLength currentLength :=
    vectorApprox_mono (by linarith only [he]) (by linarith only [he']) hstaleLength
  refine ⟨computed_length_tolerance _ _ _ _ _ he he' hd hd' hnumLength hstaleLength,?_⟩
  have hg := computed_gradient_tolerance _ _ scale _ _ _ _ _ hd hscale hstored hnumGradient hstaleGradient
  have hbudget := widened_gradient_tolerance_budget m U k a x ha hxlo
  intro e
  exact (hg e).trans hbudget

end MinCostFlow.IPM.Machine
