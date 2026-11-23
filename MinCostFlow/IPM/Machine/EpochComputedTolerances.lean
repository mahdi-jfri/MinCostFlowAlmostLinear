module

public import MinCostFlow.IPM.Machine.EpochRefreshedCache
public import MinCostFlow.IPM.Machine.PrecisionToleranceBudget
import Mathlib.Tactic.Linarith
import MinCostFlow.IPM.Parameters
import MinCostFlow.IPM.Machine.PrecisionEta

/-!
# Lemma 9.1 at the coefficients of an actual epoch call

Decode the refreshed cache's numerical errors, then combine them with
Detect's stale-coordinate bound and the held residual's drift bound.
The same gradient and length blocks supplied to the next Update now
satisfy the dyadic step's tolerances.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Lemma 9.1 of Chen et al., arXiv:2203.00671v2 (page 70), applied to
the computed cache with the selected dyadic exponent and error budget. -/
theorem epoch_computed_tolerances (I : Instance) (U : ℕ) (target a x r : ℝ)
    (stored current computedGradient computedLength : Fin I.m → ℝ)
    (hm : 0<I.m) (hsize : 2≤(I.m:ℝ)*U) (hnums : NumbersBounded I U)
    (ha0 : 0≤a) (ha : a≤alpha I U)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤x) (hxhi : x≤1)
    (hinside : StrictlyInside I stored)
    (hclose : ∀ e,|lengths I a stored e*(current e-stored e)|≤8*(x/1024))
    (hresidual : ScalarApprox (1+8*(x/1024)) r (residual I target current))
    (hnumLength : VectorApprox (1+1/(2:ℝ)^(ipmErrorBits I.m U)) computedLength (lengths I a stored))
    (hnumGradient : ∀ e,|computedGradient e-gradientWithResidual I a r stored e|≤
      (1/(2:ℝ)^(ipmErrorBits I.m U))*lengths I a stored e) :
    let scale := r/residual I target current
    ((3/4:ℝ)≤scale ∧ scale≤4/3) ∧
    VectorApprox 2 computedLength (lengths I a current) ∧
    GradientTolerance (lengths I a current) (fun e => scale*computedGradient e)
      (gradient I a target current) ((x/32)/16) := by
  have haSmall := ha.trans (alpha_le I U hsize)
  obtain ⟨he,he',_,_⟩ := selected_epoch_error_bounds I.m U x hxlo hxhi
  have hs := residual_ratio_three_fourths he (by linarith only [he']) hresidual
  have habs : |r/residual I target current|≤2 := by
    rw [abs_of_nonneg (hs.1.trans' (by norm_num : (0:ℝ)≤3/4))]
    exact hs.2.trans (by norm_num)
  obtain ⟨hl,hg⟩ := lemma_9_1_at_exponent I U a target (8*(x/1024)) r stored current hm
    (Nat.cast_nonneg _) hsize ha0 ha hnums hinside he he' hclose hresidual
  exact ⟨hs,selected_computed_epoch_tolerances I.m U a x _ computedGradient _ _
    computedLength _ _ haSmall hxlo hxhi habs hnumLength hl hnumGradient hg⟩

/-- Lemma 9.1 of Chen et al., arXiv:2203.00671v2 (page 70), applied to
the computed cache with the selected dyadic exponent and error budget. -/
theorem epoch_widened_computed_tolerances (I : Instance) (U k : ℕ) (target a x r : ℝ)
    (stored current computedGradient computedLength : Fin I.m → ℝ)
    (hm : 0<I.m) (hsize : 2≤(I.m:ℝ)*U) (hnums : NumbersBounded I U)
    (ha0 : 0≤a) (ha : a≤alpha I U)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤x) (hxhi : x≤1)
    (hinside : StrictlyInside I stored)
    (hclose : ∀ e,|lengths I a stored e*(current e-stored e)|≤8*(x/1024))
    (hresidual : ScalarApprox (1+8*(x/1024)) r (residual I target current))
    (hnumLength : VectorApprox (1+1/(2:ℝ)^(ipmQualityErrorBits I.m U k)) computedLength (lengths I a stored))
    (hnumGradient : ∀ e,|computedGradient e-gradientWithResidual I a r stored e|≤
      (1/(2:ℝ)^(ipmQualityErrorBits I.m U k))*lengths I a stored e) :
    let scale := r/residual I target current
    ((3/4:ℝ)≤scale ∧ scale≤4/3) ∧
    VectorApprox 2 computedLength (lengths I a current) ∧
    GradientTolerance (lengths I a current) (fun e => scale*computedGradient e)
      (gradient I a target current) ((x/32)/16) := by
  have haSmall := ha.trans (alpha_le I U hsize)
  obtain ⟨he,he',_,_⟩ := widened_epoch_error_bounds I.m U k x hxlo hxhi
  have hs := residual_ratio_three_fourths he (by linarith only [he']) hresidual
  have habs : |r/residual I target current|≤2 := by
    rw [abs_of_nonneg (hs.1.trans' (by norm_num : (0:ℝ)≤3/4))]
    exact hs.2.trans (by norm_num)
  obtain ⟨hl,hg⟩ := lemma_9_1_at_exponent I U a target (8*(x/1024)) r stored current hm
    (Nat.cast_nonneg _) hsize ha0 ha hnums hinside he he' hclose hresidual
  exact ⟨hs,widened_computed_epoch_tolerances I.m U k a x _ computedGradient _ _
    computedLength _ _ haSmall hxlo hxhi habs hnumLength hl hnumGradient hg⟩

end MinCostFlow.IPM.Machine
