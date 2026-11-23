module

public import MinCostFlow.IPM.LazyAlgorithm
public import MinCostFlow.IPM.LazyStability
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Explicit approximation tolerances for an epoch

Algorithm 7 and Lemma 9.1 of Chen et al., arXiv:2203.00671v2
(Section 9, page 70), rescale the stored gradient by the stored
residual divided by the true residual. With Detect threshold `κ α/1000`,
coordinate error and residual drift bounded by eight thresholds give
the tolerances used by `StoredStep`. The small barrier exponent makes
the resulting gradient error fit within the step budget.
-/

public section
namespace MinCostFlow.IPM

/-- Widening a positive approximation factor preserves a vector
approximation. -/
theorem vectorApprox_mono {n : ℕ} {b c : ℝ} {x y : Fin n → ℝ}
    (hb : 0 < b) (hbc : b ≤ c) (h : VectorApprox b x y) : VectorApprox c x y := by
  have hc : 0 < c := hb.trans_le hbc
  intro e
  refine ⟨(h e).1, (h e).2.1, ?_, ?_⟩
  · have hinv : c⁻¹ ≤ b⁻¹ := (inv_le_inv₀ hc hb).mpr hbc
    exact (mul_le_mul_of_nonneg_right hinv (h e).2.1.le).trans (h e).2.2.1
  · exact (h e).2.2.2.trans (mul_le_mul_of_nonneg_right hbc (h e).2.1.le)

/-- The epoch's eight-threshold tolerance is at most `1/100`, and the
rescaled gradient error fits in the budget for `q = κ α/32`. -/
theorem epoch_tolerance_bounds (I : Instance) (U κ : ℝ)
    (hsize : 2 ≤ (I.m : ℝ)*U) (hk : 0 < κ) (hk' : κ ≤ 1) :
    0 < ipmDetectThreshold I U κ ∧ 8*ipmDetectThreshold I U κ ≤ 1/100 ∧
      64*alpha I U*ipmDetectThreshold I U κ ≤ (κ*alpha I U/32)/16 := by
  have ha := alpha_pos I U hsize
  have ha' := alpha_le I U hsize
  have hka : 0 < κ*alpha I U := mul_pos hk ha
  have hupper := mul_le_mul_of_nonneg_right hk' ha.le
  have hn : 64*alpha I U/1000 ≤ (1/512 : ℝ) := by linarith only [ha']
  have hmul := mul_le_mul_of_nonneg_right hn hka.le
  unfold ipmDetectThreshold
  refine ⟨div_pos hka (by norm_num), ?_, ?_⟩
  · linarith only [hupper, ha']
  · nlinarith only [hmul]

/-- Combining the proved stale-coordinate bound and residual drift gives
the actual length and rescaled-gradient tolerances for an IPM step. -/
theorem epoch_stability_tolerances (I : Instance) (U F κ r : ℝ)
    (stored current : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hs : StrictlyInside I stored)
    (hk : 0 < κ) (hk' : κ ≤ 1)
    (hclose : ∀ e, |lengths I (alpha I U) stored e*(current e-stored e)| ≤
      8*ipmDetectThreshold I U κ)
    (hr : ScalarApprox (1+8*ipmDetectThreshold I U κ) r (residual I F current)) :
    VectorApprox 2 (lengths I (alpha I U) stored) (lengths I (alpha I U) current) ∧
      GradientTolerance (lengths I (alpha I U) current)
        (fun e => (r/residual I F current)*gradientWithResidual I (alpha I U) r stored e)
        (gradient I (alpha I U) F current) ((κ*alpha I U/32)/16) := by
  have he := epoch_tolerance_bounds I U κ hsize hk hk'
  have hd0 : 0 ≤ 8*ipmDetectThreshold I U κ := mul_nonneg (by norm_num) he.1.le
  have hh := lemma_9_1 I U F (8*ipmDetectThreshold I U κ) r stored current
    hm hU hsize hnums hs hd0 he.2.1 hclose hr
  refine ⟨vectorApprox_mono (by linarith only [hd0])
    (by linarith only [he.2.1]) hh.1, ?_⟩
  intro e
  have heq : 8*alpha I U*(8*ipmDetectThreshold I U κ) =
      64*alpha I U*ipmDetectThreshold I U κ := by ring
  exact (hh.2 e).trans (by rw [heq]; exact he.2.2)

/-- The stored-to-true residual ratio is between one half and two under
the epoch approximation. These are the exact inputs to `stored_step_update`. -/
theorem epoch_residual_scale_bounds (I : Instance) (U F κ r : ℝ) (f : Fin I.m → ℝ)
    (hsize : 2 ≤ (I.m : ℝ)*U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hr : ScalarApprox (1+8*ipmDetectThreshold I U κ) r (residual I F f)) :
    (1/2 : ℝ) ≤ r/residual I F f ∧ r/residual I F f ≤ 2 := by
  have he := epoch_tolerance_bounds I U κ hsize hk hk'
  have hb : 0 < 1+8*ipmDetectThreshold I U κ := by linarith only [he.1]
  have hlo := (inv_mul_le_iff₀ hb).mp hr.2.2.1
  have hhi := hr.2.2.2
  have hbr := mul_le_mul_of_nonneg_right he.2.1 hr.1.le
  have hbR := mul_le_mul_of_nonneg_right he.2.1 hr.2.1.le
  constructor
  · apply (le_div_iff₀ hr.2.1).mpr
    linarith only [hlo, hbr, hr.1.le]
  · apply (div_le_iff₀ hr.2.1).mpr
    linarith only [hhi, hbR, hr.2.1.le]

end MinCostFlow.IPM
