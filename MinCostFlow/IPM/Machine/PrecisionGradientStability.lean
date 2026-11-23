module

public import MinCostFlow.IPM.Machine.PrecisionLengthStability
public import MinCostFlow.IPM.GradientStability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Stored-gradient stability at the dyadic exponent

Chen et al., arXiv:2203.00671v2, Lemma 4.10 (page 30), cancels the cost
term after rescaling by the residual. The remaining power changes use
the length-stability proof at the same exponent. We retain the original
constants and make the nonnegative exponent `a≤alpha` explicit.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

private theorem residual_ratio_error (r R ε : ℝ) (hε : 0 ≤ ε) (hε' : ε ≤ 1/100)
    (hr : ScalarApprox (1+ε) r R) : |1-R/r| ≤ ε := by
  have hfac : 0 < 1+ε := by linarith only [hε]
  have hlo : R ≤ (1+ε)*r := (inv_mul_le_iff₀ hfac).mp hr.2.2.1
  have hhi := hr.2.2.2
  have hm := mul_le_mul_of_nonneg_left hhi (by linarith only [hε'] : 0 ≤ 1-ε)
  have hnonneg := mul_nonneg (sq_nonneg ε) hr.2.1.le
  have hdiff : |r-R| ≤ ε*r := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hlo, hm, hnonneg]
  rw [show 1-R/r = (r-R)/r by field_simp [hr.1.ne'], abs_div, abs_of_pos hr.1]
  exact (div_le_iff₀ hr.1).mpr hdiff

private theorem abs_barrier_difference (p q a : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (ha : 0 ≤ a) : |a*p-a*q| ≤ a*(p+q) := by
  apply abs_le.mpr
  constructor <;> nlinarith only [mul_nonneg ha hp, mul_nonneg ha hq]

private theorem barrier_gradient_change (a ε p q pbar qbar t : ℝ)
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (hε' : ε ≤ 1/100)
    (hp : 0 < p) (hq : 0 < q) (hpb : 0 < pbar) (hqb : 0 < qbar)
    (hres : |1-t| ≤ ε)
    (hup : |pbar-p| ≤ (5/2)*ε*p) (hlo : |qbar-q| ≤ (5/2)*ε*q)
    (hlen : pbar+qbar ≤ (1+3*ε)*(p+q)) :
    |(a*p-a*q) - t*(a*pbar-a*qbar)| ≤ 6*a*ε*(p+q) := by
  have hid : (a*p-a*q) - t*(a*pbar-a*qbar) =
      (1-t)*(a*pbar-a*qbar) + a*((p-pbar)-(q-qbar)) := by ring
  rw [hid]
  have ht := abs_add_le ((1-t)*(a*pbar-a*qbar)) (a*((p-pbar)-(q-qbar)))
  have hb := abs_barrier_difference pbar qbar a hpb.le hqb.le ha
  have hprod := mul_le_mul hres hb (abs_nonneg _) hε
  rw [← abs_mul] at hprod
  have hdiff := abs_sub_le (p-pbar) 0 (q-qbar)
  simp only [sub_zero, zero_sub, abs_neg] at hdiff
  have hd : |(p-pbar)-(q-qbar)| ≤ (5/2)*ε*(p+q) := by
    rw [abs_sub_comm] at hup hlo
    linarith only [hdiff, hup, hlo]
  have hdprod : |a*((p-pbar)-(q-qbar))| ≤ a*((5/2)*ε*(p+q)) := by
    rw [abs_mul, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left hd ha
  have hlenprod := mul_le_mul_of_nonneg_left hlen (mul_nonneg hε ha)
  have hsmall : ε^2 ≤ ε/100 := by nlinarith only [hε, hε']
  have hpay := mul_le_mul_of_nonneg_right hsmall (mul_nonneg ha (add_pos hp hq).le)
  nlinarith only [ht, hprod, hdprod, hlenprod, hpay, mul_nonneg (mul_nonneg ha hε) (add_pos hp hq).le]

/-- Small old weighted displacement keeps the new flow strictly inside
its capacity box, as required for Lemma 4.10 (page 30). -/
theorem stability_inside_at_exponent (I : Instance) (U a ε : ℝ) (f fbar : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (haNonneg : 0 ≤ a) (haUpper : a ≤ alpha I U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1/100)
    (hclose : ∀ e, |lengths I (a) f e*(fbar e-f e)| ≤ ε) :
    StrictlyInside I fbar := by
  intro e
  have hs := stability_slacks_at_exponent I U a ε f fbar hm hU hsize haNonneg haUpper hnums hf hε hclose e
  have hp := sub_pos.mpr (hf e).2
  have hq := sub_pos.mpr (hf e).1
  have hu := relative_slack_tenth _ _ ε hp hε' hs.1
  have hl := relative_slack_tenth _ _ ε hq hε' hs.2
  have hdu := abs_le.mp hu
  have hdl := abs_le.mp hl
  constructor <;> linarith only [hp, hq, hdu.1, hdu.2, hdl.1, hdl.2]

/-- Lemma 4.10 (page 30) (gradient stability) of Chen et al., arXiv:2203.00671v2.
The conclusion is the coordinate form of its weighted maximum norm bound.
We retain `ε ≤ 1/100`, needed by its invocation of Lemma 4.9 (page 29) but omitted
from the displayed statement in the source. -/
theorem lemma_4_10_at_exponent (I : Instance) (U a F ε r : ℝ) (f fbar : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (haNonneg : 0 ≤ a) (haUpper : a ≤ alpha I U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1/100)
    (hclose : ∀ e, |lengths I (a) f e*(fbar e-f e)| ≤ ε)
    (hres : ScalarApprox (1+ε) r (residual I F fbar)) :
    GradientTolerance (lengths I (a) f) (gradientWithResidual I (a) r f)
      (fun e => (residual I F fbar/r)*gradient I (a) F fbar e) (6*a*ε) := by
  have hfbar := stability_inside_at_exponent I U a ε f fbar hm hU hsize haNonneg haUpper hnums hf hε hε' hclose
  have hratio := residual_ratio_error r (residual I F fbar) ε hε hε' hres
  have hlength := lemma_4_9_at_exponent I U a ε f fbar hm hU hsize haNonneg haUpper hnums hf hε hε' hclose
  have ha := haNonneg
  intro e
  obtain ⟨hup, hlo⟩ := stability_power_changes_at_exponent I U a ε f fbar hm hU hsize haNonneg haUpper hnums hf hε hε' hclose e
  have hlen : lengths I (a) fbar e ≤ (1+3*ε)*lengths I (a) f e := by
    have ht := (hlength e).2.2.1
    exact (inv_mul_le_iff₀ (by linarith only [hε] : 0 < 1+3*ε)).mp ht
  have hbar := barrier_gradient_change (a) ε
    (Real.rpow ((I.edge e).upper-f e) (-1-a))
    (Real.rpow (f e-(I.edge e).lower) (-1-a))
    (Real.rpow ((I.edge e).upper-fbar e) (-1-a))
    (Real.rpow (fbar e-(I.edge e).lower) (-1-a))
    (residual I F fbar/r) ha hε hε'
    (Real.rpow_pos_of_pos (sub_pos.mpr (hf e).2) _)
    (Real.rpow_pos_of_pos (sub_pos.mpr (hf e).1) _)
    (Real.rpow_pos_of_pos (sub_pos.mpr (hfbar e).2) _)
    (Real.rpow_pos_of_pos (sub_pos.mpr (hfbar e).1) _)
    hratio hup hlo hlen
  have hid : gradientWithResidual I (a) r f e -
      (residual I F fbar/r)*gradient I (a) F fbar e =
      (a*Real.rpow ((I.edge e).upper-f e) (-1-a) -
        a*Real.rpow (f e-(I.edge e).lower) (-1-a)) -
      (residual I F fbar/r)*(a*Real.rpow ((I.edge e).upper-fbar e) (-1-a) -
        a*Real.rpow (fbar e-(I.edge e).lower) (-1-a)) := by
    unfold gradientWithResidual gradient
    field_simp [hres.1.ne', hres.2.1.ne']
    ring
  rw [hid, abs_div, abs_of_pos (lengths_pos I (a) f hf e)]
  apply (div_le_iff₀ (lengths_pos I (a) f hf e)).mpr
  exact hbar

end MinCostFlow.IPM.Machine
