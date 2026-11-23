module

public import MinCostFlow.IPM.Definitions
import MinCostFlow.IPM.Parameters
import MinCostFlow.IPM.WeightedBounds
import MinCostFlow.IPM.ResidualStability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounds on a normalized IPM step

The proof of Lemma 4.4 (page 25) of Chen et al., arXiv:2203.00671v2, first
normalizes the step so its approximate gradient dot product is `-κ²/50`.
Hölder's inequality bounds the true gradient error, and separating its
cost term bounds the residual change. The chosen exponent also bounds
the power of each slack by two.
-/

public section
namespace MinCostFlow.IPM

/-- The slack-power bound used in the proof of Lemma 4.4 (page 25). -/
theorem slack_rpow_alpha_le_two (I : Instance) (U x : ℝ)
    (hsize : 2 ≤ (I.m : ℝ)*U) (hx : 0 < x) (hbound : x ≤ 2*(I.m*U)) :
    Real.rpow x (alpha I U) ≤ 2 := by
  have hs : 0 < (I.m : ℝ)*U := lt_of_lt_of_le (by norm_num) hsize
  have ha := (alpha_pos I U hsize).le
  have hlog2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hlog2
  have hlogsize := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hsize
  have hlogx := Real.log_le_log hx hbound
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hs.ne'] at hlogx
  have hlog : Real.log x ≤ 2*Real.log (I.m*U) := by linarith only [hlogx, hlogsize]
  have hmul := mul_le_mul_of_nonneg_left hlog ha
  have hcancel := alpha_mul_log I U hsize
  rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hx, ← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  nlinarith only [hmul, hcancel, hlog2]

/-- A sharper slack-power bound, used to retain the factor `1+3ε` in
Lemma 4.9 (page 29) rather than lose a constant in the relative slack estimate. -/
theorem slack_rpow_alpha_le_five_fourths (I : Instance) (U x : ℝ)
    (hsize : 2 ≤ (I.m : ℝ)*U) (hx : 0 < x) (hbound : x ≤ 2*(I.m*U)) :
    Real.rpow x (alpha I U) ≤ 5/4 := by
  have hs : 0 < (I.m : ℝ)*U := lt_of_lt_of_le (by norm_num) hsize
  have ha := (alpha_pos I U hsize).le
  have hlogquarter := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 5/4)
  norm_num at hlogquarter
  have hlogsize := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hsize
  have hlogx := Real.log_le_log hx hbound
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hs.ne'] at hlogx
  have hlog : Real.log x ≤ 2*Real.log (I.m*U) := by linarith only [hlogx, hlogsize]
  have hmul := mul_le_mul_of_nonneg_left hlog ha
  have hcancel := alpha_mul_log I U hsize
  rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hx,
    ← Real.exp_log (by norm_num : (0 : ℝ) < 5/4)]
  apply Real.exp_le_exp.mpr
  nlinarith only [hmul, hcancel, hlogquarter]

/-- A normalized good direction has small true weighted length, a negative
true gradient dot product, and small relative cost change. These are the
first bounds in the proof of Lemma 4.4 (page 25). -/
theorem normalized_step_bounds (I : Instance) (a F κ : ℝ)
    (f gApprox lApprox s : Fin I.m → ℝ)
    (hm : 0 < I.m) (hf : StrictlyInside I f) (hr : 0 < residual I F f)
    (ha : 0 ≤ a) (ha' : a ≤ 1/500) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hg : GradientTolerance (lengths I a f) gApprox (gradient I a F f) (κ/8))
    (hl : VectorApprox 2 lApprox (lengths I a f))
    (hquality : κ * weightedLength lApprox s ≤ -dot gApprox s)
    (hscale : dot gApprox s = -κ^2/50) :
    weightedLength (lengths I a f) s ≤ κ/25 ∧
      dot (gradient I a F f) s ≤ -κ^2/100 ∧
      20*I.m*(|I.cost s| / residual I F f) ≤ κ/25 := by
  have hlen := weightedLength_le_two I a f lApprox s hf hl
  have hnorm : weightedLength (lengths I a f) s ≤ κ/25 := by
    rw [hscale] at hquality
    nlinarith only [hquality, hlen, hκ]
  have herr := abs_dot_error_le (lengths I a f) gApprox (gradient I a F f) s (κ/8)
    (lengths_pos I a f hf) hg
  have herr' : |dot gApprox s - dot (gradient I a F f) s| ≤ κ^2/200 := by
    have hmul := mul_le_mul_of_nonneg_left hnorm (div_nonneg hκ.le (by norm_num : (0 : ℝ) ≤ 8))
    exact herr.trans (by nlinarith only [hmul])
  have hgrad : dot (gradient I a F f) s ≤ -κ^2/100 := by
    have he := (abs_le.mp herr').1
    rw [hscale] at he
    nlinarith only [he, sq_nonneg κ]
  rw [hscale] at herr'
  have habsgrad : |dot (gradient I a F f) s| ≤ κ^2/40 := by
    have ht := abs_sub_le (dot (gradient I a F f) s) (dot gApprox s) 0
    rw [sub_zero, sub_zero, abs_sub_comm] at ht
    rw [hscale, abs_of_nonpos (by nlinarith only [sq_nonneg κ] : -κ^2/50 ≤ 0)] at ht
    linarith only [ht, herr']
  have hcost := abs_cost_term_le I a F f s hf ha
  have hm' : (0 : ℝ) < I.m := Nat.cast_pos.mpr hm
  rw [abs_mul, abs_of_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 20) hm')
    (inv_pos.mpr hr))] at hcost
  have hcost' : 20*I.m*(|I.cost s| / residual I F f) ≤
      κ^2/40 + a*(κ/25) := by
    have hn := mul_le_mul_of_nonneg_left hnorm ha
    rw [div_eq_mul_inv]
    nlinarith only [hcost, habsgrad, hn]
  have hksq : κ^2 ≤ κ := by nlinarith only [hκ', hκ]
  have haκ := mul_le_mul_of_nonneg_right ha' hκ.le
  refine ⟨hnorm, hgrad, ?_⟩
  nlinarith only [hcost', hksq, haκ, hκ]

end MinCostFlow.IPM
