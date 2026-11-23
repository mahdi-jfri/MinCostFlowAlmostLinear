module

public import MinCostFlow.IPM.Machine.MinRatioContract
public import MinCostFlow.IPM.Update
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Normalization rounding within Lemma 9.3's interval

Chen et al., arXiv:2203.00671v2, Lemma 9.3 (page 71), uses the
source step normalization with a stored residual. The machine contract
also rounds the normalization by a factor between one half and two.
Multiplying these two errors still puts the effective step parameter
in the same interval `[q/2,2q]` as the round-2 model. The square root
must be taken after multiplying the errors. No coordinatewise rounding
is justified by this argument.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine

/-- A rounded scalar normalization and a stored-residual ratio each
within `[1/2,2]` give an admissible step with effective parameter in
`[q/2,2q]`. This is the factor-four interval in the adapted Lemma 9.3,
not an additional factor-four loss on top of that interval. -/
theorem rounded_stored_step_update (I : Instance) (U F q s r : ℝ)
    (f g l d : Fin I.m → ℝ) (hq : 0 < q)
    (hslo : (1/2 : ℝ) ≤ s) (hshi : s ≤ 2)
    (hrlo : (1/2 : ℝ) ≤ r) (hrhi : r ≤ 2)
    (hg : GradientTolerance (lengths I (alpha I U) f)
      (fun e => s*g e) (gradient I (alpha I U) F f) (q/16))
    (hl : VectorApprox 2 l (lengths I (alpha I U) f))
    (hd : IsCirculation I d) (hqual : dot g d / weightedLength l d ≤ -4*q) :
    ∃ p : ℝ, q/2 ≤ p ∧ p ≤ 2*q ∧ ∃ u : IPM.Update I U F p f,
      u.gApprox = (fun e => s*g e) ∧ u.lApprox = l ∧ u.direction = d ∧
      u.stepSize = r*q^2/(50*|dot g d|) := by
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hslo
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hrlo
  have hsrlo : (1/4 : ℝ) ≤ s*r := by
    have hh := mul_le_mul hslo hrlo (by norm_num : (0 : ℝ) ≤ 1/2) hspos.le
    norm_num at hh
    exact hh
  have hsrhi : s*r ≤ 4 := by
    have hh := mul_le_mul hshi hrhi hrpos.le (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at hh
    exact hh
  have hsqrt0 := Real.sqrt_nonneg (s*r)
  have hsqrt := Real.sq_sqrt (mul_pos hspos hrpos).le
  have hlo : (1/2 : ℝ) ≤ Real.sqrt (s*r) := by nlinarith only [hsrlo, hsqrt0, hsqrt]
  have hhi : Real.sqrt (s*r) ≤ 2 := by nlinarith only [hsrhi, hsqrt0, hsqrt]
  let p := Real.sqrt (s*r)*q
  have hp : q/2 ≤ p := by
    have hh := mul_le_mul_of_nonneg_right hlo hq.le
    dsimp only [p]
    linarith only [hh]
  have hp' : p ≤ 2*q := mul_le_mul_of_nonneg_right hhi hq.le
  have hlen0 : 0 ≤ weightedLength l d := Finset.sum_nonneg fun e _ => abs_nonneg _
  have hlen : 0 < weightedLength l d := by
    by_contra hn
    have hz := le_antisymm (not_lt.mp hn) hlen0
    rw [hz, div_zero] at hqual
    linarith only [hq, hqual]
  have hneg : dot g d < 0 := by
    have hh := (div_le_iff₀ hlen).mp hqual
    exact lt_of_le_of_lt hh (mul_neg_of_neg_of_pos (by linarith only [hq]) hlen)
  have hdot : dot (fun e => s*g e) d = s*dot g d := by
    simp only [dot, Finset.mul_sum, mul_assoc]
  have hg' : GradientTolerance (lengths I (alpha I U) f)
      (fun e => s*g e) (gradient I (alpha I U) F f) (p/8) := by
    intro e
    exact (hg e).trans (by linarith only [hp])
  have hqual' : dot (fun e => s*g e) d / weightedLength l d ≤ -p := by
    rw [hdot, mul_div_assoc]
    have hh := mul_le_mul_of_nonneg_left hqual hspos.le
    have hs := mul_le_mul_of_nonneg_right hslo hq.le
    linarith only [hh, hp', hs]
  have hp2 : p^2 = s*r*q^2 := by dsimp only [p]; rw [mul_pow, hsqrt]
  have hnorm : r*q^2/(50*|dot g d|)*dot (fun e => s*g e) d = -p^2/50 := by
    rw [hdot, abs_of_neg hneg, hp2]
    field_simp [hneg.ne]
  exact ⟨p, hp, hp', ⟨(fun e => s*g e), l, d, r*q^2/(50*|dot g d|), hg', hl, hd,
    hqual', hnorm⟩, rfl, rfl, rfl, rfl⟩

/-- A positive requested normalization turns the machine contract's
absolute interval into the relative factor used above. -/
theorem NormalizationWithin.div_bounds {requested actual : ℝ}
    (hp : 0 < requested) (h : NormalizationWithin requested actual) :
    (1/2 : ℝ) ≤ actual/requested ∧ actual/requested ≤ 2 := by
  constructor
  · apply (le_div_iff₀ hp).mpr
    linarith only [h.1]
  · exact (div_le_iff₀ hp).mpr h.2

end MinCostFlow.IPM.Machine
