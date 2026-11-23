module

public import MinCostFlow.IPM.Update
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Converting a stored-gradient update into an IPM step

Chen et al., arXiv:2203.00671v2, Algorithm 7 and Lemma 9.3
(Section 9, pages 69--72), rescale the stored gradient by the ratio of
the stored and true residuals. This also changes the effective step
normalization. Taking the square root of that ratio gives the correct
effective parameter. The result below proves its factor-four range
and a bound on the total weighted movement of the actual update.
-/

noncomputable section
public section
namespace MinCostFlow.IPM

private theorem ratio_dot_neg {m : ℕ} (g ℓ d : Fin m → ℝ) (q : ℝ)
    (hq : 0 < q) (hqual : dot g d / weightedLength ℓ d ≤ -4*q) :
    0 < weightedLength ℓ d ∧ dot g d < 0 := by
  have hlen0 : 0 ≤ weightedLength ℓ d := Finset.sum_nonneg fun e _ => abs_nonneg _
  have hlen : 0 < weightedLength ℓ d := by
    by_contra hn
    have hz := le_antisymm (not_lt.mp hn) hlen0
    rw [hz, div_zero] at hqual
    linarith only [hq, hqual]
  have hh := (div_le_iff₀ hlen).mp hqual
  exact ⟨hlen, lt_of_le_of_lt hh (mul_neg_of_neg_of_pos (by linarith only [hq]) hlen)⟩

private theorem dot_scale {m : ℕ} (s : ℝ) (g d : Fin m → ℝ) :
    dot (fun e => s*g e) d = s*dot g d := by
  simp only [dot, Finset.mul_sum, mul_assoc]

/-- A stored-gradient step is a permitted IPM update, with an effective
parameter in `[q/2,2q]`. This explicitly accounts for the residual
rescaling in Chen et al., Lemma 9.3 (page 71). -/
theorem stored_step_update (I : Instance) (U F q s : ℝ)
    (f g ℓ d : Fin I.m → ℝ) (hq : 0 < q) (hslo : (1/2 : ℝ) ≤ s) (hshi : s ≤ 2)
    (hg : GradientTolerance (lengths I (alpha I U) f)
      (fun e => s*g e) (gradient I (alpha I U) F f) (q/16))
    (hl : VectorApprox 2 ℓ (lengths I (alpha I U) f))
    (hd : IsCirculation I d) (hqual : dot g d / weightedLength ℓ d ≤ -4*q) :
    ∃ p : ℝ, q/2 ≤ p ∧ p ≤ 2*q ∧ ∃ u : Update I U F p f,
      u.gApprox = (fun e => s*g e) ∧ u.lApprox = ℓ ∧ u.direction = d ∧
      u.stepSize = q^2/(50*|dot g d|) := by
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hslo
  have hsqrt0 := Real.sqrt_nonneg s
  have hsqrt := Real.sq_sqrt hspos.le
  have hsqrtlo : (1/2 : ℝ) ≤ Real.sqrt s := by nlinarith only [hslo, hsqrt0, hsqrt]
  have hsqrthi : Real.sqrt s ≤ 2 := by nlinarith only [hshi, hsqrt0, hsqrt]
  let p := Real.sqrt s*q
  have hp : q/2 ≤ p := by
    have hh := mul_le_mul_of_nonneg_right hsqrtlo hq.le
    dsimp only [p]
    linarith only [hh]
  have hp' : p ≤ 2*q := mul_le_mul_of_nonneg_right hsqrthi hq.le
  obtain ⟨hlen, hneg⟩ := ratio_dot_neg g ℓ d q hq hqual
  have hg' : GradientTolerance (lengths I (alpha I U) f)
      (fun e => s*g e) (gradient I (alpha I U) F f) (p/8) := by
    intro e
    exact (hg e).trans (by linarith only [hp])
  have hqual' : dot (fun e => s*g e) d / weightedLength ℓ d ≤ -p := by
    rw [dot_scale, mul_div_assoc]
    have hh := mul_le_mul_of_nonneg_left hqual hspos.le
    have hsq : 2*q ≤ 4*s*q := by
      have hmul := mul_le_mul_of_nonneg_right hslo hq.le
      linarith only [hmul]
    linarith only [hh, hp', hsq]
  have hnorm : q^2/(50*|dot g d|)*dot (fun e => s*g e) d = -p^2/50 := by
    rw [dot_scale, abs_of_neg hneg]
    have hp2 : p^2 = s*q^2 := by dsimp only [p]; rw [mul_pow, hsqrt]
    rw [hp2]
    field_simp [hneg.ne]
  exact ⟨p, hp, hp', ⟨(fun e => s*g e), ℓ, d, q^2/(50*|dot g d|), hg', hl, hd,
    hqual', hnorm⟩, rfl, rfl, rfl, rfl⟩

/-- The scaled circulation in Algorithm 7 has weighted movement at most
`q/200` when its unscaled stored-gradient ratio is at most `-4q`.
This sharper bound cancels the dependence on the Detect threshold in
Lemma 9.4's charging argument. -/
theorem stored_step_movement {m : ℕ} (q : ℝ) (g ℓ d : Fin m → ℝ)
    (hq : 0 < q) (hqual : dot g d / weightedLength ℓ d ≤ -4*q) :
    weightedLength ℓ (fun e => (q^2/(50*|dot g d|))*d e) ≤ q/200 := by
  obtain ⟨hlen, hneg⟩ := ratio_dot_neg g ℓ d q hq hqual
  have hratio := (div_le_iff₀ hlen).mp hqual
  have habs : 0 < |dot g d| := abs_pos.mpr hneg.ne
  have hstep : 0 ≤ q^2/(50*|dot g d|) := div_nonneg (sq_nonneg q)
    (mul_nonneg (by norm_num) habs.le)
  have heq : weightedLength ℓ (fun e => (q^2/(50*|dot g d|))*d e) =
      (q^2/(50*|dot g d|))*weightedLength ℓ d := by
    unfold weightedLength
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [show ℓ e*((q^2/(50*|dot g d|))*d e) =
      (q^2/(50*|dot g d|))*(ℓ e*d e) by ring, abs_mul, abs_of_nonneg hstep]
  rw [heq]
  apply (mul_le_mul_iff_right₀ (mul_pos (by norm_num : (0 : ℝ) < 50) habs)).mp
  have hcancel : (50*|dot g d|)*((q^2/(50*|dot g d|))*weightedLength ℓ d) =
      q^2*weightedLength ℓ d := by field_simp
  rw [hcancel, abs_of_neg hneg]
  nlinarith only [hratio, hq]

end MinCostFlow.IPM
